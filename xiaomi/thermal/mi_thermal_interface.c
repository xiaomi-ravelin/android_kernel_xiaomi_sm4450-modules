// SPDX-License-Identifier: GPL-2.0-only
/*
 * Xiaomi thermal control interface (/sys/class/thermal/thermal_message).
 *
 * Based on the sky-t-oss mi_thermal_interface driver. Carries the union of the
 * nodes used by the sky, breeze, flame and mist mi_thermald builds, so one
 * module serves all sm4450 devices. Per-device data comes from the DT
 * "thermal-message" and "thermal-screen" nodes.
 */

#include <linux/atomic.h>
#include <linux/cpufreq.h>
#include <linux/device.h>
#include <linux/kernfs.h>
#include <linux/module.h>
#include <linux/of.h>
#include <linux/pm_qos.h>
#include <linux/slab.h>
#include <linux/soc/qcom/panel_event_notifier.h>
#include <linux/string.h>
#include <linux/sysfs.h>
#include <linux/workqueue.h>
#include <drm/drm_panel.h>

#define BUF_SIZE 128

/* Optional hooks provided by Xiaomi charger drivers that forward to the ADSP. */
extern void set_board_temp(int board_temp);
extern void set_thermal_scene(int scene);

struct cpufreq_device {
	int id;
	unsigned int cpufreq_state;
	unsigned int max_level;
	unsigned int *freq_table;	/* descending */
	struct cpufreq_policy *policy;
	struct freq_qos_request qos_req;
	struct list_head node;
};

static struct device *mi_thermal_dev;
static struct class *power_debug_class;
static LIST_HEAD(cpufreq_dev_list);
static DEFINE_MUTEX(cpufreq_list_lock);

static struct drm_panel *prim_panel;
static void *cookie;
static int screen_state;
static int screen_last_status;
static struct delayed_work screen_state_dw;
static int screen_retry_count = 10;
static struct delayed_work setup_dw;
static int setup_retry_count = 60;

static const char *board_sensor = "invalid";
static const char *ambient_sensor = "ABT-SENSOR";
static char board_sensor_temp[BUF_SIZE];
static char board_sensor_second_temp[BUF_SIZE];
static char board_sensor_other_temp[BUF_SIZE];
static char ambient_sensor_temp[BUF_SIZE];
static char boost_buf[BUF_SIZE];

static atomic_t switch_mode = ATOMIC_INIT(-1);
static atomic_t temp_state = ATOMIC_INIT(0);
static atomic_t balance_mode = ATOMIC_INIT(0);
static atomic_t boost_limit = ATOMIC_INIT(0);
static atomic_t flash_state = ATOMIC_INIT(0);
static atomic_t market_download_limit = ATOMIC_INIT(0);
static atomic_t modem_limit = ATOMIC_INIT(0);
static atomic_t modem_level = ATOMIC_INIT(0);
static atomic_t modem_rate = ATOMIC_INIT(0);
static atomic_t poor_modem_limit = ATOMIC_INIT(0);
static atomic_t wifi_limit = ATOMIC_INIT(0);
static atomic_t thermal_max_brightness = ATOMIC_INIT(0);
static atomic_t board_sensor_temp_comp = ATOMIC_INIT(0);
static atomic_t cpu_nolimit_temp = ATOMIC_INIT(0);
static u8 temp_aware_mode = 10;

static void (*board_temp_hook)(int);
static void (*thermal_scene_hook)(int);

/* CPU frequency limits */

static void cpu_limits_set_level(unsigned int cpu, unsigned int max_freq)
{
	struct cpufreq_device *cdev;
	unsigned int level;

	mutex_lock(&cpufreq_list_lock);
	list_for_each_entry(cdev, &cpufreq_dev_list, node) {
		if (!cpumask_test_cpu(cpu, cdev->policy->related_cpus))
			continue;
		for (level = 0; level <= cdev->max_level; level++) {
			if (max_freq >= cdev->freq_table[level])
				break;
		}
		if (level > cdev->max_level)
			level = cdev->max_level;
		if (cdev->cpufreq_state != level) {
			cdev->cpufreq_state = level;
			freq_qos_update_request(&cdev->qos_req,
						cdev->freq_table[level]);
		}
		break;
	}
	mutex_unlock(&cpufreq_list_lock);
}

static unsigned int find_next_max(struct cpufreq_frequency_table *table,
				  unsigned int prev_max)
{
	struct cpufreq_frequency_table *pos;
	unsigned int max = 0;

	cpufreq_for_each_valid_entry(pos, table) {
		if (pos->frequency > max && pos->frequency < prev_max)
			max = pos->frequency;
	}
	return max;
}

static void cpu_thermal_exit(void)
{
	struct cpufreq_device *cdev, *tmp;

	mutex_lock(&cpufreq_list_lock);
	list_for_each_entry_safe(cdev, tmp, &cpufreq_dev_list, node) {
		freq_qos_remove_request(&cdev->qos_req);
		cpufreq_cpu_put(cdev->policy);
		list_del(&cdev->node);
		kfree(cdev->freq_table);
		kfree(cdev);
	}
	mutex_unlock(&cpufreq_list_lock);
}

static int cpu_thermal_init(void)
{
	struct cpufreq_policy *policy;
	struct cpufreq_device *cdev;
	unsigned int cpu, i, freq, count;
	int ret;

	for_each_possible_cpu(cpu) {
		policy = cpufreq_cpu_get(cpu);
		if (!policy) {
			pr_err("%s: no cpufreq policy for cpu%u\n", __func__, cpu);
			return -EPROBE_DEFER;
		}
		/* One request per policy */
		if (policy->cpu != cpu) {
			cpufreq_cpu_put(policy);
			continue;
		}

		count = cpufreq_table_count_valid_entries(policy);
		if (!count) {
			cpufreq_cpu_put(policy);
			return -ENODEV;
		}

		cdev = kzalloc(sizeof(*cdev), GFP_KERNEL);
		if (!cdev) {
			cpufreq_cpu_put(policy);
			return -ENOMEM;
		}
		cdev->freq_table = kcalloc(count, sizeof(*cdev->freq_table),
					   GFP_KERNEL);
		if (!cdev->freq_table) {
			kfree(cdev);
			cpufreq_cpu_put(policy);
			return -ENOMEM;
		}
		cdev->policy = policy;
		cdev->id = cpu;
		cdev->max_level = count - 1;
		for (i = 0, freq = UINT_MAX; i < count; i++) {
			freq = find_next_max(policy->freq_table, freq);
			cdev->freq_table[i] = freq;
		}

		ret = freq_qos_add_request(&policy->constraints, &cdev->qos_req,
					   FREQ_QOS_MAX, cdev->freq_table[0]);
		if (ret < 0) {
			pr_err("%s: failed to add freq constraint: %d\n",
			       __func__, ret);
			kfree(cdev->freq_table);
			kfree(cdev);
			cpufreq_cpu_put(policy);
			return ret;
		}

		mutex_lock(&cpufreq_list_lock);
		list_add_tail(&cdev->node, &cpufreq_dev_list);
		mutex_unlock(&cpufreq_list_lock);
	}
	return 0;
}

/* sysfs */

#define MI_ATOMIC_ATTR(_name, _var)						\
static ssize_t _name##_show(struct device *dev,					\
			    struct device_attribute *attr, char *buf)		\
{										\
	return sysfs_emit(buf, "%d\n", atomic_read(&_var));			\
}										\
static ssize_t _name##_store(struct device *dev,				\
			     struct device_attribute *attr,			\
			     const char *buf, size_t len)			\
{										\
	int val;								\
										\
	if (kstrtoint(strim((char *)buf), 10, &val))				\
		return -EINVAL;							\
	atomic_set(&_var, val);							\
	return len;								\
}										\
static DEVICE_ATTR_RW(_name)

#define MI_STRING_ATTR(_name, _buf)						\
static ssize_t _name##_show(struct device *dev,					\
			    struct device_attribute *attr, char *buf)		\
{										\
	return sysfs_emit(buf, "%s", _buf);					\
}										\
static ssize_t _name##_store(struct device *dev,				\
			     struct device_attribute *attr,			\
			     const char *buf, size_t len)			\
{										\
	strscpy(_buf, buf, sizeof(_buf));					\
	return len;								\
}										\
static DEVICE_ATTR_RW(_name)

MI_ATOMIC_ATTR(temp_state, temp_state);
MI_ATOMIC_ATTR(balance_mode, balance_mode);
MI_ATOMIC_ATTR(boost_limit, boost_limit);
MI_ATOMIC_ATTR(flash_state, flash_state);
MI_ATOMIC_ATTR(market_download_limit, market_download_limit);
MI_ATOMIC_ATTR(modem_limit, modem_limit);
MI_ATOMIC_ATTR(modem_level, modem_level);
MI_ATOMIC_ATTR(modem_rate, modem_rate);
MI_ATOMIC_ATTR(poor_modem_limit, poor_modem_limit);
MI_ATOMIC_ATTR(wifi_limit, wifi_limit);
MI_ATOMIC_ATTR(thermal_max_brightness, thermal_max_brightness);
MI_ATOMIC_ATTR(board_sensor_temp_comp, board_sensor_temp_comp);
MI_ATOMIC_ATTR(cpu_nolimit_temp, cpu_nolimit_temp);

MI_STRING_ATTR(boost, boost_buf);
MI_STRING_ATTR(board_sensor_second_temp, board_sensor_second_temp);
MI_STRING_ATTR(board_sensor_other_temp, board_sensor_other_temp);
MI_STRING_ATTR(ambient_sensor_temp, ambient_sensor_temp);

static ssize_t sconfig_show(struct device *dev,
			    struct device_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%d\n", atomic_read(&switch_mode));
}

static ssize_t sconfig_store(struct device *dev,
			     struct device_attribute *attr,
			     const char *buf, size_t len)
{
	int val;

	if (kstrtoint(strim((char *)buf), 10, &val))
		return -EINVAL;
	if (thermal_scene_hook)
		thermal_scene_hook(val);
	atomic_set(&switch_mode, val);
	return len;
}
static DEVICE_ATTR_RW(sconfig);

static ssize_t board_sensor_temp_show(struct device *dev,
				      struct device_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%s", board_sensor_temp);
}

static ssize_t board_sensor_temp_store(struct device *dev,
				       struct device_attribute *attr,
				       const char *buf, size_t len)
{
	int val;

	strscpy(board_sensor_temp, buf, sizeof(board_sensor_temp));
	if (board_temp_hook && !kstrtoint(strim(board_sensor_temp), 10, &val))
		board_temp_hook(val / 100);
	return len;
}
static DEVICE_ATTR_RW(board_sensor_temp);

static ssize_t board_sensor_show(struct device *dev,
				 struct device_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%s", board_sensor);
}
static DEVICE_ATTR_RO(board_sensor);

static ssize_t ambient_sensor_show(struct device *dev,
				   struct device_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%s", ambient_sensor);
}
static DEVICE_ATTR_RO(ambient_sensor);

static ssize_t screen_state_show(struct device *dev,
				 struct device_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%d\n", screen_state);
}
static DEVICE_ATTR_RO(screen_state);

static ssize_t cpu_limits_show(struct device *dev,
			       struct device_attribute *attr, char *buf)
{
	return 0;
}

static ssize_t cpu_limits_store(struct device *dev,
				struct device_attribute *attr,
				const char *buf, size_t len)
{
	unsigned int cpu, max;

	if (sscanf(buf, "cpu%u %u", &cpu, &max) != 2)
		return -EINVAL;
	cpu_limits_set_level(cpu, max);
	return len;
}
static DEVICE_ATTR_RW(cpu_limits);

static struct attribute *mi_thermal_attrs[] = {
	&dev_attr_temp_state.attr,
	&dev_attr_balance_mode.attr,
	&dev_attr_boost.attr,
	&dev_attr_boost_limit.attr,
	&dev_attr_cpu_limits.attr,
	&dev_attr_cpu_nolimit_temp.attr,
	&dev_attr_flash_state.attr,
	&dev_attr_market_download_limit.attr,
	&dev_attr_modem_limit.attr,
	&dev_attr_modem_level.attr,
	&dev_attr_modem_rate.attr,
	&dev_attr_poor_modem_limit.attr,
	&dev_attr_wifi_limit.attr,
	&dev_attr_sconfig.attr,
	&dev_attr_screen_state.attr,
	&dev_attr_thermal_max_brightness.attr,
	&dev_attr_board_sensor.attr,
	&dev_attr_board_sensor_temp.attr,
	&dev_attr_board_sensor_temp_comp.attr,
	&dev_attr_board_sensor_second_temp.attr,
	&dev_attr_board_sensor_other_temp.attr,
	&dev_attr_ambient_sensor.attr,
	&dev_attr_ambient_sensor_temp.attr,
	NULL,
};

static const struct attribute_group mi_thermal_group = {
	.attrs = mi_thermal_attrs,
};

/* /sys/class/power_debug/temp_aware (mist) */

static ssize_t temp_aware_show(const struct class *class,
			       const struct class_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%u\n", temp_aware_mode);
}

static ssize_t temp_aware_store(const struct class *class,
				const struct class_attribute *attr,
				const char *buf, size_t len)
{
	u8 val;

	if (kstrtou8(buf, 10, &val) || val > 9)
		return -EINVAL;
	temp_aware_mode = val;
	return len;
}
static CLASS_ATTR_RW(temp_aware);

/* Screen state */

static void screen_state_callback(enum panel_event_notifier_tag tag,
				  struct panel_event_notification *notification,
				  void *client_data)
{
	if (!notification || notification->notif_data.early_trigger)
		return;

	switch (notification->notif_type) {
	case DRM_PANEL_EVENT_UNBLANK:
		screen_state = 1;
		break;
	case DRM_PANEL_EVENT_BLANK:
	case DRM_PANEL_EVENT_BLANK_LP:
		screen_state = 0;
		break;
	default:
		return;
	}

	if (screen_last_status != screen_state) {
		sysfs_notify(&mi_thermal_dev->kobj, NULL, "screen_state");
		screen_last_status = screen_state;
	}
}

static struct drm_panel *find_active_panel(struct device_node *np)
{
	struct device_node *node;
	struct drm_panel *panel;
	int i, count;

	count = of_count_phandle_with_args(np, "panel", NULL);
	for (i = 0; i < count; i++) {
		node = of_parse_phandle(np, "panel", i);
		panel = of_drm_find_panel(node);
		of_node_put(node);
		if (!IS_ERR(panel))
			return panel;
	}
	return NULL;
}

static void screen_state_check(struct work_struct *work)
{
	struct device_node *np;

	np = of_find_node_by_name(NULL, "thermal-screen");
	if (!np)
		return;

	prim_panel = find_active_panel(np);
	of_node_put(np);

	if (!prim_panel) {
		if (screen_retry_count-- > 0)
			schedule_delayed_work(&screen_state_dw, 5 * HZ);
		else
			pr_err("%s: no active panel\n", __func__);
		return;
	}

	cookie = panel_event_notifier_register(PANEL_EVENT_NOTIFICATION_PRIMARY,
			PANEL_EVENT_NOTIFIER_CLIENT_THERMAL, prim_panel,
			screen_state_callback, NULL);
	if (IS_ERR_OR_NULL(cookie)) {
		pr_err("%s: failed to register panel notifier\n", __func__);
		cookie = NULL;
	}
}

/* Device creation */

static void of_parse_thermal_message(void)
{
	struct device_node *np;

	np = of_find_node_by_name(NULL, "thermal-message");
	if (!np)
		return;

	of_property_read_string(np, "board-sensor", &board_sensor);
	of_property_read_string(np, "ambient-sensor", &ambient_sensor);
	of_node_put(np);
	pr_info("board sensor: %s\n", board_sensor);
}

/*
 * The thermal class is private to thermal_core. Find it through any device
 * that lives in /sys/class/thermal (all entries there are symlinks).
 */
static const struct class *find_thermal_class(void)
{
	struct kernfs_node *class_kn, *thermal_kn, *kn;
	const struct class *cls = NULL;
	struct kobject *kobj;

	class_kn = kernfs_find_and_get(kernel_kobj->sd->parent, "class");
	if (!class_kn)
		return NULL;
	thermal_kn = kernfs_find_and_get(class_kn, "thermal");
	kernfs_put(class_kn);
	if (!thermal_kn)
		return NULL;

	kn = kernfs_find_and_get(thermal_kn, "thermal_zone0");
	if (!kn)
		kn = kernfs_find_and_get(thermal_kn, "cooling_device0");
	kernfs_put(thermal_kn);
	if (!kn)
		return NULL;

	if (kernfs_type(kn) == KERNFS_LINK && kn->symlink.target_kn) {
		kobj = kn->symlink.target_kn->priv;
		if (kobj)
			cls = kobj_to_dev(kobj)->class;
	}
	kernfs_put(kn);
	return cls;
}

static int mi_thermal_setup(void)
{
	const struct class *thermal_class;
	int ret;

	thermal_class = find_thermal_class();
	if (!thermal_class)
		return -EPROBE_DEFER;

	ret = cpu_thermal_init();
	if (ret) {
		cpu_thermal_exit();
		return ret;
	}

	of_parse_thermal_message();

	board_temp_hook = symbol_get(set_board_temp);
	thermal_scene_hook = symbol_get(set_thermal_scene);

	mi_thermal_dev = device_create(thermal_class, NULL, MKDEV(0, 0), NULL,
				       "thermal_message");
	if (IS_ERR(mi_thermal_dev)) {
		ret = PTR_ERR(mi_thermal_dev);
		mi_thermal_dev = NULL;
		goto err_hooks;
	}

	ret = sysfs_create_group(&mi_thermal_dev->kobj, &mi_thermal_group);
	if (ret)
		goto err_dev;

	power_debug_class = class_create("power_debug");
	if (!IS_ERR(power_debug_class)) {
		if (class_create_file(power_debug_class, &class_attr_temp_aware)) {
			class_destroy(power_debug_class);
			power_debug_class = NULL;
		}
	} else {
		power_debug_class = NULL;
	}

	schedule_delayed_work(&screen_state_dw, 5 * HZ);
	return 0;

err_dev:
	device_unregister(mi_thermal_dev);
	mi_thermal_dev = NULL;
err_hooks:
	if (board_temp_hook)
		symbol_put(set_board_temp);
	if (thermal_scene_hook)
		symbol_put(set_thermal_scene);
	board_temp_hook = NULL;
	thermal_scene_hook = NULL;
	cpu_thermal_exit();
	return ret;
}

/* cpufreq and the thermal zones may come up after this module loads. */
static void mi_thermal_setup_work(struct work_struct *work)
{
	int ret = mi_thermal_setup();

	if (ret == -EPROBE_DEFER && setup_retry_count-- > 0) {
		schedule_delayed_work(&setup_dw, HZ);
		return;
	}
	if (ret)
		pr_err("%s: setup failed: %d\n", __func__, ret);
}

static int __init mi_thermal_interface_init(void)
{
	INIT_DELAYED_WORK(&screen_state_dw, screen_state_check);
	INIT_DELAYED_WORK(&setup_dw, mi_thermal_setup_work);
	schedule_delayed_work(&setup_dw, 0);
	return 0;
}

static void __exit mi_thermal_interface_exit(void)
{
	cancel_delayed_work_sync(&setup_dw);
	cancel_delayed_work_sync(&screen_state_dw);
	if (!mi_thermal_dev)
		return;

	if (cookie)
		panel_event_notifier_unregister(cookie);

	if (power_debug_class) {
		class_remove_file(power_debug_class, &class_attr_temp_aware);
		class_destroy(power_debug_class);
	}

	sysfs_remove_group(&mi_thermal_dev->kobj, &mi_thermal_group);
	device_unregister(mi_thermal_dev);

	if (board_temp_hook)
		symbol_put(set_board_temp);
	if (thermal_scene_hook)
		symbol_put(set_thermal_scene);

	cpu_thermal_exit();
}

module_init(mi_thermal_interface_init);
module_exit(mi_thermal_interface_exit);

MODULE_DESCRIPTION("Xiaomi thermal control interface");
MODULE_LICENSE("GPL");
