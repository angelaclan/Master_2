#ifndef CHARDEV_H_   /* Include guard */
#define CHARDEV_H_

#include <linux/cdev.h>
#include <linux/delay.h>
#include <linux/device.h>
#include <linux/fs.h>
#include <linux/init.h>
#include <linux/irq.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/poll.h>
#include <linux/proc_fs.h> /* Necessary because we use the proc fs */ 
#include <linux/uaccess.h> /* for copy_from_user */ 
#include <linux/version.h>

#define SUCCESS 0
#define DEVICE_NAME "chardev"

struct buffer {

	int major;
	int buf_size;
	char* msg;
	int count;
	int head;
	int tail;
};  

/* prototypes of buffer struct */
void buffer_init(struct buffer*, int);
void buffer_free(struct buffer*);
int buffer_changesize(struct buffer*, int);

/* prototypes of chardev functions */
int device_open(struct inode *, struct file *); 
int device_release(struct inode *, struct file *);
ssize_t device_read(struct file *, char __user *, size_t, loff_t *);
ssize_t device_write(struct file *, const char __user *, size_t, loff_t *);

/* prototypes of proc functions */
int __init procfs2_init(void);
void __exit procfs2_exit(void);
ssize_t procfile_read(struct file *filePointer, char __user *buffer, size_t buffer_length, loff_t *offset);
ssize_t procfile_write(struct file *file, const char __user *buff, size_t len, loff_t *off);
                             
#endif

