/* outputs the buffer size and the number of characters currently contained in the buffer 
 * int kstrtoll (const char * s, unsigned int base, long long * res);
 * unsigned long __copy_to_user (void __user * to, const void * from, unsigned long n);
 */

#include "chardev.h"
#include "proc.h"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 6, 0) 
#define HAVE_PROC_OPS 
#endif

#define PROCFS_MAX_SIZE 1024 
#define PROCFS_NAME "asee_channel" 


extern struct buffer buffer_s;

static struct class* cls;

static struct proc_dir_entry *our_proc_file; /* This structure hold information about the /proc file */ 						
static char procfs_buffer[PROCFS_MAX_SIZE]; /* The buffer used to store character for this module */ 
static unsigned long procfs_buffer_size = 0; /* The size of the buffer */ 

static const struct proc_ops proc_file_fops = { 

    .proc_read = procfile_read, 
    .proc_write = procfile_write, 
}; 

static struct file_operations chardv_fops = {
	.read = device_read,
	.write = device_write,
	.open = device_open,
	.release = device_release,
}; 

/* This function is called then the /proc file is read */
ssize_t procfile_read(struct file *filePointer, char __user *buffer, size_t buffer_length, loff_t *offset) 
{ 

    int len = sizeof(buffer_s.msg); 
    ssize_t ret = len;  

    if (copy_to_user(buffer, buffer_s.msg, len)) { 
        pr_info("copy_to_user failed\n"); 
        ret = 0; 
    } else { 
        pr_info("procfile read %s\n", filePointer->f_path.dentry->d_name.name); 
        *offset += len; 
    } 

    return ret; 
}  

/* This function is called with the /proc file is written. */ 
ssize_t procfile_write(struct file *file, const char __user *buff, size_t len, loff_t *off) 

{    					
   	long new_bufsize = 0;
    int bufsize_output = 0;
    
   	procfs_buffer_size = len; 
   															 
    if (procfs_buffer_size > PROCFS_MAX_SIZE) 
        procfs_buffer_size = PROCFS_MAX_SIZE; 

    if (copy_from_user(procfs_buffer, buff, procfs_buffer_size)) 
        return -EFAULT; 

    procfs_buffer[procfs_buffer_size & (PROCFS_MAX_SIZE - 1)] = '\0'; /* kernel buffer must end string with '\0' */
    pr_info("procfile write %s\n", procfs_buffer);
    
    
    if (kstrtol(procfs_buffer, 10, &new_bufsize))  /* transfrom number_string to int, using as new buffer size */ 
    	return -EINVAL ;
    bufsize_output = buffer_changesize(&buffer_s, new_bufsize); /* cmp given buffer size and kernel buffer size, store the msg, allocat memeory space */   
    
    pr_info("new buffer size : %d\n", bufsize_output); 
	
    return bufsize_output; 
} 
 

int __init procfs2_init(void) 
{ 
    our_proc_file = proc_create(PROCFS_NAME, 0644, NULL, &proc_file_fops); 

    if (NULL == our_proc_file) { 
        proc_remove(our_proc_file); 
        pr_alert("Error:Could not initialize /proc/%s\n", PROCFS_NAME); 
        return -ENOMEM; 
    } 
    
	buffer_init(&buffer_s, 16);
	buffer_s.major = register_chrdev(0, DEVICE_NAME, &chardv_fops);
	
	if (buffer_s.major < 0) {
		pr_alert("Registering char device failed with %d\n", buffer_s.major);
		return buffer_s.major;
	}
	pr_info("Assigned major number : %d\n", buffer_s.major);
	cls = class_create(THIS_MODULE, DEVICE_NAME);
	device_create(cls, NULL, MKDEV(buffer_s.major, 0), NULL, DEVICE_NAME);
	pr_info("Device created on /dev/%s\n", DEVICE_NAME);
	
    pr_info("/proc/%s created\n", PROCFS_NAME); 

    return 0; 
} 

void __exit procfs2_exit(void) 
{   
	device_destroy(cls, MKDEV(buffer_s.major, 0));
	class_destroy(cls);
	buffer_free(&buffer_s);
	unregister_chrdev(buffer_s.major, DEVICE_NAME);
	
    proc_remove(our_proc_file); 
    pr_info("/proc/%s removed\n", PROCFS_NAME); 
} 

module_init(procfs2_init); 

module_exit(procfs2_exit); 

 

MODULE_LICENSE("GPL");
