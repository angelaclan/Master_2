
#include "chardev.h"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 6, 0) 
#define HAVE_PROC_OPS 
#endif

#define PROCFS_MAX_SIZE 1024 
#define PROCFS_NAME "asee_channel" 

#ifdef HAVE_PROC_OPS 

/* This structure hold information about the /proc file */ 
static struct proc_dir_entry *our_proc_file; 
/* The buffer used to store character for this module */ 
static char procfs_buffer[PROCFS_MAX_SIZE]; 
/* The size of the buffer */ 
static unsigned long procfs_buffer_size;

static const struct proc_ops proc_file_fops = { 

    .proc_read = procfile_read, 

    .proc_write = procfile_write, 

}; 

#else 

static const struct file_operations proc_file_fops = { 

    .read = procfile_read, 

    .write = procfile_write, 

}; 

#endif 

 
extern static struct buffer; 

/* The size of the buffer */ 
procfs_buffer_size = 0;

/* This function is called then the /proc file is read */
static ssize_t procfile_read(struct file *filePointer, char __user *buffer, size_t buffer_length, loff_t *offset) 
{ 

    int len = sizeof(buffer_s->msg); 
    ssize_t ret = len;  

    if (copy_to_user(buffer, b->msg, len)) { 

        pr_info("copy_to_user failed\n"); 

        ret = 0; 

    } else { 

        pr_info("procfile read %s\n", filePointer->f_path.dentry->d_name.name); 

        *offset += len; 

    } 

    return ret; 

}  

/* This function is called with the /proc file is written. */ 
static ssize_t procfile_write(struct file *file, const char __user *buff, size_t len, loff_t *off) 

{ 
    if (len > buffer_s-> buf_size)
	{
		pr_info("ERROR : Given string is larger than exsit buffer length");
		return -EINVAL;
	} 
	
	procfs_buffer_size = buffer_changesize(buffer_s, len);

    if (procfs_buffer_size > PROCFS_MAX_SIZE) 
        procfs_buffer_size = PROCFS_MAX_SIZE; 

    if (copy_from_user(procfs_buffer, buff, procfs_buffer_size)) 
        return -EFAULT; 

    procfs_buffer[procfs_buffer_size & (PROCFS_MAX_SIZE - 1)] = '\0'; 
    
    copy_from_user(buffer_s->msg, buff, len);
	
    pr_info("procfile write %s\n", procfs_buffer); 

 

    return procfs_buffer_size; 

} 

 

 

static int __init procfs2_init(void) 

{ 

    our_proc_file = proc_create(PROCFS_NAME, 0644, NULL, &proc_file_fops); 

    if (NULL == our_proc_file) { 

        proc_remove(our_proc_file); 

        pr_alert("Error:Could not initialize /proc/%s\n", PROCFS_NAME); 

        return -ENOMEM; 

    } 

 

    pr_info("/proc/%s created\n", PROCFS_NAME); 

    return 0; 

} 

 

static void __exit procfs2_exit(void) 

{ 

    proc_remove(our_proc_file); 

    pr_info("/proc/%s removed\n", PROCFS_NAME); 

} 

 

module_init(procfs2_init); 

module_exit(procfs2_exit); 

 

MODULE_LICENSE("GPL");