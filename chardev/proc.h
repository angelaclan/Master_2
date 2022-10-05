#ifndef _PROC_H_
#define _PROC_H_

/* prototypes of proc functions */
int __init procfs2_init(void);
void __exit procfs2_exit(void);
ssize_t procfile_read(struct file *filePointer, char __user *buffer, size_t buffer_length, loff_t *offset);
ssize_t procfile_write(struct file *file, const char __user *buff, size_t len, loff_t *off);

#endif
