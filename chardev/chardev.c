/*
 * chardev.c: A read only device that reads char in the order of input and
 */

#include "chardev.h"

enum{
	CDEV_NOT_USED = 0,
	CDEV_EXCLUSIVE_OPEN = 1,
	};

static atomic_t already_open = ATOMIC_INIT(CDEV_NOT_USED);

struct buffer buffer_s;

void buffer_init(struct buffer* b, int size)
{
	 b->major = 0;
	 b->buf_size = size;
	 b->msg = kmalloc(size, GFP_KERNEL);
	 b->count = 0;
	 b->head = 0;
	 b->tail = 0;

};

void buffer_free(struct buffer* b)
{
	 b->major = 0;
	 b->buf_size = 0; 
	 kfree(b->msg);
	 b->count = 0;
	 b->head = 0;
	 b->tail = 0; 
};

/*cmp size, store msg, allocat space */
int buffer_changesize(struct buffer* b, int newsize)
{
	 char* temp_buffer;
	 
	 if(b->buf_size < newsize) return -EINVAL;
	 
	 strcpy(temp_buffer, b->msg); /*strcpy(char *dest, const char *src)*/
	 
	 buffer_free(b);
	 buffer_init(b, newsize);
	 
	 return b->buf_size;
}

/* open a device file, ex : cat /dev/chardev */
int device_open(struct inode *inode, struct file *file )
{

	if (atomic_cmpxchg(&already_open, CDEV_NOT_USED, CDEV_EXCLUSIVE_OPEN))
		return -EBUSY;
	
	pr_info("Already told you %d times %s \n", buffer_s.count++, buffer_s.msg);	
	try_module_get(THIS_MODULE);
	
	return SUCCESS;
}

/* close a device file when called by a proc */
int device_release(struct inode *inode, struct file *file )
{
	atomic_set(&already_open, CDEV_NOT_USED);
	/* decrement the counter or once the file was opened we can never get rid of the module */
	module_put(THIS_MODULE);
	return SUCCESS;	
}

/* read from an opened device file */
ssize_t device_read(struct file *filp, char __user *buffer, size_t length, loff_t *offset){
	int bytes_read = 0; /* number of bytes written to buffer */
	int i = 0;
	/* we copy the data from kernel data segment to user data segment */
	while(bytes_read < length && (buffer_s.count)!=0){
		put_user((buffer_s.msg[buffer_s.tail++]), &buffer[i++]);
		if(buffer_s.tail == 16) buffer_s.tail = 0;
		bytes_read++;
		buffer_s.count--;
	}

	return bytes_read;
}
/* write to an opened device file, ex : echo "cafe" > /dev/coffee */
ssize_t device_write(struct file *filp, const char __user *buffer, size_t length, loff_t *offset){
	
	int bytes_write = 0;
	int i = 0;

	
	while(length > i && buffer_s.count < 16){
		get_user((buffer_s.msg[buffer_s.head]), &buffer[i++]);
		buffer_s.head++;
		buffer_s.count++;
		bytes_write++;
		if(buffer_s.head == 16) buffer_s.head = 0;
	}
	
	return bytes_write;	
}


MODULE_LICENSE("GPL");
