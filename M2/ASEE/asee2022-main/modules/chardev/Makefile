KERNEL_TREE= ../../../build/kvm/


obj-$(CONFIG_ISDN_I4L) += isdn.o 
isdn-m := chardev.o proc.o

all:
	make -C $(KERNEL_TREE) M=$(PWD) modules 

clean:
	make -C $(KERNEL_TREE) M=$(PWD) clean

