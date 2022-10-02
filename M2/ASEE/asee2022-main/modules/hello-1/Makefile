KERNEL_TREE= ../../../build/kvm/

obj-m += hello-1.o

all:
	make -C $(KERNEL_TREE) M=$(PWD) modules 

clean:
	make -C $(KERNEL_TREE) M=$(PWD) clean

