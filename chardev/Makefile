KERNEL_TREE=../../../build/kvm

obj-m += fin.o
fin-objs := proc.o chardev.o

all:
	make -C $(KERNEL_TREE) M=$(PWD) modules 

clean:
	make -C $(KERNEL_TREE) M=$(PWD) clean

