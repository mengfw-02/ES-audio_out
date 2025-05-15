ifneq (${KERNELRELEASE},)

	obj-m := audio.o
else
	
audio.o:
	cc -c audio.c audio.h

endif

