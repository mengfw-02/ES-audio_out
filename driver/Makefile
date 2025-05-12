ifneq (${KERNELRELEASE},)

# KERNELRELEASE defined: we are being compiled as part of the Kernel
        obj-m := audio.o

else

audio.o:
	cc -c audio.c audio.h


endif 
