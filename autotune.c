#include <stdio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "driver/audio.h"
 
#define BUF_SIZE (20) /* 20 packets ~ 5 seconds of audio */
#define INT_BUF_SIZE (BUF_SIZE * 2048)
 
long unsigned int buffer[BUF_SIZE];
int int_buffer[INT_BUF_SIZE];
int idx;
int audio_fd;

/* Read and save samples from the device to our buffer */
void read_samples() {
    audio_arg_t vla;
  
    if (ioctl(audio_fd, AUDIO_READ_SAMPLES, &vla)) {
        perror("ioctl(AUDIO_READ_SAMPLES) failed");
        return;
    }
		
		buffer[idx++] = vla.data;
}
 
int main(int argc, char ** argv)
{
    idx = 0;

    static const char filename[] = "/dev/audio";

    printf("Audio Userspace program started\n");

    if ( (audio_fd = open(filename, O_RDWR)) == -1) {
        fprintf(stderr, "could not open %s\n", filename);
        return -1;
    }

		printf("buf size: %d\n", BUF_SIZE);
    while(idx < BUF_SIZE){
        read_samples();
	}

    for (int i = 0; i < BUF_SIZE; i++) {
        audio_arg_t vla;
        vla.data = buffer[i];
        int_buffer[i] = (int)vla.data; // Extract the int from audio_arg_t
    }

    printf("sample read done");
    for (int i = 50; i < 150; i++) // change i based on our test
        printf("samp: %lu\n", int_buffer[i]);

    printf("Audio Userspace program terminating\n");
    return 0;
}