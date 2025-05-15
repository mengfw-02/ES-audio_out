#include <stdio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "wavfile_construction/make_wav.h"
#include "audio.h"
 
#define S_RATE  (8000)
#define AUDIO_BUF_SIZE (S_RATE*5) /* 5 second buffer for L/R */
#define BUF_SIZE (20) /* 20 packets ~ 5 seconds of audio */
#define INT_BUF_SIZE (BUF_SIZE * 2048)
#define BUF_SIZE (S_RATE*5*2)
 
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
    
    // Copy each sample from vla.data to int_buffer
    for (int i = 0; i < 2048; i++) {
        int_buffer[idx * 2048 + i] = vla.data[i];
    }
    idx++;
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

    printf("sample read done");
    for (int i = 50; i < 150; i++) // change i based on our test
        printf("samp: %d\n", int_buffer[i]);

    write_wav("./wavfiles/anonymous_audio.wav", AUDIO_BUF_SIZE, (long unsigned int *)int_buffer, S_RATE);

    printf("Audio Userspace program terminating\n");
    return 0;
}