/* Creates a WAV file from an array of ints.
 * Output is stereo, signed 32-bit samples
 * 
 * Based on code from Kevin Karplus, licensed under Creative Commons
 * https://karplus4arduino.wordpress.com/2011/10/08/making-wav-files-from-c-programs/
 */
 
#include <stdio.h>
#include <assert.h>
#include "make_wav.h"


void write_little_endian(long unsigned int word, int num_bytes, FILE *wav_file)
{
    unsigned buf;
    while(num_bytes>0)
    {   buf = word & 0xff;
        fwrite(&buf, 1,1, wav_file);
        num_bytes--;
        word >>= 8;
    }
}
 
/* information about the WAV file format from
    http://ccrma.stanford.edu/courses/422/projects/WaveFormat/
 */
 
void write_wav(char * filename, unsigned long num_samples, long unsigned int * data, int s_rate)
{
    FILE* wav_file;
    unsigned int sample_rate;
    unsigned int num_channels;
    unsigned int bytes_per_sample;
    unsigned int byte_rate;
    unsigned long i, j;    /* counters for samples */
 
    num_channels = 1;   /* stereo */
    bytes_per_sample = 3; /* 24 bit samples */
 
    sample_rate = (unsigned int) s_rate;
 
    byte_rate = sample_rate*num_channels*bytes_per_sample;
 
    wav_file = fopen(filename, "w");
    assert(wav_file);   /* make sure it opened */
 
    /* write RIFF header */
    fwrite("RIFF", 1, 4, wav_file);
    write_little_endian(36 + bytes_per_sample* num_samples*num_channels, 4, wav_file);
    fwrite("WAVE", 1, 4, wav_file);
 
    /* write fmt  subchunk */
    fwrite("fmt ", 1, 4, wav_file);
    write_little_endian(16, 4, wav_file);   /* SubChunk1Size is 16 */
    write_little_endian(1, 2, wav_file);    /* PCM is format 1 */
    write_little_endian(num_channels, 2, wav_file);
    write_little_endian(sample_rate, 4, wav_file);
    write_little_endian(byte_rate, 4, wav_file);
    write_little_endian(num_channels*bytes_per_sample, 2, wav_file);  /* block align */
    write_little_endian(8*bytes_per_sample, 2, wav_file);  /* bits/sample */
 
    /* write data subchunk */
    fwrite("data", 1, 4, wav_file);
    write_little_endian(bytes_per_sample*num_samples*num_channels, 4, wav_file);
    for (i=0; i<num_samples; i+=num_channels)
        for(j=0; j<num_channels; j++)
            write_little_endian((unsigned int)(data[i+j]), bytes_per_sample, wav_file);

    /* close the file */
    fclose(wav_file);
}
