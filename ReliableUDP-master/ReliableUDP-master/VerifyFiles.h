#pragma once
//function to calculate the CRC of a packet
unsigned int crc32(const char* data, int size)
{
    unsigned int crc = 0xffffffff;
    while (size--) {
        crc ^= *data++;
        for (int i = 0; i < 8; i++)
            crc = (crc >> 1) ^ ((crc & 1) ? 0xedb88320 : 0);
    }
    return crc ^ 0xffffffff;
}