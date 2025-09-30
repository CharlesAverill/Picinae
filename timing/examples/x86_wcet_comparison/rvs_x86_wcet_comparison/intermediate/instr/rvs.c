/* RVS - C Map and Trace Instrumentation library */
/* RVS 3.23 */

/*=============================================================================
* Rapita Systems Ltd. - Rapita Verification Suite (RVS) Source Code License
*
* DOC13027 V1 (2014/01/28)
*
* (c) 2004-2021 Rapita Systems Ltd. All rights reserved
* -----------------------------------------------------------------------------
*
* Subject to the terms and conditions of the RVS License Agreement, Rapita
* Systems Ltd. grants the Licensee a non-exclusive, non-transferable license to
* use the source code contained in this file (the "Licensed Software").
*
* The Licensee may use the Licensed Software for its own use, and may
* translate or modify it or incorporate it into other software. The Licensee
* may not, however, alter or remove the copyright notice or the text of the
* source code license.
*
* The Licensee may not, however, transfer or sublicense the Licensed Software
* to any third party, in whole or in part, in any form, whether modified or
* unmodified without the prior written consent of Rapita Systems Ltd.
*
* The original and any copies of the Licensed Software, made by the Licensee,
* including translations, compilations, partial copies, modifications,
* and updates, are the property of Rapita Systems Ltd.
*
* The Licensee recognizes that Rapita Systems Ltd. regards the Licensed
* Software as its proprietary information and as confidential trade secrets.
*
* The Licensee agrees not to provide or to otherwise make available in any
* form the Licensed Software, or any portion thereof, to any person other
* than employees of the Licensee without the prior written consent of
* Rapita Systems Ltd.
*
* The Licensee further agrees to treat the Licensed Programs with at least
* the same degree of care with which the Licensee treats its own confidential
* information and in no event with less care than is reasonably required to
* protect the confidentiality of the Licensed Software.
*
* -----------------------------------------------------------------------------
*
* Registered in the UK, number 5011090.
* Registered address:
*   Atlas House, Link Business Park
*   Osbaldwick Link Road
*   York
*   YO10 3JB
*   UK
* Phone: +44 (0) 1904 413 945
*
* email: support@rapitasystems.com
* http://www.rapitasystems.com/
*
*=============================================================================
*/

#include "rvs.h"
#include "rvs_ipoint.h"

#include <stdlib.h>
#include <stdio.h>

#ifdef _WIN32
#include <windows.h>
#else
#include <time.h>
#include <errno.h>
#endif
#include <x86intrin.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The trace file handler */
FILE *trace_file = NULL;

t_rvs_uint64 time_correction = 0;

#ifndef RVS_TIMING
#define RVS_TIMING RVS_PMC_NULL
#endif

/*************************************************************
 * READ_TIMER: read the processor cycle counter (x86)
 *************************************************************/
#define READ_TIMER(_VAR) _VAR=__rdtsc()

/*************************************************************
 * READ_TIMER: read various PMC values
 *************************************************************/
#define READ_PMC(_PMC, _VAR) if (PMC == RVS_TIMING) {READ_TIMER(_VAR);} else {_VAR = _PMC;}

/**
 * Instrumentation point routine
 *
 * All ipoints are recorded or outputted via this routine and as such it
 * should be as fast and lightweight as possible
 *
 * This call should output the id or record it in memory ready for
 * RVS_Output() to output in bulk.
 *
 * @param id ID to record.
 */
void RVS_Ipoint(t_rvs_ipoint_id id)
{

   t_rvs_uint64 t1;

   t_rvs_uint64 t2;

   READ_TIMER(t1);

   /* Some host OS (XP, for example) will raise an exception if trace_file is NULL at this point
    * In order to be consistent across platforms, do not output if RVS_Init() has not been called */
   if (trace_file != NULL)
   {

      fprintf(trace_file, "%u %llu\n", id, t1 - time_correction);

   }

    READ_TIMER(t2);
   /* discount the time spent writing to the file */
   time_correction += (t2 - t1);

}

/**
 * Helper to open the RVS stream, done in RVS_Init() and RVS_Begin_Test()
 */
static void RVS_Open_Stream(void)
{
   /* Open the trace file */

   const char *file_name = "rvs_trace.txt";

   if (trace_file == NULL)
   {
      trace_file = fopen(file_name, "a");
   }
   if (trace_file == NULL)
   {
      fprintf(stderr, "Error: Could not open the trace file '%s'\n", file_name);
      exit(1);
   }
}

/**
 * Helper to close the RVS stream, done only in RVS_RTS_Execute()
 */
void RVS_Close_Stream(void)
{
   /* ----- Close the trace file ----- */
   if (trace_file != NULL)
   {
      fclose(trace_file);
      trace_file = NULL;
   }
}

/**
 * Initialises RVS. This is an optional call typically inserted into the code
 * under test as early as possible. If required, call this before ipoints are
 * written out.
 *
 * Typical uses of this are:
 *  - Set up GPIO pins
 *  - Initialise a dynamic-map block
 *  - Open an output stream
 *
 * Be aware that if this is required then ipoints written out before
 * RVS_Init() is called may be lost or corrupt
 *
 * Typically RVS_Init() is called only once
 */
void RVS_Init(void)
{

   FILE *file_ptr;

   /* Clear the output file */

   const char *file_name = "rvs_trace.txt";

   file_ptr = fopen(file_name, "w");
   if (file_ptr == NULL)
   {
      fprintf(stderr, "Error: Could not create the trace file '%s'\n", file_name);
      exit(1);
   }
   fclose(file_ptr);
   /* Open the trace file */
   RVS_Open_Stream();

}

/**
 * Outputs RVS data. This is an optional call typically inserted into the code
 * under test as late as possible. If required, call this after ipoints are
 * written out.
 *
 * Typical uses of this are:
 *  - Upload a map
 *  - Flush a memory buffer
 *  - Disable subsequent ipoints
 *
 * Be aware that if this is required then ipoints written out after
 * RVS_Output() is called may be lost or corrupt.
 *
 * Some integrations may call RVS_Output() multiple times (the test framework
 * calls this via RVS_End_Test() once per test). Other integrations may call
 * this only once a run is complete.
 */
void RVS_Output(void)
{

   RVS_Close_Stream();

}

/**
 * Set the build ID for the instrumented source code.
 * The mechanism here varies based on whether a map or a trace is used but it
 * is typically not required to alter this from the default if using a
 * standard map or trace implementation.
 *
 * The build ID affects the entire code and should be set consistently across
 * map uploads. Note resetting the map will reset the build ID.
 *
 * @param build_id Build ID for the instrumented source code.
 */
void RVS_Build_Id(const char *build_id)
{

   unsigned int i;

   /* 7,5 = build id */
   RVS_Ipoint(7);
   RVS_Ipoint(5);

   /* 0 terminated string : build ID */
   for (i = 0; build_id[i] != 0; i++)
   {
      RVS_Ipoint((t_rvs_ipoint_id)build_id[i]);
   }
   RVS_Ipoint(0);

}

/**
 * Marks a test as 'begun'. The mechanism here varies based on whether a map
 * or a trace is used but it is typically not required to alter this from the
 * default if using a standard map or trace implementation.
 *
 * This can be called manually if performing system testing to identify
 * different sections of the run. It is called automatically by the RVS test
 * framework.
 *
 * @param test_id New test ID.
 * @param test_description Name or short description of the new test.
 */
void RVS_Begin_Test(t_rvs_test_id test_id, const char *test_description)
{

   (void)test_id;
   (void)test_description;
   RVS_Open_Stream();

}

/**
 * Marks a test as 'complete'. The mechanism here varies based on whether a
 * map or trace is used but it is typically not requried to alter this from
 * the default if using a standard map or trace implementation.
 *
 * This can be called manually if performing system testing to identify
 * different sections of the run. It is called automatically by the RVS test
 * framework.
 */
void RVS_End_Test(void)
{
   RVS_Output();
}

/**
 * Marks the transition between an existing test and a new test.
 * This call assumes a test is currently active, outputs it and starts a new
 * test.
 * It is provided as a convenience function wrapping RVS_End_Test() and
 * RVS_Begin_Test()
 *
 * @param test_id New test ID.
 * @param test_description Name or short description of the new test.
 */
void RVS_Next_Test(t_rvs_test_id test_id, const char *test_description)
{
   RVS_End_Test();
   RVS_Begin_Test(test_id, test_description);
}

/**
 * Delays for the given number of nanoseconds, to the precision possible on
 * the target hardware.
 *
 * @param nanos Number of nanoseconds to sleep for.
 */
void RVS_Calibration_Sleep(t_rvs_uint64 nanos)
{
#ifdef _WIN32
   Sleep(nanos / (1000 * 1000));
#else
   struct timespec delta;
   delta.tv_sec = nanos / 1000000000;
   delta.tv_nsec = nanos % 1000000000;

   /* If nanosleep was interrupted by something, repeat until remainder
    * depleted. Note: Does not warn if there's another error */
   while (nanosleep(&delta, &delta) == EINTR) {}
#endif
}

/**
 * Base atomic-data write of 8 bits
 *
 * @param byteVal Value to write.
 */
void RVS_Write_8(t_rvs_uint8 byteVal)
{
   RVS_Ipoint((t_rvs_ipoint_id) byteVal);
}

/**
 * Write out 16-bit packet.
 * Default implementation assumes a 32-bit data stream.
 *
 * @param word Value to write.
 */
void RVS_Write_16(t_rvs_uint16 word)
{
   RVS_Ipoint((t_rvs_ipoint_id) word);
}

/**
 * Write out 32-bit packet.
 * Default implementation assumes a 32-bit data stream.
 *
 * @param dword Value to write.
 */
void RVS_Write_32(t_rvs_uint32 dword)
{
   RVS_Ipoint((t_rvs_ipoint_id) dword);
}

/**
 * Write out 64-bit packet.
 * Default implementation assumes a 32-bit data stream.
 *
 * @param qword Value to write.
 */
void RVS_Write_64(t_rvs_uint64 qword)
{
   RVS_Write_32((t_rvs_uint32)(qword & 0xFFFFFFFFUL));
   RVS_Write_32((t_rvs_uint32)((qword >> 32) & 0xFFFFFFFFUL));
}

/**
 * Write out N-byte packet.
 * Default implementation assumes a 8-bit data stream.
 *
 * @param memory Data to write.
 * @param bytes Number of bytes represented by memory.
 */
void RVS_Write_N(const t_rvs_uint8_ptr memory, int bytes)
{
   int ix;
   for (ix = 0; ix < bytes; ix += 1)
   {
      RVS_Write_8(memory[ix]);
   }
}

/**
 * Write out null-terminated char-size string.
 * Default implementation assumes an 8-bit data stream.
 *
 * @param string String to write.
 * @param add_terminator whether to add a trailing null-byte.
 */
void RVS_Write_S(const char *string, t_rvs_boolean add_terminator)
{
   int ix;
   for (ix = 0; string[ix] != '\0'; ix++)
   {
      RVS_Write_8(string[ix]);
   }
   if (add_terminator)
   {
      RVS_Write_8('\0');
   }
}

/**
 * Write out a registration header and following elements.
 *
 * @param data Pointer to registration header object to be written.
 * @param add_elements Whether to also write data elements from the header.
 */
void RVS_Write_Header(const RVS_REGISTRATION_HEADER *data, t_rvs_boolean add_elements)
{
   unsigned int ix;
   /* Header is 4 bytes (32-bits) of data */
   /* However, first element (escape Ipoint) is always an Ipoint, not a data element */
   RVS_Ipoint(data->EscapeIpoint);
   for (ix = 1; ix < sizeof(*data); ix++)
   {
      RVS_Write_8(*((t_rvs_uint8_ptr)data + ix));
   }
   /* Header is followed by N packets of RVS_REGISTRATION_ELEMENT */
   if (add_elements)
   {
      int jx;
      for (jx = 0; jx < data->ElemCount + 1; jx++)
      {
         RVS_Write_Header_Element((const RVS_REGISTRATION_ELEMENT *)(data + 1) + jx);
      }
   }
}

/**
 * Write out a single element packet while registering a new data class
 *
 * @param data Element to write.
 */
void RVS_Write_Header_Element(const RVS_REGISTRATION_ELEMENT *data)
{
   unsigned int ix;
   /* Header element is 4 bytes (32-bits) of data */
   for (ix = 0; ix < sizeof(*data); ix++)
   {
      RVS_Write_8(*((t_rvs_uint8_ptr)data + ix));
   }
}

/**
 * Write out a header packet plus following content bytes.
 *
 * @note The header packet is not word aligned.
 * @param data Data to write.
 * @param content_bytes Number of content bytes (excludes sizeof header).
 */
void RVS_Write_Packet(const RVS_PACKET_HEADER *data, int content_bytes)
{
   unsigned int ix;
   /* Hard code packet header size
      For alignment issues, it is not good to rely on a 3-byte header not being padded by the compiler */
   enum { RVS_PACKET_HEADER_SZ = 3 };
   /* Data for Ipoint and ClassId are always separate values */
   RVS_Ipoint(data->EscapeIpoint);
   RVS_Write_8(data->EscapeType);
   RVS_Write_8(data->ClassId);
   /* Content immediately follows */
   for (ix = RVS_PACKET_HEADER_SZ; ix < (sizeof(*data) + content_bytes); ix++)
   {
      RVS_Write_8(*((t_rvs_uint8_ptr)data + ix));
   }
}

/**
 * Write out a header packet only of a preregistered user data class.
 * @param class_id Preregistered data class ID.
 * @param class_flags
 */
void RVS_Write_Escape(t_rvs_uint8 class_id, t_rvs_uint8 class_flags)
{
   /* Data for Ipoint and ClassId are always separate values */
   RVS_Ipoint(RVS_IPOINT_ESCAPE);
   RVS_Write_8(RVS_ESCAPE_USERCLASS | class_flags);
   RVS_Write_8(class_id);
}

#ifdef __cplusplus
} /* extern "C" */
#endif
