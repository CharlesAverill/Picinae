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
#ifndef __RVS_H__
#define __RVS_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "rvs_types.h"

/* RVS_Init: Initialise the instrumentation library */
void RVS_Init(void);

/* RVS_Output: Output the current coverage data */
void RVS_Output(void);

/* RVS_Build_Id: Set the build id for the instrumented source code */
void RVS_Build_Id(const char *build_id);

/* RVS_Begin_Test: Set the start of a new test */
void RVS_Begin_Test(t_rvs_test_id test_id, const char *test_description);
void RVS_Next_Test(t_rvs_test_id test_id, const char *test_description);
void RVS_End_Test(void);

void RVS_Calibration_Sleep(t_rvs_uint64 nanos);

void RVS_Close_Stream(void);

/*
 * Available known packet types
 * Used in RVS_REGISTRATION_ELEMENT.TypeId[Lo|Hi]
 */
typedef enum {
   RVS_PTYPE_NULL                   = 0x0000,  /* Reserved null packet type */
   RVS_PTYPE_IPOINT                 = 0x0001,  /* Explicit use of Ipoint in the data */
   RVS_PTYPE_TIMESTAMP              = 0x0002,  /* Time stamp data */
   RVS_PTYPE_BUILD_ID               = 0x0005,  /* Set build ID */

   RVS_PTYPE_ASSERT_BITS            = 0x0010,  /* RapiTest 32-bit assert data */
   RVS_PTYPE_ASSERT_HEAD            = 0x0011,  /* RapiTest 48-bit (12 byte) assert header */
   RVS_PTYPE_ASSERT_CELL            = 0x0012,  /* RapiTest 48-bit (12 byte) assert instance data */
   RVS_PTYPE_ASSERT_DYNHEAD         = 0x0013,  /* RapiTest 48-bit (12 byte) assert dynamic capture */
   RVS_PTYPE_ASSERT_DYNDATA         = 0x0014,  /* RapiTest assert dynamic data block */
   RVS_PTYPE_ASSERT_ALLOC           = 0x0015,  /* RapiTest 64-bit (8 byte) assert allocation mapping */

   RVS_PTYPE_DATA_PACKET            = 0x0020,  /* Observation mode data packet */

   RVS_PTYPE_START_VIRTUAL_TASK     = 0x0030,  /* New dataset ID registration */
   RVS_PTYPE_END_VIRTUAL_TASK       = 0x0031,  /* New dataset core registration (N cores per dataset) */
   RVS_PTYPE_DATASET_GROUP          = 0x0032,  /* New dataset metric group association */
   /*RVS_PTYPE_BUILD_ID               = 0x0033,*/
   RVS_PTYPE_CORE_ID                = 0x0035,
   RVS_PTYPE_RAW_MAP                = 0x0038,
   RVS_PTYPE_LOG_ERROR              = 0x0039,
   RVS_PTYPE_LOG_WARNING            = 0x003A,
   RVS_PTYPE_LOG_INFO               = 0x003B,
   RVS_PTYPE_JOB_COLOR              = 0x003C,
   RVS_PTYPE_TEST_ID                = 0x003D,
   RVS_PTYPE_SEQUENCE_CHECKPOINT    = 0x003E,  /* deprecated */
   RVS_PTYPE_METRIC_ASSERTION       = 0x003F,
   RVS_PTYPE_SEQUENCE_REFS          = 0x0040,
   RVS_PTYPE_SEQUENCE_GUARDS        = 0x0041,

   /* Up to RVS_PTYPE_USER_BASE reserved for RVS */
   RVS_PTYPE_USER_BASE              = 0x0100 /* User-defined events */
} RVS_PACKET_TYPE;

enum
{
   RVS_IPOINT_ESCAPE    = 0x07, /* Master escape Ipoint */
   RVS_ESCAPE_USERDEF   = 0xFE, /* User definition of a class */
   RVS_ESCAPE_USERCLASS = 0x80  /* User-defined Ipoint class */
};

/*
 * Given the number of elements in a registration packet, this provides
 * a byte-size required for a char (byte) array large enough to populate that data
 *
 * For example:
 *   -- Provides a packet of data that will capture a 'traditional' Ipoint pair of ident+timestamp
 *   -- The Ipoint is 16-bits (2 bytes) and the timestamp is 64-bits (8 bytes)
 *   const char packet_header[RVS_REGISTRATION_SIZE(2)] = {
 *       RVS_REGISTRATION_HEADER(17, 2),               -- ClassId is 17, 2 elements
 *       RVS_REGISTRATION_ELEMENT(RVS_PTYPE_IPOINT,    RVS_ELEMENT_F_BYTESLN2(1)),
 *       RVS_REGISTRATION_ELEMENT(RVS_PTYPE_TIMESTAMP, RVS_ELEMENT_F_BYTESLN2(3))
 *   };
 */
#define RVS_REGISTRATION_SIZE(Elements) (sizeof(RVS_REGISTRATION_HEADER) + (Elements) * sizeof(RVS_REGISTRATION_ELEMENT))
/*
 * Array definitions for packet header and elements, see RVS_REGISTRATION_SIZE()
 */
#define RVS_REGISTRATION_HEADER(ClassId, Elements) RVS_IPOINT_ESCAPE, RVS_ESCAPE_USERDEF, (ClassId), ((Elements) - 1)
#define RVS_REGISTRATION_ELEMENT(TypeId, Flags)    ((TypeId) & 0xFF), ((TypeId) >> 8), ((Flags) & 0xFF), ((Flags) >> 8)

/*
 * Flag definitions for packet elements, see RVS_REGISTRATION_ELEMENT() and RVS_REGISTRATION_SIZE()
 */
#define RVS_ELEMENT_F_BYTESLN2(Ln2Val) (Ln2Val)  /* Provide the number of bytes ln2, so 0=1, 1=2, 2=4, 3=8... 0-7 (128byte max) */
#define RVS_ELEMENT_F_STRING           0x10      /* If this flag is set, look for a null terminator. The Ln2 bytes is padding alignment. */
#define RVS_ELEMENT_F_BYTES_1          0x0       /* Metric is the same size as the output stream - we only need one packet for it */
#define RVS_ELEMENT_F_BYTES_2          0x1       /* Metric is output across two values */
#define RVS_ELEMENT_F_BYTES_4          0x2       /* Metric is output across four values */
#define RVS_ELEMENT_F_BYTES_8          0x3       /* Metric is output across eight values */
#define RVS_ELEMENT_F_DYNAMIC          0x20      /* Packet has a dynamic size - size -> data */

/*
 * Flag definitions for the amount to shift by, should be ORed with the RVS_ELEMENT_F value to create the flag byte.
 */
#define RVS_ELEMENT_S_8  0x00
#define RVS_ELEMENT_S_16 0x40
#define RVS_ELEMENT_S_32 0x80

/*
 * Registration packet data header
 * Provides information about the contents of 'rich' trace data that can be bound
 * to Ipoints - see RVS_REGISTRATION_HEADER()
 */
typedef struct _RVS_REGISTRATION_HEADER
{
   t_rvs_uint8 EscapeIpoint; /* RVS_IPOINT_ESCAPE */
   t_rvs_uint8 EscapeType;   /* RVS_ESCAPE_USERDEF */
   t_rvs_uint8 ClassId;      /* Class to register, 0x00-0xFD */
   t_rvs_uint8 ElemCount;    /* Elements to follow - 1 */
} RVS_REGISTRATION_HEADER;

/*
 * Registration packet data element
 * Provides information about the contents of 'rich' trace data that can be bound
 * to Ipoints - see RVS_REGISTRATION_ELEMENT()
 */
typedef struct _RVS_REGISTRATION_ELEMENT
{
   t_rvs_uint8 TypeIdLo;     /* Bottom 8 bits of type ID - see RVS_PACKET_TYPE enum */
   t_rvs_uint8 TypeIdHi;     /* Top 8 bits of type ID    - see RVS_PACKET_TYPE enum */
   t_rvs_uint8 FlagsLo;      /* Bottom 8 bits of flags   - see RVS_ELEMENT_F_... defines */
   t_rvs_uint8 FlagsHi;      /* Top 8 bits of type ID    - see RVS_ELEMENT_F_... defines */
} RVS_REGISTRATION_ELEMENT;

/*
 * Registration packet data header
 * Provides information about the contents of 'rich' trace data that can be bound
 * to Ipoints - see RVS_REGISTRATION_HEADER()
 */
typedef struct _RVS_PACKET_HEADER
{
   t_rvs_uint8 EscapeIpoint; /* RVS_IPOINT_ESCAPE */
   t_rvs_uint8 EscapeType;   /* RVS_ESCAPE_USERCLASS */
   t_rvs_uint8 ClassId;      /* Class identifier previously registered */
   /* Remaining data is packet captires from registered elements */
} RVS_PACKET_HEADER;

/*
 * Low level capture routines for dynamic packet uploads
 */
void RVS_Write_8(t_rvs_uint8 byteVal);
void RVS_Write_16(t_rvs_uint16 word);
void RVS_Write_32(t_rvs_uint32 dword);
void RVS_Write_64(t_rvs_uint64 qword);
void RVS_Write_N(const t_rvs_uint8_ptr memory, int bytes);
void RVS_Write_S(const char *string, t_rvs_boolean add_terminator);
void RVS_Write_32_Chunked(t_rvs_uint32 val);
void RVS_Write_16_Chunked(t_rvs_uint16 val);

/*
  More complete packet uploads
*/
void RVS_Write_Header(const RVS_REGISTRATION_HEADER *data, t_rvs_boolean add_elements);
void RVS_Write_Escape(t_rvs_uint8 class_id, t_rvs_uint8 class_flags);
void RVS_Write_Header_Element(const RVS_REGISTRATION_ELEMENT *data);
void RVS_Write_Packet(const RVS_PACKET_HEADER *data, int content_bytes); /* content_bytes excludes sizeof header */

#ifdef __cplusplus
}
#endif

#endif
