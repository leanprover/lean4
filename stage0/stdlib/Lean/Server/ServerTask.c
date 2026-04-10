// Lean compiler output
// Module: Lean.Server.ServerTask
// Imports: public import Init.Task public import Init.System.IO
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_io_wait_any(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_io_wait(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_io_cancel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Server_instCoeTaskServerTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instCoeTaskServerTask___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instCoeTaskServerTask___closed__0 = (const lean_object*)&l_Lean_Server_instCoeTaskServerTask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_ServerTask_join___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_ServerTask_join___redArg___closed__0 = (const lean_object*)&l_Lean_Server_ServerTask_join___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Server_ServerTask_join___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_join___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__0 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__1 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__2 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__3 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__4 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value;
static const lean_array_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__5 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__6 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__7 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__8 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__9 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__10 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__11 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__12;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__13;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__14 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__15 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__16 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Nat.zero_lt_succ"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__17 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__18;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__19;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__20 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "zero_lt_succ"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__21 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(139, 13, 209, 151, 253, 249, 15, 51)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__22 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__23;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__24;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__25 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__26 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__27 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_value;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__28;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__29;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__30;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__31;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__32;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__33;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__34;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__35;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__36;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__37;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__38;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__39;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__40;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__41;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__42;
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___auto__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask_default___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_task_pure(v_inst_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask_default(lean_object* v_00_u03b1_3_, lean_object* v_inst_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_task_pure(v_inst_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask___redArg(lean_object* v_inst_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_task_pure(v_inst_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask(lean_object* v_a_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_task_pure(v_inst_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___lam__0(lean_object* v_task_11_){
_start:
{
lean_inc_ref(v_task_11_);
return v_task_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___lam__0___boxed(lean_object* v_task_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Server_instCoeTaskServerTask___lam__0(v_task_12_);
lean_dec_ref(v_task_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask(lean_object* v_00_u03b1_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = ((lean_object*)(l_Lean_Server_instCoeTaskServerTask___closed__0));
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure___redArg(lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_task_pure(v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure(lean_object* v_00_u03b1_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_task_pure(v_x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get___redArg(lean_object* v_t_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_task_get_own(v_t_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get(lean_object* v_00_u03b1_24_, lean_object* v_t_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_task_get_own(v_t_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg(lean_object* v_t_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_io_wait(v_t_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg___boxed(lean_object* v_t_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Server_ServerTask_wait___redArg(v_t_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait(lean_object* v_00_u03b1_33_, lean_object* v_t_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_io_wait(v_t_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___boxed(lean_object* v_00_u03b1_37_, lean_object* v_t_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Server_ServerTask_wait(v_00_u03b1_37_, v_t_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object* v_f_41_, lean_object* v_t_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = 1;
v___x_45_ = lean_task_map(v_f_41_, v_t_42_, v___x_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_f_48_, lean_object* v_t_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Server_ServerTask_mapCheap___redArg(v_f_48_, v_t_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly___redArg(lean_object* v_f_51_, lean_object* v_t_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_unsigned_to_nat(9u);
v___x_54_ = 0;
v___x_55_ = lean_task_map(v_f_51_, v_t_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_f_58_, lean_object* v_t_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Server_ServerTask_mapCostly___redArg(v_f_58_, v_t_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(lean_object* v_f_61_, lean_object* v_x_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_apply_1(v_f_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object* v_t_64_, lean_object* v_f_65_){
_start:
{
lean_object* v___f_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; 
v___f_66_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_66_, 0, v_f_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = 1;
v___x_69_ = lean_task_bind(v_t_64_, v___f_66_, v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_t_72_, lean_object* v_f_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_t_72_, v_f_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object* v_t_75_, lean_object* v_f_76_){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; 
v___f_77_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_77_, 0, v_f_76_);
v___x_78_ = lean_unsigned_to_nat(9u);
v___x_79_ = 0;
v___x_80_ = lean_task_bind(v_t_75_, v___f_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_t_83_, lean_object* v_f_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Server_ServerTask_bindCostly___redArg(v_t_83_, v_f_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(lean_object* v_acc_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_array_push(v_acc_86_, v_x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(lean_object* v_a_89_, lean_object* v_acc_90_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_92_; 
v___f_91_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_91_, 0, v_acc_90_);
v___x_92_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_91_, v_a_89_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(lean_object* v_as_93_, size_t v_sz_94_, size_t v_i_95_, lean_object* v_b_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_95_, v_sz_94_);
if (v___x_97_ == 0)
{
return v_b_96_;
}
else
{
lean_object* v_a_98_; lean_object* v___f_99_; lean_object* v___x_100_; size_t v___x_101_; size_t v___x_102_; 
v_a_98_ = lean_array_uget_borrowed(v_as_93_, v_i_95_);
lean_inc(v_a_98_);
v___f_99_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1), 2, 1);
lean_closure_set(v___f_99_, 0, v_a_98_);
v___x_100_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_b_96_, v___f_99_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_95_, v___x_101_);
v_i_95_ = v___x_102_;
v_b_96_ = v___x_100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(lean_object* v_as_104_, lean_object* v_sz_105_, lean_object* v_i_106_, lean_object* v_b_107_){
_start:
{
size_t v_sz_boxed_108_; size_t v_i_boxed_109_; lean_object* v_res_110_; 
v_sz_boxed_108_ = lean_unbox_usize(v_sz_105_);
lean_dec(v_sz_105_);
v_i_boxed_109_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_104_, v_sz_boxed_108_, v_i_boxed_109_, v_b_107_);
lean_dec_ref(v_as_104_);
return v_res_110_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_join___redArg___closed__1(void){
_start:
{
lean_object* v___x_113_; lean_object* v_r_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Server_ServerTask_join___redArg___closed__0));
v_r_114_ = lean_task_pure(v___x_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg(lean_object* v_ts_115_){
_start:
{
lean_object* v_r_116_; size_t v_sz_117_; size_t v___x_118_; lean_object* v___x_119_; 
v_r_116_ = lean_obj_once(&l_Lean_Server_ServerTask_join___redArg___closed__1, &l_Lean_Server_ServerTask_join___redArg___closed__1_once, _init_l_Lean_Server_ServerTask_join___redArg___closed__1);
v_sz_117_ = lean_array_size(v_ts_115_);
v___x_118_ = ((size_t)0ULL);
v___x_119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_ts_115_, v_sz_117_, v___x_118_, v_r_116_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg___boxed(lean_object* v_ts_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Server_ServerTask_join___redArg(v_ts_120_);
lean_dec_ref(v_ts_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join(lean_object* v_00_u03b1_122_, lean_object* v_ts_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Server_ServerTask_join___redArg(v_ts_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___boxed(lean_object* v_00_u03b1_125_, lean_object* v_ts_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Server_ServerTask_join(v_00_u03b1_125_, v_ts_126_);
lean_dec_ref(v_ts_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_object* v_00_u03b1_128_, lean_object* v_as_129_, size_t v_sz_130_, size_t v_i_131_, lean_object* v_b_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_129_, v_sz_130_, v_i_131_, v_b_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(lean_object* v_00_u03b1_134_, lean_object* v_as_135_, lean_object* v_sz_136_, lean_object* v_i_137_, lean_object* v_b_138_){
_start:
{
size_t v_sz_boxed_139_; size_t v_i_boxed_140_; lean_object* v_res_141_; 
v_sz_boxed_139_ = lean_unbox_usize(v_sz_136_);
lean_dec(v_sz_136_);
v_i_boxed_140_ = lean_unbox_usize(v_i_137_);
lean_dec(v_i_137_);
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(v_00_u03b1_134_, v_as_135_, v_sz_boxed_139_, v_i_boxed_140_, v_b_138_);
lean_dec_ref(v_as_135_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object* v_act_142_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(9u);
v___x_145_ = lean_io_as_task(v_act_142_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(lean_object* v_act_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask(lean_object* v_00_u03b1_149_, lean_object* v_act_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___boxed(lean_object* v_00_u03b1_153_, lean_object* v_act_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Server_ServerTask_BaseIO_asTask(v_00_u03b1_153_, v_act_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(lean_object* v_f_157_, lean_object* v_t_158_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = 1;
v___x_162_ = lean_io_map_task(v_f_157_, v_t_158_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(lean_object* v_f_163_, lean_object* v_t_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_163_, v_t_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_f_169_, lean_object* v_t_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_169_, v_t_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_f_175_, lean_object* v_t_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(v_00_u03b1_173_, v_00_u03b2_174_, v_f_175_, v_t_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(lean_object* v_f_179_, lean_object* v_t_180_){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(9u);
v___x_183_ = 0;
v___x_184_ = lean_io_map_task(v_f_179_, v_t_180_, v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(lean_object* v_f_185_, lean_object* v_t_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_185_, v_t_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_f_191_, lean_object* v_t_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_191_, v_t_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_f_197_, lean_object* v_t_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(v_00_u03b1_195_, v_00_u03b2_196_, v_f_197_, v_t_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(lean_object* v_f_201_, lean_object* v_x_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_apply_2(v_f_201_, v_x_202_, lean_box(0));
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_205_, lean_object* v_x_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(v_f_205_, v_x_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(lean_object* v_t_209_, lean_object* v_f_210_){
_start:
{
lean_object* v___f_212_; lean_object* v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v___f_212_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_212_, 0, v_f_210_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = 1;
v___x_215_ = lean_io_bind_task(v_t_209_, v___f_212_, v___x_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(lean_object* v_t_216_, lean_object* v_f_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_216_, v_f_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_t_222_, lean_object* v_f_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_222_, v_f_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_t_228_, lean_object* v_f_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(v_00_u03b1_226_, v_00_u03b2_227_, v_t_228_, v_f_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(lean_object* v_t_232_, lean_object* v_f_233_){
_start:
{
lean_object* v___f_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; 
v___f_235_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_235_, 0, v_f_233_);
v___x_236_ = lean_unsigned_to_nat(9u);
v___x_237_ = 0;
v___x_238_ = lean_io_bind_task(v_t_232_, v___f_235_, v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(lean_object* v_t_239_, lean_object* v_f_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_239_, v_f_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_t_245_, lean_object* v_f_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_245_, v_f_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_t_251_, lean_object* v_f_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(v_00_u03b1_249_, v_00_u03b2_250_, v_t_251_, v_f_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(lean_object* v_act_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_apply_1(v_act_255_, lean_box(0));
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_a_266_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_257_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_257_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed(lean_object* v_act_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(v_act_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object* v_act_277_){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___f_279_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_279_, 0, v_act_277_);
v___x_280_ = lean_unsigned_to_nat(9u);
v___x_281_ = lean_io_as_task(v___f_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(lean_object* v_act_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask(lean_object* v_00_u03b5_285_, lean_object* v_00_u03b1_286_, lean_object* v_act_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___boxed(lean_object* v_00_u03b5_290_, lean_object* v_00_u03b1_291_, lean_object* v_act_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Server_ServerTask_EIO_asTask(v_00_u03b5_290_, v_00_u03b1_291_, v_act_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(lean_object* v_f_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_apply_2(v_f_295_, v_a_296_, lean_box(0));
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 1);
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_a_307_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_298_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_298_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 0);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_315_, lean_object* v_a_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(v_f_315_, v_a_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object* v_f_319_, lean_object* v_t_320_){
_start:
{
lean_object* v___f_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_322_, 0, v_f_319_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = 1;
v___x_325_ = lean_io_map_task(v___f_322_, v_t_320_, v___x_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(lean_object* v_f_326_, lean_object* v_t_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_326_, v_t_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b5_331_, lean_object* v_00_u03b2_332_, lean_object* v_f_333_, lean_object* v_t_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_333_, v_t_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b5_338_, lean_object* v_00_u03b2_339_, lean_object* v_f_340_, lean_object* v_t_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap(v_00_u03b1_337_, v_00_u03b5_338_, v_00_u03b2_339_, v_f_340_, v_t_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object* v_f_344_, lean_object* v_t_345_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; 
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_347_, 0, v_f_344_);
v___x_348_ = lean_unsigned_to_nat(9u);
v___x_349_ = 0;
v___x_350_ = lean_io_map_task(v___f_347_, v_t_345_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(lean_object* v_f_351_, lean_object* v_t_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_351_, v_t_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b5_356_, lean_object* v_00_u03b2_357_, lean_object* v_f_358_, lean_object* v_t_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_358_, v_t_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b5_363_, lean_object* v_00_u03b2_364_, lean_object* v_f_365_, lean_object* v_t_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly(v_00_u03b1_362_, v_00_u03b5_363_, v_00_u03b2_364_, v_f_365_, v_t_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(lean_object* v_f_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_apply_2(v_f_369_, v_a_370_, lean_box(0));
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref(v___x_372_);
return v_a_373_;
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_a_374_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_372_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = lean_task_pure(v___x_379_);
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_383_, lean_object* v_a_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(v_f_383_, v_a_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object* v_t_387_, lean_object* v_f_388_){
_start:
{
lean_object* v___f_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; 
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_390_, 0, v_f_388_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = 1;
v___x_393_ = lean_io_bind_task(v_t_387_, v___f_390_, v___x_391_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(lean_object* v_t_394_, lean_object* v_f_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_394_, v_f_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b5_399_, lean_object* v_00_u03b2_400_, lean_object* v_t_401_, lean_object* v_f_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_401_, v_f_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b5_406_, lean_object* v_00_u03b2_407_, lean_object* v_t_408_, lean_object* v_f_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap(v_00_u03b1_405_, v_00_u03b5_406_, v_00_u03b2_407_, v_t_408_, v_f_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object* v_t_412_, lean_object* v_f_413_){
_start:
{
lean_object* v___f_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_415_, 0, v_f_413_);
v___x_416_ = lean_unsigned_to_nat(9u);
v___x_417_ = 0;
v___x_418_ = lean_io_bind_task(v_t_412_, v___f_415_, v___x_416_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(lean_object* v_t_419_, lean_object* v_f_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_419_, v_f_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly(lean_object* v_00_u03b1_423_, lean_object* v_00_u03b5_424_, lean_object* v_00_u03b2_425_, lean_object* v_t_426_, lean_object* v_f_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_426_, v_f_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b5_431_, lean_object* v_00_u03b2_432_, lean_object* v_t_433_, lean_object* v_f_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly(v_00_u03b1_430_, v_00_u03b5_431_, v_00_u03b2_432_, v_t_433_, v_f_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(lean_object* v_act_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_apply_1(v_act_437_, lean_box(0));
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 1);
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_439_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed(lean_object* v_act_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(v_act_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object* v_act_459_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_461_, 0, v_act_459_);
v___x_462_ = lean_unsigned_to_nat(9u);
v___x_463_ = lean_io_as_task(v___f_461_, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(lean_object* v_act_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object* v_00_u03b1_467_, lean_object* v_act_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___boxed(lean_object* v_00_u03b1_471_, lean_object* v_act_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Server_ServerTask_IO_asTask(v_00_u03b1_471_, v_act_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(lean_object* v_f_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_apply_2(v_f_475_, v_a_476_, lean_box(0));
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 1);
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_478_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_478_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 0);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_495_, lean_object* v_a_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(v_f_495_, v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(lean_object* v_f_499_, lean_object* v_t_500_){
_start:
{
lean_object* v___f_502_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; 
v___f_502_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_502_, 0, v_f_499_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = 1;
v___x_505_ = lean_io_map_task(v___f_502_, v_t_500_, v___x_503_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(lean_object* v_f_506_, lean_object* v_t_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_506_, v_t_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_f_512_, lean_object* v_t_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_512_, v_t_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_f_518_, lean_object* v_t_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Server_ServerTask_IO_mapTaskCheap(v_00_u03b1_516_, v_00_u03b2_517_, v_f_518_, v_t_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(lean_object* v_f_522_, lean_object* v_t_523_){
_start:
{
lean_object* v___f_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; 
v___f_525_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_525_, 0, v_f_522_);
v___x_526_ = lean_unsigned_to_nat(9u);
v___x_527_ = 0;
v___x_528_ = lean_io_map_task(v___f_525_, v_t_523_, v___x_526_, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(lean_object* v_f_529_, lean_object* v_t_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_529_, v_t_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_f_535_, lean_object* v_t_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_535_, v_t_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_f_541_, lean_object* v_t_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Server_ServerTask_IO_mapTaskCostly(v_00_u03b1_539_, v_00_u03b2_540_, v_f_541_, v_t_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(lean_object* v_f_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_apply_2(v_f_545_, v_a_546_, lean_box(0));
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
return v_a_549_;
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_a_550_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v___x_548_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 0);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_task_pure(v___x_555_);
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_559_, lean_object* v_a_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(v_f_559_, v_a_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(lean_object* v_t_563_, lean_object* v_f_564_){
_start:
{
lean_object* v___f_566_; lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; 
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_566_, 0, v_f_564_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = 1;
v___x_569_ = lean_io_bind_task(v_t_563_, v___f_566_, v___x_567_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(lean_object* v_t_570_, lean_object* v_f_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_570_, v_f_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_t_576_, lean_object* v_f_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_576_, v_f_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_t_582_, lean_object* v_f_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Server_ServerTask_IO_bindTaskCheap(v_00_u03b1_580_, v_00_u03b2_581_, v_t_582_, v_f_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(lean_object* v_t_586_, lean_object* v_f_587_){
_start:
{
lean_object* v___f_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_589_, 0, v_f_587_);
v___x_590_ = lean_unsigned_to_nat(9u);
v___x_591_ = 0;
v___x_592_ = lean_io_bind_task(v_t_586_, v___f_589_, v___x_590_, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(lean_object* v_t_593_, lean_object* v_f_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_593_, v_f_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_t_599_, lean_object* v_f_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_599_, v_f_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_t_605_, lean_object* v_f_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Server_ServerTask_IO_bindTaskCostly(v_00_u03b1_603_, v_00_u03b2_604_, v_t_605_, v_f_606_);
return v_res_608_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object* v_t_609_){
_start:
{
uint8_t v___x_611_; 
v___x_611_ = lean_io_get_task_state(v_t_609_);
if (v___x_611_ == 2)
{
uint8_t v___x_612_; 
v___x_612_ = 1;
return v___x_612_;
}
else
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___redArg___boxed(lean_object* v_t_614_, lean_object* v_a_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_614_);
lean_dec_ref(v_t_614_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished(lean_object* v_00_u03b1_618_, lean_object* v_t_619_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___boxed(lean_object* v_00_u03b1_622_, lean_object* v_t_623_, lean_object* v_a_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_Lean_Server_ServerTask_hasFinished(v_00_u03b1_622_, v_t_623_);
lean_dec_ref(v_t_623_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10));
v___x_654_ = l_Lean_mkAtom(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__12, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12);
v___x_656_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_657_ = lean_array_push(v___x_656_, v___x_655_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17));
v___x_667_ = lean_string_utf8_byte_size(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__18, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17));
v___x_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_669_);
lean_ctor_set(v___x_671_, 2, v___x_668_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22));
v___x_679_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__19, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19);
v___x_680_ = lean_box(2);
v___x_681_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_678_);
lean_ctor_set(v___x_681_, 3, v___x_677_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__23, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23);
v___x_683_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_684_ = lean_array_push(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__27));
v___x_693_ = l_Lean_mkAtom(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__28, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28);
v___x_695_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_696_ = lean_array_push(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__29, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29);
v___x_698_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26));
v___x_699_ = lean_box(2);
v___x_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
lean_ctor_set(v___x_700_, 2, v___x_697_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__30, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30);
v___x_702_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_703_ = lean_array_push(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__31, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31);
v___x_705_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
v___x_706_ = lean_box(2);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
lean_ctor_set(v___x_707_, 2, v___x_704_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__32, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32);
v___x_709_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__24, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24);
v___x_710_ = lean_array_push(v___x_709_, v___x_708_);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__33, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33);
v___x_712_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16));
v___x_713_ = lean_box(2);
v___x_714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_711_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__34, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34);
v___x_716_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__13, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13);
v___x_717_ = lean_array_push(v___x_716_, v___x_715_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__35, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35);
v___x_719_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11));
v___x_720_ = lean_box(2);
v___x_721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_719_);
lean_ctor_set(v___x_721_, 2, v___x_718_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__36, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36);
v___x_723_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_724_ = lean_array_push(v___x_723_, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_725_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__37, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37);
v___x_726_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
v___x_727_ = lean_box(2);
v___x_728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_725_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__38, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38);
v___x_730_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_731_ = lean_array_push(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__39, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39);
v___x_733_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7));
v___x_734_ = lean_box(2);
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_732_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__40, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40);
v___x_737_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_738_ = lean_array_push(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_739_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__41, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41);
v___x_740_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4));
v___x_741_ = lean_box(2);
v___x_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
lean_ctor_set(v___x_742_, 2, v___x_739_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__42, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
if (lean_obj_tag(v_a_744_) == 0)
{
lean_object* v___x_746_; 
v___x_746_ = l_List_reverse___redArg(v_a_745_);
return v___x_746_;
}
else
{
lean_object* v_head_747_; lean_object* v_tail_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_head_747_ = lean_ctor_get(v_a_744_, 0);
v_tail_748_ = lean_ctor_get(v_a_744_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_744_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v_a_744_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_tail_748_);
lean_inc(v_head_747_);
lean_dec(v_a_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v_a_745_);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_head_747_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_a_745_);
v___x_753_ = v_reuseFailAlloc_755_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
v_a_744_ = v_tail_748_;
v_a_745_ = v___x_753_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object* v_tasks_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_box(0);
v___x_760_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(v_tasks_757_, v___x_759_);
v___x_761_ = lean_io_wait_any(v___x_760_);
lean_dec(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg___boxed(lean_object* v_tasks_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny(lean_object* v_00_u03b1_765_, lean_object* v_tasks_766_, lean_object* v_h_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_766_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___boxed(lean_object* v_00_u03b1_770_, lean_object* v_tasks_771_, lean_object* v_h_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Server_ServerTask_waitAny(v_00_u03b1_770_, v_tasks_771_, v_h_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(lean_object* v_00_u03b1_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(v_a_776_, v_a_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg(lean_object* v_t_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_io_cancel(v_t_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg___boxed(lean_object* v_t_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Server_ServerTask_cancel___redArg(v_t_782_);
lean_dec_ref(v_t_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel(lean_object* v_00_u03b1_785_, lean_object* v_t_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_io_cancel(v_t_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___boxed(lean_object* v_00_u03b1_789_, lean_object* v_t_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Server_ServerTask_cancel(v_00_u03b1_789_, v_t_790_);
lean_dec_ref(v_t_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg(lean_object* v_t_793_){
_start:
{
lean_inc_ref(v_t_793_);
return v_t_793_;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg___boxed(lean_object* v_t_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Task_asServerTask___redArg(v_t_794_);
lean_dec_ref(v_t_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask(lean_object* v_00_u03b1_796_, lean_object* v_t_797_){
_start:
{
lean_inc_ref(v_t_797_);
return v_t_797_;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask___boxed(lean_object* v_00_u03b1_798_, lean_object* v_t_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Task_asServerTask(v_00_u03b1_798_, v_t_799_);
lean_dec_ref(v_t_799_);
return v_res_800_;
}
}
lean_object* runtime_initialize_Init_Task(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_ServerTask(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Server_ServerTask_waitAny___auto__1 = _init_l_Lean_Server_ServerTask_waitAny___auto__1();
lean_mark_persistent(l_Lean_Server_ServerTask_waitAny___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Task(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_ServerTask(builtin);
}
#ifdef __cplusplus
}
#endif
