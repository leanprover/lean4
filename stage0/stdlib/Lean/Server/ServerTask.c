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
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Server_instCoeTaskServerTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instCoeTaskServerTask___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instCoeTaskServerTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg();
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___lam__0(lean_object* v_task_11_){
_start:
{
lean_inc_ref(v_task_11_);
return v_task_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___lam__0___boxed(lean_object* v_task_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Server_instCoeTaskServerTask___redArg___lam__0(v_task_12_);
lean_dec_ref(v_task_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg(){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = ((lean_object*)(l_Lean_Server_instCoeTaskServerTask___redArg___closed__0));
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Server_instCoeTaskServerTask___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask(lean_object* v_00_u03b1_19_){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = ((lean_object*)(l_Lean_Server_instCoeTaskServerTask___redArg___closed__0));
return v___f_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure___redArg(lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_task_pure(v_x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure(lean_object* v_00_u03b1_23_, lean_object* v_x_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_task_pure(v_x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get___redArg(lean_object* v_t_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_task_get_own(v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get(lean_object* v_00_u03b1_28_, lean_object* v_t_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_task_get_own(v_t_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg(lean_object* v_t_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_io_wait(v_t_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg___boxed(lean_object* v_t_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Server_ServerTask_wait___redArg(v_t_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait(lean_object* v_00_u03b1_37_, lean_object* v_t_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_io_wait(v_t_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___boxed(lean_object* v_00_u03b1_41_, lean_object* v_t_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Server_ServerTask_wait(v_00_u03b1_41_, v_t_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object* v_f_45_, lean_object* v_t_46_){
_start:
{
lean_object* v___x_47_; uint8_t v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = 1;
v___x_49_ = lean_task_map(v_f_45_, v_t_46_, v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_f_52_, lean_object* v_t_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Server_ServerTask_mapCheap___redArg(v_f_52_, v_t_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly___redArg(lean_object* v_f_55_, lean_object* v_t_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_unsigned_to_nat(9u);
v___x_58_ = 0;
v___x_59_ = lean_task_map(v_f_55_, v_t_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_, lean_object* v_f_62_, lean_object* v_t_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Server_ServerTask_mapCostly___redArg(v_f_62_, v_t_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(lean_object* v_f_65_, lean_object* v_x_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_1(v_f_65_, v_x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object* v_t_68_, lean_object* v_f_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; 
v___f_70_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_70_, 0, v_f_69_);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = 1;
v___x_73_ = lean_task_bind(v_t_68_, v___f_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_t_76_, lean_object* v_f_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_t_76_, v_f_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object* v_t_79_, lean_object* v_f_80_){
_start:
{
lean_object* v___f_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; 
v___f_81_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_81_, 0, v_f_80_);
v___x_82_ = lean_unsigned_to_nat(9u);
v___x_83_ = 0;
v___x_84_ = lean_task_bind(v_t_79_, v___f_81_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_t_87_, lean_object* v_f_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Server_ServerTask_bindCostly___redArg(v_t_87_, v_f_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(lean_object* v_acc_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_array_push(v_acc_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(lean_object* v_a_93_, lean_object* v_acc_94_){
_start:
{
lean_object* v___f_95_; lean_object* v___x_96_; 
v___f_95_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_95_, 0, v_acc_94_);
v___x_96_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_95_, v_a_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(lean_object* v_as_97_, size_t v_sz_98_, size_t v_i_99_, lean_object* v_b_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_lt(v_i_99_, v_sz_98_);
if (v___x_101_ == 0)
{
return v_b_100_;
}
else
{
lean_object* v_a_102_; lean_object* v___f_103_; lean_object* v___x_104_; size_t v___x_105_; size_t v___x_106_; 
v_a_102_ = lean_array_uget_borrowed(v_as_97_, v_i_99_);
lean_inc(v_a_102_);
v___f_103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1), 2, 1);
lean_closure_set(v___f_103_, 0, v_a_102_);
v___x_104_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_b_100_, v___f_103_);
v___x_105_ = ((size_t)1ULL);
v___x_106_ = lean_usize_add(v_i_99_, v___x_105_);
v_i_99_ = v___x_106_;
v_b_100_ = v___x_104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(lean_object* v_as_108_, lean_object* v_sz_109_, lean_object* v_i_110_, lean_object* v_b_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_109_);
lean_dec(v_sz_109_);
v_i_boxed_113_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_108_, v_sz_boxed_112_, v_i_boxed_113_, v_b_111_);
lean_dec_ref(v_as_108_);
return v_res_114_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_join___redArg___closed__1(void){
_start:
{
lean_object* v___x_117_; lean_object* v_r_118_; 
v___x_117_ = ((lean_object*)(l_Lean_Server_ServerTask_join___redArg___closed__0));
v_r_118_ = lean_task_pure(v___x_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg(lean_object* v_ts_119_){
_start:
{
lean_object* v_r_120_; size_t v_sz_121_; size_t v___x_122_; lean_object* v___x_123_; 
v_r_120_ = lean_obj_once(&l_Lean_Server_ServerTask_join___redArg___closed__1, &l_Lean_Server_ServerTask_join___redArg___closed__1_once, _init_l_Lean_Server_ServerTask_join___redArg___closed__1);
v_sz_121_ = lean_array_size(v_ts_119_);
v___x_122_ = ((size_t)0ULL);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_ts_119_, v_sz_121_, v___x_122_, v_r_120_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg___boxed(lean_object* v_ts_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Server_ServerTask_join___redArg(v_ts_124_);
lean_dec_ref(v_ts_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join(lean_object* v_00_u03b1_126_, lean_object* v_ts_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Server_ServerTask_join___redArg(v_ts_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___boxed(lean_object* v_00_u03b1_129_, lean_object* v_ts_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Server_ServerTask_join(v_00_u03b1_129_, v_ts_130_);
lean_dec_ref(v_ts_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_object* v_00_u03b1_132_, lean_object* v_as_133_, size_t v_sz_134_, size_t v_i_135_, lean_object* v_b_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_133_, v_sz_134_, v_i_135_, v_b_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(lean_object* v_00_u03b1_138_, lean_object* v_as_139_, lean_object* v_sz_140_, lean_object* v_i_141_, lean_object* v_b_142_){
_start:
{
size_t v_sz_boxed_143_; size_t v_i_boxed_144_; lean_object* v_res_145_; 
v_sz_boxed_143_ = lean_unbox_usize(v_sz_140_);
lean_dec(v_sz_140_);
v_i_boxed_144_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_res_145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(v_00_u03b1_138_, v_as_139_, v_sz_boxed_143_, v_i_boxed_144_, v_b_142_);
lean_dec_ref(v_as_139_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object* v_act_146_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(9u);
v___x_149_ = lean_io_as_task(v_act_146_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(lean_object* v_act_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask(lean_object* v_00_u03b1_153_, lean_object* v_act_154_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___boxed(lean_object* v_00_u03b1_157_, lean_object* v_act_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Server_ServerTask_BaseIO_asTask(v_00_u03b1_157_, v_act_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(lean_object* v_f_161_, lean_object* v_t_162_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = 1;
v___x_166_ = lean_io_map_task(v_f_161_, v_t_162_, v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(lean_object* v_f_167_, lean_object* v_t_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_167_, v_t_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_f_173_, lean_object* v_t_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_173_, v_t_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_f_179_, lean_object* v_t_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(v_00_u03b1_177_, v_00_u03b2_178_, v_f_179_, v_t_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(lean_object* v_f_183_, lean_object* v_t_184_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(9u);
v___x_187_ = 0;
v___x_188_ = lean_io_map_task(v_f_183_, v_t_184_, v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(lean_object* v_f_189_, lean_object* v_t_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_189_, v_t_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_f_195_, lean_object* v_t_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_195_, v_t_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_f_201_, lean_object* v_t_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(v_00_u03b1_199_, v_00_u03b2_200_, v_f_201_, v_t_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(lean_object* v_f_205_, lean_object* v_x_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_apply_2(v_f_205_, v_x_206_, lean_box(0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_209_, lean_object* v_x_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(v_f_209_, v_x_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(lean_object* v_t_213_, lean_object* v_f_214_){
_start:
{
lean_object* v___f_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; 
v___f_216_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_216_, 0, v_f_214_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = 1;
v___x_219_ = lean_io_bind_task(v_t_213_, v___f_216_, v___x_217_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(lean_object* v_t_220_, lean_object* v_f_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_220_, v_f_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_t_226_, lean_object* v_f_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_226_, v_f_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_t_232_, lean_object* v_f_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(v_00_u03b1_230_, v_00_u03b2_231_, v_t_232_, v_f_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(lean_object* v_t_236_, lean_object* v_f_237_){
_start:
{
lean_object* v___f_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
v___f_239_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_239_, 0, v_f_237_);
v___x_240_ = lean_unsigned_to_nat(9u);
v___x_241_ = 0;
v___x_242_ = lean_io_bind_task(v_t_236_, v___f_239_, v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(lean_object* v_t_243_, lean_object* v_f_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_243_, v_f_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_t_249_, lean_object* v_f_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_249_, v_f_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_t_255_, lean_object* v_f_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(v_00_u03b1_253_, v_00_u03b2_254_, v_t_255_, v_f_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(lean_object* v_act_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_apply_1(v_act_259_, lean_box(0));
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 1);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_a_270_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_261_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_261_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed(lean_object* v_act_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(v_act_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object* v_act_281_){
_start:
{
lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___f_283_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_283_, 0, v_act_281_);
v___x_284_ = lean_unsigned_to_nat(9u);
v___x_285_ = lean_io_as_task(v___f_283_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(lean_object* v_act_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask(lean_object* v_00_u03b5_289_, lean_object* v_00_u03b1_290_, lean_object* v_act_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___boxed(lean_object* v_00_u03b5_294_, lean_object* v_00_u03b1_295_, lean_object* v_act_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Server_ServerTask_EIO_asTask(v_00_u03b5_294_, v_00_u03b1_295_, v_act_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(lean_object* v_f_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_apply_2(v_f_299_, v_a_300_, lean_box(0));
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_a_311_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_302_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 0);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_319_, lean_object* v_a_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(v_f_319_, v_a_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object* v_f_323_, lean_object* v_t_324_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; 
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_326_, 0, v_f_323_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = 1;
v___x_329_ = lean_io_map_task(v___f_326_, v_t_324_, v___x_327_, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(lean_object* v_f_330_, lean_object* v_t_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_330_, v_t_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b5_335_, lean_object* v_00_u03b2_336_, lean_object* v_f_337_, lean_object* v_t_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_337_, v_t_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b5_342_, lean_object* v_00_u03b2_343_, lean_object* v_f_344_, lean_object* v_t_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap(v_00_u03b1_341_, v_00_u03b5_342_, v_00_u03b2_343_, v_f_344_, v_t_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object* v_f_348_, lean_object* v_t_349_){
_start:
{
lean_object* v___f_351_; lean_object* v___x_352_; uint8_t v___x_353_; lean_object* v___x_354_; 
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_351_, 0, v_f_348_);
v___x_352_ = lean_unsigned_to_nat(9u);
v___x_353_ = 0;
v___x_354_ = lean_io_map_task(v___f_351_, v_t_349_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(lean_object* v_f_355_, lean_object* v_t_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_355_, v_t_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b5_360_, lean_object* v_00_u03b2_361_, lean_object* v_f_362_, lean_object* v_t_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_362_, v_t_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b5_367_, lean_object* v_00_u03b2_368_, lean_object* v_f_369_, lean_object* v_t_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly(v_00_u03b1_366_, v_00_u03b5_367_, v_00_u03b2_368_, v_f_369_, v_t_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(lean_object* v_f_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_apply_2(v_f_373_, v_a_374_, lean_box(0));
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
return v_a_377_;
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_a_378_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v___x_376_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_376_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_385_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; 
v___x_384_ = lean_task_pure(v___x_383_);
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_387_, lean_object* v_a_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(v_f_387_, v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object* v_t_391_, lean_object* v_f_392_){
_start:
{
lean_object* v___f_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; 
v___f_394_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_394_, 0, v_f_392_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = 1;
v___x_397_ = lean_io_bind_task(v_t_391_, v___f_394_, v___x_395_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(lean_object* v_t_398_, lean_object* v_f_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_398_, v_f_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap(lean_object* v_00_u03b1_402_, lean_object* v_00_u03b5_403_, lean_object* v_00_u03b2_404_, lean_object* v_t_405_, lean_object* v_f_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_405_, v_f_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b5_410_, lean_object* v_00_u03b2_411_, lean_object* v_t_412_, lean_object* v_f_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap(v_00_u03b1_409_, v_00_u03b5_410_, v_00_u03b2_411_, v_t_412_, v_f_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object* v_t_416_, lean_object* v_f_417_){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_419_, 0, v_f_417_);
v___x_420_ = lean_unsigned_to_nat(9u);
v___x_421_ = 0;
v___x_422_ = lean_io_bind_task(v_t_416_, v___f_419_, v___x_420_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(lean_object* v_t_423_, lean_object* v_f_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_423_, v_f_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b5_428_, lean_object* v_00_u03b2_429_, lean_object* v_t_430_, lean_object* v_f_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_430_, v_f_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(lean_object* v_00_u03b1_434_, lean_object* v_00_u03b5_435_, lean_object* v_00_u03b2_436_, lean_object* v_t_437_, lean_object* v_f_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly(v_00_u03b1_434_, v_00_u03b5_435_, v_00_u03b2_436_, v_t_437_, v_f_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(lean_object* v_act_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_apply_1(v_act_441_, lean_box(0));
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_443_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_443_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 0);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed(lean_object* v_act_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(v_act_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object* v_act_463_){
_start:
{
lean_object* v___f_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___f_465_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_465_, 0, v_act_463_);
v___x_466_ = lean_unsigned_to_nat(9u);
v___x_467_ = lean_io_as_task(v___f_465_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(lean_object* v_act_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object* v_00_u03b1_471_, lean_object* v_act_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___boxed(lean_object* v_00_u03b1_475_, lean_object* v_act_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Server_ServerTask_IO_asTask(v_00_u03b1_475_, v_act_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(lean_object* v_f_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_apply_2(v_f_479_, v_a_480_, lean_box(0));
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_482_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_482_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 0);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_499_, lean_object* v_a_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(v_f_499_, v_a_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(lean_object* v_f_503_, lean_object* v_t_504_){
_start:
{
lean_object* v___f_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; 
v___f_506_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_506_, 0, v_f_503_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = 1;
v___x_509_ = lean_io_map_task(v___f_506_, v_t_504_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(lean_object* v_f_510_, lean_object* v_t_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_510_, v_t_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_f_516_, lean_object* v_t_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_516_, v_t_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_f_522_, lean_object* v_t_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Server_ServerTask_IO_mapTaskCheap(v_00_u03b1_520_, v_00_u03b2_521_, v_f_522_, v_t_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(lean_object* v_f_526_, lean_object* v_t_527_){
_start:
{
lean_object* v___f_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; 
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_529_, 0, v_f_526_);
v___x_530_ = lean_unsigned_to_nat(9u);
v___x_531_ = 0;
v___x_532_ = lean_io_map_task(v___f_529_, v_t_527_, v___x_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(lean_object* v_f_533_, lean_object* v_t_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_533_, v_t_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_f_539_, lean_object* v_t_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_539_, v_t_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_f_545_, lean_object* v_t_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Server_ServerTask_IO_mapTaskCostly(v_00_u03b1_543_, v_00_u03b2_544_, v_f_545_, v_t_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(lean_object* v_f_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_apply_2(v_f_549_, v_a_550_, lean_box(0));
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
return v_a_553_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_a_554_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_task_pure(v___x_559_);
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_563_, lean_object* v_a_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(v_f_563_, v_a_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(lean_object* v_t_567_, lean_object* v_f_568_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; 
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_570_, 0, v_f_568_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = 1;
v___x_573_ = lean_io_bind_task(v_t_567_, v___f_570_, v___x_571_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(lean_object* v_t_574_, lean_object* v_f_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_574_, v_f_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_t_580_, lean_object* v_f_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_580_, v_f_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_t_586_, lean_object* v_f_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Server_ServerTask_IO_bindTaskCheap(v_00_u03b1_584_, v_00_u03b2_585_, v_t_586_, v_f_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(lean_object* v_t_590_, lean_object* v_f_591_){
_start:
{
lean_object* v___f_593_; lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; 
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_593_, 0, v_f_591_);
v___x_594_ = lean_unsigned_to_nat(9u);
v___x_595_ = 0;
v___x_596_ = lean_io_bind_task(v_t_590_, v___f_593_, v___x_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(lean_object* v_t_597_, lean_object* v_f_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_597_, v_f_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_t_603_, lean_object* v_f_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_603_, v_f_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v_t_609_, lean_object* v_f_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Server_ServerTask_IO_bindTaskCostly(v_00_u03b1_607_, v_00_u03b2_608_, v_t_609_, v_f_610_);
return v_res_612_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object* v_t_613_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = lean_io_get_task_state(v_t_613_);
if (v___x_615_ == 2)
{
uint8_t v___x_616_; 
v___x_616_ = 1;
return v___x_616_;
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___redArg___boxed(lean_object* v_t_618_, lean_object* v_a_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_618_);
lean_dec_ref(v_t_618_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished(lean_object* v_00_u03b1_622_, lean_object* v_t_623_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___boxed(lean_object* v_00_u03b1_626_, lean_object* v_t_627_, lean_object* v_a_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Lean_Server_ServerTask_hasFinished(v_00_u03b1_626_, v_t_627_);
lean_dec_ref(v_t_627_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10));
v___x_658_ = l_Lean_mkAtom(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__12, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12);
v___x_660_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_661_ = lean_array_push(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17));
v___x_671_ = lean_string_utf8_byte_size(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__18, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17));
v___x_675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
lean_ctor_set(v___x_675_, 2, v___x_672_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_681_ = lean_box(0);
v___x_682_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22));
v___x_683_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__19, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19);
v___x_684_ = lean_box(2);
v___x_685_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_682_);
lean_ctor_set(v___x_685_, 3, v___x_681_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__23, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23);
v___x_687_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_688_ = lean_array_push(v___x_687_, v___x_686_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__27));
v___x_697_ = l_Lean_mkAtom(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__28, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28);
v___x_699_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_700_ = lean_array_push(v___x_699_, v___x_698_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__29, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29);
v___x_702_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26));
v___x_703_ = lean_box(2);
v___x_704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
lean_ctor_set(v___x_704_, 2, v___x_701_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__30, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30);
v___x_706_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_707_ = lean_array_push(v___x_706_, v___x_705_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__31, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31);
v___x_709_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
v___x_710_ = lean_box(2);
v___x_711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_708_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__32, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32);
v___x_713_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__24, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24);
v___x_714_ = lean_array_push(v___x_713_, v___x_712_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_715_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__33, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33);
v___x_716_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16));
v___x_717_ = lean_box(2);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_715_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__34, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34);
v___x_720_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__13, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13);
v___x_721_ = lean_array_push(v___x_720_, v___x_719_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_722_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__35, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35);
v___x_723_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11));
v___x_724_ = lean_box(2);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_722_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__36, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36);
v___x_727_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_728_ = lean_array_push(v___x_727_, v___x_726_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__37, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37);
v___x_730_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
v___x_731_ = lean_box(2);
v___x_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_729_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__38, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38);
v___x_734_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_735_ = lean_array_push(v___x_734_, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__39, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39);
v___x_737_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7));
v___x_738_ = lean_box(2);
v___x_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
lean_ctor_set(v___x_739_, 2, v___x_736_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__40, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40);
v___x_741_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_742_ = lean_array_push(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__41, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41);
v___x_744_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4));
v___x_745_ = lean_box(2);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__42, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
if (lean_obj_tag(v_a_748_) == 0)
{
lean_object* v___x_750_; 
v___x_750_ = l_List_reverse___redArg(v_a_749_);
return v___x_750_;
}
else
{
lean_object* v_head_751_; lean_object* v_tail_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_head_751_ = lean_ctor_get(v_a_748_, 0);
v_tail_752_ = lean_ctor_get(v_a_748_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v_a_748_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_tail_752_);
lean_inc(v_head_751_);
lean_dec(v_a_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_a_749_);
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_head_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_749_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
v_a_748_ = v_tail_752_;
v_a_749_ = v___x_757_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object* v_tasks_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(v_tasks_761_, v___x_763_);
v___x_765_ = lean_io_wait_any(v___x_764_);
lean_dec(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg___boxed(lean_object* v_tasks_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny(lean_object* v_00_u03b1_769_, lean_object* v_tasks_770_, lean_object* v_h_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_770_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___boxed(lean_object* v_00_u03b1_774_, lean_object* v_tasks_775_, lean_object* v_h_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Server_ServerTask_waitAny(v_00_u03b1_774_, v_tasks_775_, v_h_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(lean_object* v_00_u03b1_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(v_a_780_, v_a_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg(lean_object* v_t_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_io_cancel(v_t_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg___boxed(lean_object* v_t_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Server_ServerTask_cancel___redArg(v_t_786_);
lean_dec_ref(v_t_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel(lean_object* v_00_u03b1_789_, lean_object* v_t_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_io_cancel(v_t_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___boxed(lean_object* v_00_u03b1_793_, lean_object* v_t_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Server_ServerTask_cancel(v_00_u03b1_793_, v_t_794_);
lean_dec_ref(v_t_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___redArg(lean_object* v_t_797_){
_start:
{
lean_inc_ref(v_t_797_);
return v_t_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___redArg___boxed(lean_object* v_t_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Task_asServerTask___redArg(v_t_798_);
lean_dec_ref(v_t_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask(lean_object* v_00_u03b1_800_, lean_object* v_t_801_){
_start:
{
lean_inc_ref(v_t_801_);
return v_t_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___boxed(lean_object* v_00_u03b1_802_, lean_object* v_t_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Task_asServerTask(v_00_u03b1_802_, v_t_803_);
lean_dec_ref(v_t_803_);
return v_res_804_;
}
}
lean_object* runtime_initialize_Init_Task(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
