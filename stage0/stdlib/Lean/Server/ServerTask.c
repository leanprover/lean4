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
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Server_ServerTask_join___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_join___redArg___closed__0;
static lean_once_cell_t l_Lean_Server_ServerTask_join___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_join___redArg___closed__1;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
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
uint8_t lean_io_get_task_state(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__4 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__6 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__7 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__8 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__9 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__10 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__11 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__18;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__19;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__20 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "zero_lt_succ"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__21 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_asServerTask___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_instCoeTaskServerTask___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Server_instCoeTaskServerTask___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_task_get_own(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_wait(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_wait___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_wait(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = 1;
x_5 = lean_task_map(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_mapCheap___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(9u);
x_4 = 0;
x_5 = lean_task_map(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_mapCostly___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = 1;
x_6 = lean_task_bind(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_bindCheap___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_unsigned_to_nat(9u);
x_5 = 0;
x_6 = lean_task_bind(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_bindCostly___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Server_ServerTask_mapCheap___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_Server_ServerTask_bindCheap___redArg(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_join___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_join___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_join___redArg___closed__0, &l_Lean_Server_ServerTask_join___redArg___closed__0_once, _init_l_Lean_Server_ServerTask_join___redArg___closed__0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_join___redArg___closed__1, &l_Lean_Server_ServerTask_join___redArg___closed__1_once, _init_l_Lean_Server_ServerTask_join___redArg___closed__1);
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_ServerTask_join___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_join___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_join(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(9u);
x_4 = lean_io_as_task(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_asTask(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = 1;
x_6 = lean_io_map_task(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(9u);
x_5 = 0;
x_6 = lean_io_map_task(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = lean_io_bind_task(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(9u);
x_6 = 0;
x_7 = lean_io_bind_task(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(9u);
x_5 = lean_io_as_task(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_EIO_asTask___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_EIO_asTask___redArg(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_EIO_asTask(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = lean_io_map_task(x_4, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_mapTaskCheap(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(9u);
x_6 = 0;
x_7 = lean_io_map_task(x_4, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_mapTaskCostly(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_ctor_set_tag(x_4, 0);
x_7 = lean_task_pure(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_task_pure(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = lean_io_bind_task(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_bindTaskCheap(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(9u);
x_6 = 0;
x_7 = lean_io_bind_task(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_ServerTask_EIO_bindTaskCostly(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(9u);
x_5 = lean_io_as_task(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_IO_asTask___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_asTask___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_asTask(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = lean_io_map_task(x_4, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_mapTaskCheap(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(9u);
x_6 = 0;
x_7 = lean_io_map_task(x_4, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_mapTaskCostly(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_ctor_set_tag(x_4, 0);
x_7 = lean_task_pure(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_task_pure(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = lean_io_bind_task(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_bindTaskCheap(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(9u);
x_6 = 0;
x_7 = lean_io_bind_task(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_ServerTask_IO_bindTaskCostly(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = lean_io_get_task_state(x_1);
if (x_3 == 2)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_ServerTask_hasFinished___redArg(x_1);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_ServerTask_hasFinished(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Server_ServerTask_hasFinished___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Server_ServerTask_hasFinished(x_1, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__12, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__18, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22));
x_3 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__19, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19);
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__23, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__27));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__28, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__29, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__30, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__31, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__32, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__24, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__33, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__34, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__13, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__35, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__36, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__37, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__38, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__39, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__40, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40);
x_2 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__5, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__41, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41);
x_2 = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__42, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(x_1, x_3);
x_5 = lean_io_wait_any(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_waitAny___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_waitAny___redArg(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_ServerTask_waitAny(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_cancel(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_ServerTask_cancel___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_cancel(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_ServerTask_cancel(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Task_asServerTask___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Task_asServerTask___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Task_asServerTask(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
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
l_Lean_Server_ServerTask_waitAny___auto__1 = _init_l_Lean_Server_ServerTask_waitAny___auto__1();
lean_mark_persistent(l_Lean_Server_ServerTask_waitAny___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
