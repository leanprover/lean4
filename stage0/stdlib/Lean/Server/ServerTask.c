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
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__18 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__19 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "zero_lt_succ"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__20 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(139, 13, 209, 151, 253, 249, 15, 51)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__21 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_value),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__22 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__23;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__24 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_value;
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value_aux_0),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value_aux_1),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value_aux_2),((lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__25 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value;
static const lean_string_object l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__26 = (const lean_object*)&l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value;
static lean_once_cell_t l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_ServerTask_waitAny___auto__1___closed__27;
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
lean_object* l_Lean_Server_instCoeTaskServerTask___redArg(){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = ((lean_object*)(l_Lean_Server_instCoeTaskServerTask___redArg___closed__0));
return v___f_16_;
}
}
LEAN_EXPORT void l_Lean_Server_instCoeTaskServerTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_17_;
v_res_17_ = l_Lean_Server_instCoeTaskServerTask___redArg();
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask___redArg___boxed(lean_object* v___dummy_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Server_instCoeTaskServerTask___redArg();
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeTaskServerTask(lean_object* v_00_u03b1_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = ((lean_object*)(l_Lean_Server_instCoeTaskServerTask___redArg___closed__0));
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure___redArg(lean_object* v_x_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_task_pure(v_x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_pure(lean_object* v_00_u03b1_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_task_pure(v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get___redArg(lean_object* v_t_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_task_get_own(v_t_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_get(lean_object* v_00_u03b1_29_, lean_object* v_t_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_task_get_own(v_t_30_);
return v___x_31_;
}
}
lean_object* l_Lean_Server_ServerTask_wait___redArg(lean_object* v_t_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_io_wait(v_t_32_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_wait___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_32_ = stack[0].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_Lean_Server_ServerTask_wait___redArg(v_t_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___redArg___boxed(lean_object* v_t_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Server_ServerTask_wait___redArg(v_t_36_);
return v_res_38_;
}
}
lean_object* l_Lean_Server_ServerTask_wait(lean_object* v_00_u03b1_39_, lean_object* v_t_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_io_wait(v_t_40_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_40_ = stack[1].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_Server_ServerTask_wait(lean_box(0), v_t_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_wait___boxed(lean_object* v_00_u03b1_44_, lean_object* v_t_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Server_ServerTask_wait(v_00_u03b1_44_, v_t_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object* v_f_48_, lean_object* v_t_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = 1;
v___x_52_ = lean_task_map(v_f_48_, v_t_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCheap(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_f_55_, lean_object* v_t_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Server_ServerTask_mapCheap___redArg(v_f_55_, v_t_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly___redArg(lean_object* v_f_58_, lean_object* v_t_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(9u);
v___x_61_ = 0;
v___x_62_ = lean_task_map(v_f_58_, v_t_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_mapCostly(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_f_65_, lean_object* v_t_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Server_ServerTask_mapCostly___redArg(v_f_65_, v_t_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(lean_object* v_f_68_, lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_apply_1(v_f_68_, v_x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object* v_t_71_, lean_object* v_f_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; 
v___f_73_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_73_, 0, v_f_72_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = 1;
v___x_76_ = lean_task_bind(v_t_71_, v___f_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCheap(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_t_79_, lean_object* v_f_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_t_79_, v_f_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object* v_t_82_, lean_object* v_f_83_){
_start:
{
lean_object* v___f_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; 
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_bindCheap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_84_, 0, v_f_83_);
v___x_85_ = lean_unsigned_to_nat(9u);
v___x_86_ = 0;
v___x_87_ = lean_task_bind(v_t_82_, v___f_84_, v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_bindCostly(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_t_90_, lean_object* v_f_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Server_ServerTask_bindCostly___redArg(v_t_90_, v_f_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(lean_object* v_acc_93_, lean_object* v_x_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_array_push(v_acc_93_, v_x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(lean_object* v_a_96_, lean_object* v_acc_97_){
_start:
{
lean_object* v___f_98_; lean_object* v___x_99_; 
v___f_98_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_98_, 0, v_acc_97_);
v___x_99_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_98_, v_a_96_);
return v___x_99_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(lean_object* v_as_100_, size_t v_sz_101_, size_t v_i_102_, lean_object* v_b_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_usize_dec_lt(v_i_102_, v_sz_101_);
if (v___x_104_ == 0)
{
return v_b_103_;
}
else
{
lean_object* v_a_105_; lean_object* v___f_106_; lean_object* v___x_107_; size_t v___x_108_; size_t v___x_109_; 
v_a_105_ = lean_array_uget_borrowed(v_as_100_, v_i_102_);
lean_inc(v_a_105_);
v___f_106_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1), 2, 1);
lean_closure_set(v___f_106_, 0, v_a_105_);
v___x_107_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_b_103_, v___f_106_);
v___x_108_ = ((size_t)1ULL);
v___x_109_ = lean_usize_add(v_i_102_, v___x_108_);
v_i_102_ = v___x_109_;
v_b_103_ = v___x_107_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_100_ = stack[0].m_obj;
size_t v_sz_101_ = stack[1].m_num;
size_t v_i_102_ = stack[2].m_num;
lean_object* v_b_103_ = stack[3].m_obj;
lean_object* v_res_111_;
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_100_, v_sz_101_, v_i_102_, v_b_103_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(lean_object* v_as_112_, lean_object* v_sz_113_, lean_object* v_i_114_, lean_object* v_b_115_){
_start:
{
size_t v_sz_boxed_116_; size_t v_i_boxed_117_; lean_object* v_res_118_; 
v_sz_boxed_116_ = lean_unbox_usize(v_sz_113_);
lean_dec(v_sz_113_);
v_i_boxed_117_ = lean_unbox_usize(v_i_114_);
lean_dec(v_i_114_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_112_, v_sz_boxed_116_, v_i_boxed_117_, v_b_115_);
lean_dec_ref(v_as_112_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_join___redArg___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v_r_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Server_ServerTask_join___redArg___closed__0));
v_r_122_ = lean_task_pure(v___x_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg(lean_object* v_ts_123_){
_start:
{
lean_object* v_r_124_; size_t v_sz_125_; size_t v___x_126_; lean_object* v___x_127_; 
v_r_124_ = lean_obj_once(&l_Lean_Server_ServerTask_join___redArg___closed__1, &l_Lean_Server_ServerTask_join___redArg___closed__1_once, _init_l_Lean_Server_ServerTask_join___redArg___closed__1);
v_sz_125_ = lean_array_size(v_ts_123_);
v___x_126_ = ((size_t)0ULL);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_ts_123_, v_sz_125_, v___x_126_, v_r_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___redArg___boxed(lean_object* v_ts_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Server_ServerTask_join___redArg(v_ts_128_);
lean_dec_ref(v_ts_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join(lean_object* v_00_u03b1_130_, lean_object* v_ts_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Server_ServerTask_join___redArg(v_ts_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_join___boxed(lean_object* v_00_u03b1_133_, lean_object* v_ts_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Server_ServerTask_join(v_00_u03b1_133_, v_ts_134_);
lean_dec_ref(v_ts_134_);
return v_res_135_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_object* v_00_u03b1_136_, lean_object* v_as_137_, size_t v_sz_138_, size_t v_i_139_, lean_object* v_b_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_137_, v_sz_138_, v_i_139_, v_b_140_);
return v___x_141_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_137_ = stack[1].m_obj;
size_t v_sz_138_ = stack[2].m_num;
size_t v_i_139_ = stack[3].m_num;
lean_object* v_b_140_ = stack[4].m_obj;
lean_object* v_res_142_;
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(lean_box(0), v_as_137_, v_sz_138_, v_i_139_, v_b_140_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(lean_object* v_00_u03b1_143_, lean_object* v_as_144_, lean_object* v_sz_145_, lean_object* v_i_146_, lean_object* v_b_147_){
_start:
{
size_t v_sz_boxed_148_; size_t v_i_boxed_149_; lean_object* v_res_150_; 
v_sz_boxed_148_ = lean_unbox_usize(v_sz_145_);
lean_dec(v_sz_145_);
v_i_boxed_149_ = lean_unbox_usize(v_i_146_);
lean_dec(v_i_146_);
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(v_00_u03b1_143_, v_as_144_, v_sz_boxed_148_, v_i_boxed_149_, v_b_147_);
lean_dec_ref(v_as_144_);
return v_res_150_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object* v_act_151_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(9u);
v___x_154_ = lean_io_as_task(v_act_151_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_151_ = stack[0].m_obj;
lean_object* v_res_155_;
v_res_155_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_151_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(lean_object* v_act_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_156_);
return v_res_158_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_asTask(lean_object* v_00_u03b1_159_, lean_object* v_act_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_160_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_160_ = stack[1].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_Lean_Server_ServerTask_BaseIO_asTask(lean_box(0), v_act_160_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___boxed(lean_object* v_00_u03b1_164_, lean_object* v_act_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Server_ServerTask_BaseIO_asTask(v_00_u03b1_164_, v_act_165_);
return v_res_167_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(lean_object* v_f_168_, lean_object* v_t_169_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = 1;
v___x_173_ = lean_io_map_task(v_f_168_, v_t_169_, v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_168_ = stack[0].m_obj;
lean_object* v_t_169_ = stack[1].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_168_, v_t_169_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(lean_object* v_f_175_, lean_object* v_t_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_175_, v_t_176_);
return v_res_178_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_f_181_, lean_object* v_t_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_181_, v_t_182_);
return v___x_184_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_mapTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_181_ = stack[2].m_obj;
lean_object* v_t_182_ = stack[3].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(lean_box(0), lean_box(0), v_f_181_, v_t_182_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(lean_object* v_00_u03b1_186_, lean_object* v_00_u03b2_187_, lean_object* v_f_188_, lean_object* v_t_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(v_00_u03b1_186_, v_00_u03b2_187_, v_f_188_, v_t_189_);
return v_res_191_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(lean_object* v_f_192_, lean_object* v_t_193_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(9u);
v___x_196_ = 0;
v___x_197_ = lean_io_map_task(v_f_192_, v_t_193_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_192_ = stack[0].m_obj;
lean_object* v_t_193_ = stack[1].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_192_, v_t_193_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(lean_object* v_f_199_, lean_object* v_t_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_199_, v_t_200_);
return v_res_202_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_f_205_, lean_object* v_t_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_205_, v_t_206_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_mapTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_205_ = stack[2].m_obj;
lean_object* v_t_206_ = stack[3].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(lean_box(0), lean_box(0), v_f_205_, v_t_206_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_f_212_, lean_object* v_t_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(v_00_u03b1_210_, v_00_u03b2_211_, v_f_212_, v_t_213_);
return v_res_215_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(lean_object* v_f_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_apply_2(v_f_216_, v_x_217_, lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_216_ = stack[0].m_obj;
lean_object* v_x_217_ = stack[1].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(v_f_216_, v_x_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_221_, lean_object* v_x_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(v_f_221_, v_x_222_);
return v_res_224_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(lean_object* v_t_225_, lean_object* v_f_226_){
_start:
{
lean_object* v___f_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; 
v___f_228_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_228_, 0, v_f_226_);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = 1;
v___x_231_ = lean_io_bind_task(v_t_225_, v___f_228_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_225_ = stack[0].m_obj;
lean_object* v_f_226_ = stack[1].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_225_, v_f_226_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(lean_object* v_t_233_, lean_object* v_f_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_233_, v_f_234_);
return v_res_236_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_t_239_, lean_object* v_f_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_239_, v_f_240_);
return v___x_242_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_bindTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_239_ = stack[2].m_obj;
lean_object* v_f_240_ = stack[3].m_obj;
lean_object* v_res_243_;
v_res_243_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(lean_box(0), lean_box(0), v_t_239_, v_f_240_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_t_246_, lean_object* v_f_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(v_00_u03b1_244_, v_00_u03b2_245_, v_t_246_, v_f_247_);
return v_res_249_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(lean_object* v_t_250_, lean_object* v_f_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_253_, 0, v_f_251_);
v___x_254_ = lean_unsigned_to_nat(9u);
v___x_255_ = 0;
v___x_256_ = lean_io_bind_task(v_t_250_, v___f_253_, v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_250_ = stack[0].m_obj;
lean_object* v_f_251_ = stack[1].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_250_, v_f_251_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(lean_object* v_t_258_, lean_object* v_f_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_258_, v_f_259_);
return v_res_261_;
}
}
lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_t_264_, lean_object* v_f_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_264_, v_f_265_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_BaseIO_bindTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_264_ = stack[2].m_obj;
lean_object* v_f_265_ = stack[3].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(lean_box(0), lean_box(0), v_t_264_, v_f_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_t_271_, lean_object* v_f_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(v_00_u03b1_269_, v_00_u03b2_270_, v_t_271_, v_f_272_);
return v_res_274_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(lean_object* v_act_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_apply_1(v_act_275_, lean_box(0));
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_277_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_277_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 0);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_275_ = stack[0].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(v_act_275_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed(lean_object* v_act_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(v_act_295_);
return v_res_297_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object* v_act_298_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_300_, 0, v_act_298_);
v___x_301_ = lean_unsigned_to_nat(9u);
v___x_302_ = lean_io_as_task(v___f_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_298_ = stack[0].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_298_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(lean_object* v_act_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_304_);
return v_res_306_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_asTask(lean_object* v_00_u03b5_307_, lean_object* v_00_u03b1_308_, lean_object* v_act_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_309_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_309_ = stack[2].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_Server_ServerTask_EIO_asTask(lean_box(0), lean_box(0), v_act_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_asTask___boxed(lean_object* v_00_u03b5_313_, lean_object* v_00_u03b1_314_, lean_object* v_act_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Server_ServerTask_EIO_asTask(v_00_u03b5_313_, v_00_u03b1_314_, v_act_315_);
return v_res_317_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(lean_object* v_f_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_apply_2(v_f_318_, v_a_319_, lean_box(0));
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 1);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_321_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_321_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 0);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_318_ = stack[0].m_obj;
lean_object* v_a_319_ = stack[1].m_obj;
lean_object* v_res_338_;
v_res_338_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(v_f_318_, v_a_319_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_339_, lean_object* v_a_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(v_f_339_, v_a_340_);
return v_res_342_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object* v_f_343_, lean_object* v_t_344_){
_start:
{
lean_object* v___f_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; 
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_346_, 0, v_f_343_);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = 1;
v___x_349_ = lean_io_map_task(v___f_346_, v_t_344_, v___x_347_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_343_ = stack[0].m_obj;
lean_object* v_t_344_ = stack[1].m_obj;
lean_object* v_res_350_;
v_res_350_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_343_, v_t_344_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(lean_object* v_f_351_, lean_object* v_t_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_351_, v_t_352_);
return v_res_354_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b5_356_, lean_object* v_00_u03b2_357_, lean_object* v_f_358_, lean_object* v_t_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_358_, v_t_359_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_mapTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_358_ = stack[3].m_obj;
lean_object* v_t_359_ = stack[4].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap(lean_box(0), lean_box(0), lean_box(0), v_f_358_, v_t_359_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b5_364_, lean_object* v_00_u03b2_365_, lean_object* v_f_366_, lean_object* v_t_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap(v_00_u03b1_363_, v_00_u03b5_364_, v_00_u03b2_365_, v_f_366_, v_t_367_);
return v_res_369_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object* v_f_370_, lean_object* v_t_371_){
_start:
{
lean_object* v___f_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; 
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_373_, 0, v_f_370_);
v___x_374_ = lean_unsigned_to_nat(9u);
v___x_375_ = 0;
v___x_376_ = lean_io_map_task(v___f_373_, v_t_371_, v___x_374_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_370_ = stack[0].m_obj;
lean_object* v_t_371_ = stack[1].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_370_, v_t_371_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(lean_object* v_f_378_, lean_object* v_t_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_378_, v_t_379_);
return v_res_381_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b5_383_, lean_object* v_00_u03b2_384_, lean_object* v_f_385_, lean_object* v_t_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_385_, v_t_386_);
return v___x_388_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_mapTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_385_ = stack[3].m_obj;
lean_object* v_t_386_ = stack[4].m_obj;
lean_object* v_res_389_;
v_res_389_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly(lean_box(0), lean_box(0), lean_box(0), v_f_385_, v_t_386_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b5_391_, lean_object* v_00_u03b2_392_, lean_object* v_f_393_, lean_object* v_t_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly(v_00_u03b1_390_, v_00_u03b5_391_, v_00_u03b2_392_, v_f_393_, v_t_394_);
return v_res_396_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(lean_object* v_f_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_apply_2(v_f_397_, v_a_398_, lean_box(0));
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
return v_a_401_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_a_402_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_400_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 0);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_409_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; 
v___x_408_ = lean_task_pure(v___x_407_);
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_397_ = stack[0].m_obj;
lean_object* v_a_398_ = stack[1].m_obj;
lean_object* v_res_411_;
v_res_411_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(v_f_397_, v_a_398_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_412_, lean_object* v_a_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(v_f_412_, v_a_413_);
return v_res_415_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object* v_t_416_, lean_object* v_f_417_){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_419_, 0, v_f_417_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = 1;
v___x_422_ = lean_io_bind_task(v_t_416_, v___f_419_, v___x_420_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_416_ = stack[0].m_obj;
lean_object* v_f_417_ = stack[1].m_obj;
lean_object* v_res_423_;
v_res_423_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_416_, v_f_417_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(lean_object* v_t_424_, lean_object* v_f_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_424_, v_f_425_);
return v_res_427_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b5_429_, lean_object* v_00_u03b2_430_, lean_object* v_t_431_, lean_object* v_f_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_431_, v_f_432_);
return v___x_434_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_bindTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_431_ = stack[3].m_obj;
lean_object* v_f_432_ = stack[4].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap(lean_box(0), lean_box(0), lean_box(0), v_t_431_, v_f_432_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b5_437_, lean_object* v_00_u03b2_438_, lean_object* v_t_439_, lean_object* v_f_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap(v_00_u03b1_436_, v_00_u03b5_437_, v_00_u03b2_438_, v_t_439_, v_f_440_);
return v_res_442_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object* v_t_443_, lean_object* v_f_444_){
_start:
{
lean_object* v___f_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
v___f_446_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_446_, 0, v_f_444_);
v___x_447_ = lean_unsigned_to_nat(9u);
v___x_448_ = 0;
v___x_449_ = lean_io_bind_task(v_t_443_, v___f_446_, v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_443_ = stack[0].m_obj;
lean_object* v_f_444_ = stack[1].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_443_, v_f_444_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(lean_object* v_t_451_, lean_object* v_f_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_451_, v_f_452_);
return v_res_454_;
}
}
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b5_456_, lean_object* v_00_u03b2_457_, lean_object* v_t_458_, lean_object* v_f_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_458_, v_f_459_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_EIO_bindTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_458_ = stack[3].m_obj;
lean_object* v_f_459_ = stack[4].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly(lean_box(0), lean_box(0), lean_box(0), v_t_458_, v_f_459_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b5_464_, lean_object* v_00_u03b2_465_, lean_object* v_t_466_, lean_object* v_f_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly(v_00_u03b1_463_, v_00_u03b5_464_, v_00_u03b2_465_, v_t_466_, v_f_467_);
return v_res_469_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(lean_object* v_act_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_1(v_act_470_, lean_box(0));
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 1);
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_a_481_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_472_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_472_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 0);
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_470_ = stack[0].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(v_act_470_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed(lean_object* v_act_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(v_act_490_);
return v_res_492_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object* v_act_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___f_495_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_495_, 0, v_act_493_);
v___x_496_ = lean_unsigned_to_nat(9u);
v___x_497_ = lean_io_as_task(v___f_495_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_493_ = stack[0].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_493_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(lean_object* v_act_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_499_);
return v_res_501_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object* v_00_u03b1_502_, lean_object* v_act_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_503_);
return v___x_505_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_503_ = stack[1].m_obj;
lean_object* v_res_506_;
v_res_506_ = l_Lean_Server_ServerTask_IO_asTask(lean_box(0), v_act_503_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_asTask___boxed(lean_object* v_00_u03b1_507_, lean_object* v_act_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Server_ServerTask_IO_asTask(v_00_u03b1_507_, v_act_508_);
return v_res_510_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(lean_object* v_f_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_apply_2(v_f_511_, v_a_512_, lean_box(0));
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_511_ = stack[0].m_obj;
lean_object* v_a_512_ = stack[1].m_obj;
lean_object* v_res_531_;
v_res_531_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(v_f_511_, v_a_512_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_532_, lean_object* v_a_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(v_f_532_, v_a_533_);
return v_res_535_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(lean_object* v_f_536_, lean_object* v_t_537_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; 
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_539_, 0, v_f_536_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = 1;
v___x_542_ = lean_io_map_task(v___f_539_, v_t_537_, v___x_540_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_536_ = stack[0].m_obj;
lean_object* v_t_537_ = stack[1].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_536_, v_t_537_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(lean_object* v_f_544_, lean_object* v_t_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_544_, v_t_545_);
return v_res_547_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_f_550_, lean_object* v_t_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_550_, v_t_551_);
return v___x_553_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_mapTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_550_ = stack[2].m_obj;
lean_object* v_t_551_ = stack[3].m_obj;
lean_object* v_res_554_;
v_res_554_ = l_Lean_Server_ServerTask_IO_mapTaskCheap(lean_box(0), lean_box(0), v_f_550_, v_t_551_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_f_557_, lean_object* v_t_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Server_ServerTask_IO_mapTaskCheap(v_00_u03b1_555_, v_00_u03b2_556_, v_f_557_, v_t_558_);
return v_res_560_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(lean_object* v_f_561_, lean_object* v_t_562_){
_start:
{
lean_object* v___f_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; 
v___f_564_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_564_, 0, v_f_561_);
v___x_565_ = lean_unsigned_to_nat(9u);
v___x_566_ = 0;
v___x_567_ = lean_io_map_task(v___f_564_, v_t_562_, v___x_565_, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_561_ = stack[0].m_obj;
lean_object* v_t_562_ = stack[1].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_561_, v_t_562_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(lean_object* v_f_569_, lean_object* v_t_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_569_, v_t_570_);
return v_res_572_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_f_575_, lean_object* v_t_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_575_, v_t_576_);
return v___x_578_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_mapTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_575_ = stack[2].m_obj;
lean_object* v_t_576_ = stack[3].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_box(0), lean_box(0), v_f_575_, v_t_576_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_f_582_, lean_object* v_t_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Server_ServerTask_IO_mapTaskCostly(v_00_u03b1_580_, v_00_u03b2_581_, v_f_582_, v_t_583_);
return v_res_585_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(lean_object* v_f_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_2(v_f_586_, v_a_587_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
return v_a_590_;
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_a_591_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 0);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_task_pure(v___x_596_);
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_586_ = stack[0].m_obj;
lean_object* v_a_587_ = stack[1].m_obj;
lean_object* v_res_600_;
v_res_600_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(v_f_586_, v_a_587_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_601_, lean_object* v_a_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(v_f_601_, v_a_602_);
return v_res_604_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(lean_object* v_t_605_, lean_object* v_f_606_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; 
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_608_, 0, v_f_606_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = 1;
v___x_611_ = lean_io_bind_task(v_t_605_, v___f_608_, v___x_609_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_605_ = stack[0].m_obj;
lean_object* v_f_606_ = stack[1].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_605_, v_f_606_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(lean_object* v_t_613_, lean_object* v_f_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_613_, v_f_614_);
return v_res_616_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_t_619_, lean_object* v_f_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_619_, v_f_620_);
return v___x_622_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_bindTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_619_ = stack[2].m_obj;
lean_object* v_f_620_ = stack[3].m_obj;
lean_object* v_res_623_;
v_res_623_ = l_Lean_Server_ServerTask_IO_bindTaskCheap(lean_box(0), lean_box(0), v_t_619_, v_f_620_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_t_626_, lean_object* v_f_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Server_ServerTask_IO_bindTaskCheap(v_00_u03b1_624_, v_00_u03b2_625_, v_t_626_, v_f_627_);
return v_res_629_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(lean_object* v_t_630_, lean_object* v_f_631_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; 
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_633_, 0, v_f_631_);
v___x_634_ = lean_unsigned_to_nat(9u);
v___x_635_ = 0;
v___x_636_ = lean_io_bind_task(v_t_630_, v___f_633_, v___x_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_630_ = stack[0].m_obj;
lean_object* v_f_631_ = stack[1].m_obj;
lean_object* v_res_637_;
v_res_637_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_630_, v_f_631_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(lean_object* v_t_638_, lean_object* v_f_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_638_, v_f_639_);
return v_res_641_;
}
}
lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_t_644_, lean_object* v_f_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_644_, v_f_645_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_IO_bindTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_644_ = stack[2].m_obj;
lean_object* v_f_645_ = stack[3].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Server_ServerTask_IO_bindTaskCostly(lean_box(0), lean_box(0), v_t_644_, v_f_645_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_t_651_, lean_object* v_f_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Server_ServerTask_IO_bindTaskCostly(v_00_u03b1_649_, v_00_u03b2_650_, v_t_651_, v_f_652_);
return v_res_654_;
}
}
uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object* v_t_655_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = lean_io_get_task_state(v_t_655_);
if (v___x_657_ == 2)
{
uint8_t v___x_658_; 
v___x_658_ = 1;
return v___x_658_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_hasFinished___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_655_ = stack[0].m_obj;
uint8_t v_res_660_;
v_res_660_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_655_);
stack->m_num = v_res_660_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___redArg___boxed(lean_object* v_t_661_, lean_object* v_a_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_661_);
lean_dec_ref(v_t_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
uint8_t l_Lean_Server_ServerTask_hasFinished(lean_object* v_00_u03b1_665_, lean_object* v_t_666_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_666_);
return v___x_668_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_hasFinished_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_666_ = stack[1].m_obj;
uint8_t v_res_669_;
v_res_669_ = l_Lean_Server_ServerTask_hasFinished(lean_box(0), v_t_666_);
stack->m_num = v_res_669_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_hasFinished___boxed(lean_object* v_00_u03b1_670_, lean_object* v_t_671_, lean_object* v_a_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_Server_ServerTask_hasFinished(v_00_u03b1_670_, v_t_671_);
lean_dec_ref(v_t_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10));
v___x_702_ = l_Lean_mkAtom(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__12, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12);
v___x_704_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_705_ = lean_array_push(v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22));
v___x_729_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_730_ = lean_array_push(v___x_729_, v___x_728_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__27(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26));
v___x_739_ = l_Lean_mkAtom(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__27, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__27);
v___x_741_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_742_ = lean_array_push(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__28, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28);
v___x_744_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__25));
v___x_745_ = lean_box(2);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__29, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29);
v___x_748_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_749_ = lean_array_push(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__30, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30);
v___x_751_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
v___x_752_ = lean_box(2);
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
lean_ctor_set(v___x_753_, 2, v___x_750_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__31, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31);
v___x_755_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__23, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23);
v___x_756_ = lean_array_push(v___x_755_, v___x_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_757_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__32, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32);
v___x_758_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16));
v___x_759_ = lean_box(2);
v___x_760_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v___x_758_);
lean_ctor_set(v___x_760_, 2, v___x_757_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__33, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33);
v___x_762_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__13, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13);
v___x_763_ = lean_array_push(v___x_762_, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__34, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34);
v___x_765_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11));
v___x_766_ = lean_box(2);
v___x_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v___x_764_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__35, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35);
v___x_769_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_770_ = lean_array_push(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_771_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__36, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36);
v___x_772_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9));
v___x_773_ = lean_box(2);
v___x_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_771_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__37, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37);
v___x_776_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_777_ = lean_array_push(v___x_776_, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__38, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38);
v___x_779_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7));
v___x_780_ = lean_box(2);
v___x_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_779_);
lean_ctor_set(v___x_781_, 2, v___x_778_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__39, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39);
v___x_783_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5));
v___x_784_ = lean_array_push(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__40, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40);
v___x_786_ = ((lean_object*)(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4));
v___x_787_ = lean_box(2);
v___x_788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
lean_ctor_set(v___x_788_, 2, v___x_785_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Server_ServerTask_waitAny___auto__1(void){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lean_obj_once(&l_Lean_Server_ServerTask_waitAny___auto__1___closed__41, &l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once, _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
if (lean_obj_tag(v_a_790_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = l_List_reverse___redArg(v_a_791_);
return v___x_792_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_head_793_ = lean_ctor_get(v_a_790_, 0);
v_tail_794_ = lean_ctor_get(v_a_790_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v_a_790_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_tail_794_);
lean_inc(v_head_793_);
lean_dec(v_a_790_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_a_791_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_head_793_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_791_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v_a_790_ = v_tail_794_;
v_a_791_ = v___x_799_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object* v_tasks_803_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_box(0);
v___x_806_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(v_tasks_803_, v___x_805_);
v___x_807_ = lean_io_wait_any(v___x_806_);
lean_dec(v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_waitAny___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tasks_803_ = stack[0].m_obj;
lean_object* v_res_808_;
v_res_808_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_803_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___redArg___boxed(lean_object* v_tasks_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_809_);
return v_res_811_;
}
}
lean_object* l_Lean_Server_ServerTask_waitAny(lean_object* v_00_u03b1_812_, lean_object* v_tasks_813_, lean_object* v_h_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_813_);
return v___x_816_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_waitAny_0interp(lean_interpreter_value* stack)
{
lean_object* v_tasks_813_ = stack[1].m_obj;
lean_object* v_res_817_;
v_res_817_ = l_Lean_Server_ServerTask_waitAny(lean_box(0), v_tasks_813_, lean_box(0));
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_waitAny___boxed(lean_object* v_00_u03b1_818_, lean_object* v_tasks_819_, lean_object* v_h_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Server_ServerTask_waitAny(v_00_u03b1_818_, v_tasks_819_, v_h_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(lean_object* v_00_u03b1_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(v_a_824_, v_a_825_);
return v___x_826_;
}
}
lean_object* l_Lean_Server_ServerTask_cancel___redArg(lean_object* v_t_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_io_cancel(v_t_827_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_cancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_827_ = stack[0].m_obj;
lean_object* v_res_830_;
v_res_830_ = l_Lean_Server_ServerTask_cancel___redArg(v_t_827_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___redArg___boxed(lean_object* v_t_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Server_ServerTask_cancel___redArg(v_t_831_);
lean_dec_ref(v_t_831_);
return v_res_833_;
}
}
lean_object* l_Lean_Server_ServerTask_cancel(lean_object* v_00_u03b1_834_, lean_object* v_t_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_io_cancel(v_t_835_);
return v___x_837_;
}
}
LEAN_EXPORT void l_Lean_Server_ServerTask_cancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_835_ = stack[1].m_obj;
lean_object* v_res_838_;
v_res_838_ = l_Lean_Server_ServerTask_cancel(lean_box(0), v_t_835_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerTask_cancel___boxed(lean_object* v_00_u03b1_839_, lean_object* v_t_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Server_ServerTask_cancel(v_00_u03b1_839_, v_t_840_);
lean_dec_ref(v_t_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___redArg(lean_object* v_t_843_){
_start:
{
lean_inc_ref(v_t_843_);
return v_t_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___redArg___boxed(lean_object* v_t_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Task_asServerTask___redArg(v_t_844_);
lean_dec_ref(v_t_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask(lean_object* v_00_u03b1_846_, lean_object* v_t_847_){
_start:
{
lean_inc_ref(v_t_847_);
return v_t_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Task_asServerTask___boxed(lean_object* v_00_u03b1_848_, lean_object* v_t_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Task_asServerTask(v_00_u03b1_848_, v_t_849_);
lean_dec_ref(v_t_849_);
return v_res_850_;
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
