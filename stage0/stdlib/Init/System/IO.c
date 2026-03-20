// Lean compiler output
// Module: Init.System.IO
// Imports: public import Init.Control.Do public import Init.System.IOError public import Init.System.FilePath import Init.Data.String.TakeDrop import Init.Data.String.Search public import Init.Data.Ord.Basic public import Init.Data.String.Basic import Init.Data.List.MapIdx import Init.Data.Ord.UInt import Init.Data.ToString.Macro import Init.Data.List.Impl import Init.Data.Int.Repr
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
lean_object* l_instMonadExceptOfEST(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_instMonadFinallyST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadAttachEST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadAttachST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_RealWorld_nonemptyType;
static lean_once_cell_t l_instMonadBaseIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadBaseIO___closed__0;
LEAN_EXPORT lean_object* l_instMonadBaseIO;
static const lean_closure_object l_instMonadFinallyBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadFinallyBaseIO___closed__0 = (const lean_object*)&l_instMonadFinallyBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_instMonadFinallyBaseIO = (const lean_object*)&l_instMonadFinallyBaseIO___closed__0_value;
static const lean_closure_object l_instMonadAttachBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachST___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachBaseIO___closed__0 = (const lean_object*)&l_instMonadAttachBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_instMonadAttachBaseIO = (const lean_object*)&l_instMonadAttachBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_BaseIO_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadLiftBaseIOEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadLiftBaseIOEIO___closed__0 = (const lean_object*)&l_instMonadLiftBaseIOEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_instMonadEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadEIO___closed__0;
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
static const lean_closure_object l_instMonadFinallyEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadFinallyEIO___closed__0 = (const lean_object*)&l_instMonadFinallyEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
static const lean_closure_object l_instMonadAttachEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachEST___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachEIO___closed__0 = (const lean_object*)&l_instMonadAttachEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object*);
static lean_once_cell_t l_instMonadExceptOfEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadExceptOfEIO___closed__0;
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
static lean_once_cell_t l_instOrElseEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___closed__0;
static lean_once_cell_t l_instOrElseEIO___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___closed__1;
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO(lean_object*, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_initializing();
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object*);
lean_object* lean_io_mono_nanos_now();
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_check_canceled();
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object*);
lean_object* lean_io_cancel(lean_object*);
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState_default;
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState;
static const lean_string_object l_IO_instReprTaskState_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IO.TaskState.waiting"};
static const lean_object* l_IO_instReprTaskState_repr___closed__0 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__0_value;
static const lean_ctor_object l_IO_instReprTaskState_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_instReprTaskState_repr___closed__0_value)}};
static const lean_object* l_IO_instReprTaskState_repr___closed__1 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__1_value;
static const lean_string_object l_IO_instReprTaskState_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IO.TaskState.running"};
static const lean_object* l_IO_instReprTaskState_repr___closed__2 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__2_value;
static const lean_ctor_object l_IO_instReprTaskState_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_instReprTaskState_repr___closed__2_value)}};
static const lean_object* l_IO_instReprTaskState_repr___closed__3 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__3_value;
static const lean_string_object l_IO_instReprTaskState_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "IO.TaskState.finished"};
static const lean_object* l_IO_instReprTaskState_repr___closed__4 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__4_value;
static const lean_ctor_object l_IO_instReprTaskState_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_instReprTaskState_repr___closed__4_value)}};
static const lean_object* l_IO_instReprTaskState_repr___closed__5 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__5_value;
static lean_once_cell_t l_IO_instReprTaskState_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_instReprTaskState_repr___closed__6;
static lean_once_cell_t l_IO_instReprTaskState_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_instReprTaskState_repr___closed__7;
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instReprTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instReprTaskState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instReprTaskState___closed__0 = (const lean_object*)&l_IO_instReprTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instReprTaskState = (const lean_object*)&l_IO_instReprTaskState___closed__0_value;
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instOrdTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instOrdTaskState_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instOrdTaskState___closed__0 = (const lean_object*)&l_IO_instOrdTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instOrdTaskState = (const lean_object*)&l_IO_instOrdTaskState___closed__0_value;
LEAN_EXPORT lean_object* l_IO_instLTTaskState;
LEAN_EXPORT lean_object* l_IO_instLETaskState;
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instMinTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMinTaskState___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instMinTaskState___closed__0 = (const lean_object*)&l_IO_instMinTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instMinTaskState = (const lean_object*)&l_IO_instMinTaskState___closed__0_value;
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instMaxTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMaxTaskState___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instMaxTaskState___closed__0 = (const lean_object*)&l_IO_instMaxTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instMaxTaskState = (const lean_object*)&l_IO_instMaxTaskState___closed__0_value;
static const lean_string_object l_IO_TaskState_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "waiting"};
static const lean_object* l_IO_TaskState_toString___closed__0 = (const lean_object*)&l_IO_TaskState_toString___closed__0_value;
static const lean_string_object l_IO_TaskState_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "running"};
static const lean_object* l_IO_TaskState_toString___closed__1 = (const lean_object*)&l_IO_TaskState_toString___closed__1_value;
static const lean_string_object l_IO_TaskState_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "finished"};
static const lean_object* l_IO_TaskState_toString___closed__2 = (const lean_object*)&l_IO_TaskState_toString___closed__2_value;
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object*);
static const lean_closure_object l_IO_instToStringTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_TaskState_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instToStringTaskState___closed__0 = (const lean_object*)&l_IO_instToStringTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instToStringTaskState = (const lean_object*)&l_IO_instToStringTaskState___closed__0_value;
uint8_t lean_io_get_task_state(lean_object*);
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_waitAny___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_IO_waitAny___auto__1___closed__0 = (const lean_object*)&l_IO_waitAny___auto__1___closed__0_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_IO_waitAny___auto__1___closed__1 = (const lean_object*)&l_IO_waitAny___auto__1___closed__1_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_IO_waitAny___auto__1___closed__2 = (const lean_object*)&l_IO_waitAny___auto__1___closed__2_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_IO_waitAny___auto__1___closed__3 = (const lean_object*)&l_IO_waitAny___auto__1___closed__3_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__4_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__4_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__4_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_IO_waitAny___auto__1___closed__4 = (const lean_object*)&l_IO_waitAny___auto__1___closed__4_value;
static const lean_array_object l_IO_waitAny___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_IO_waitAny___auto__1___closed__5 = (const lean_object*)&l_IO_waitAny___auto__1___closed__5_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_IO_waitAny___auto__1___closed__6 = (const lean_object*)&l_IO_waitAny___auto__1___closed__6_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__7_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__7_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__7_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_IO_waitAny___auto__1___closed__7 = (const lean_object*)&l_IO_waitAny___auto__1___closed__7_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_IO_waitAny___auto__1___closed__8 = (const lean_object*)&l_IO_waitAny___auto__1___closed__8_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_IO_waitAny___auto__1___closed__9 = (const lean_object*)&l_IO_waitAny___auto__1___closed__9_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_IO_waitAny___auto__1___closed__10 = (const lean_object*)&l_IO_waitAny___auto__1___closed__10_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__11_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__11_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__11_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_IO_waitAny___auto__1___closed__11 = (const lean_object*)&l_IO_waitAny___auto__1___closed__11_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__12;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__13;
static const lean_string_object l_IO_waitAny___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_IO_waitAny___auto__1___closed__14 = (const lean_object*)&l_IO_waitAny___auto__1___closed__14_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_IO_waitAny___auto__1___closed__15 = (const lean_object*)&l_IO_waitAny___auto__1___closed__15_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__16_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__16_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__16_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_IO_waitAny___auto__1___closed__16 = (const lean_object*)&l_IO_waitAny___auto__1___closed__16_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Nat.zero_lt_succ"};
static const lean_object* l_IO_waitAny___auto__1___closed__17 = (const lean_object*)&l_IO_waitAny___auto__1___closed__17_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__18;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__19;
static const lean_string_object l_IO_waitAny___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_IO_waitAny___auto__1___closed__20 = (const lean_object*)&l_IO_waitAny___auto__1___closed__20_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "zero_lt_succ"};
static const lean_object* l_IO_waitAny___auto__1___closed__21 = (const lean_object*)&l_IO_waitAny___auto__1___closed__21_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__22_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(139, 13, 209, 151, 253, 249, 15, 51)}};
static const lean_object* l_IO_waitAny___auto__1___closed__22 = (const lean_object*)&l_IO_waitAny___auto__1___closed__22_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__23;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__24;
static const lean_string_object l_IO_waitAny___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_IO_waitAny___auto__1___closed__25 = (const lean_object*)&l_IO_waitAny___auto__1___closed__25_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__26_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__26_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__26_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_IO_waitAny___auto__1___closed__26 = (const lean_object*)&l_IO_waitAny___auto__1___closed__26_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_IO_waitAny___auto__1___closed__27 = (const lean_object*)&l_IO_waitAny___auto__1___closed__27_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__28;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__29;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__30;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__31;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__32;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__33;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__34;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__35;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__36;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__37;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__38;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__39;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__40;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__41;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__42;
LEAN_EXPORT lean_object* l_IO_waitAny___auto__1;
lean_object* lean_io_wait_any(lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___auto__1;
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_IO_waitAny_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_IO_waitAny_x27___redArg___closed__0 = (const lean_object*)&l_IO_waitAny_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_IO_FS_instInhabitedStream_default___lam__0___closed__0 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value;
static const lean_ctor_object l_IO_FS_instInhabitedStream_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value)}};
static const lean_object* l_IO_FS_instInhabitedStream_default___lam__0___closed__1 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0();
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(size_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3();
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__0 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__0_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__1 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__1_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__2 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__2_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__3 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__3_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__4 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__4_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__5 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__5_value;
static const lean_ctor_object l_IO_FS_instInhabitedStream_default___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__0_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__1_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__2_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__3_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__4_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__5_value)}};
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__6 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__6_value;
LEAN_EXPORT const lean_object* l_IO_FS_instInhabitedStream_default = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__6_value;
LEAN_EXPORT const lean_object* l_IO_FS_instInhabitedStream = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__6_value;
lean_object* lean_get_stdin();
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object*);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object*);
lean_object* lean_get_stderr();
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object*);
lean_object* lean_get_set_stdin(lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object*, lean_object*);
uint8_t lean_io_prim_handle_is_tty(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
lean_object* lean_io_remove_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object*, lean_object*);
lean_object* lean_io_create_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object*, lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object*);
lean_object* lean_io_create_tempdir();
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object*);
lean_object* lean_io_getenv(lean_object*);
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
lean_object* lean_io_app_path();
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object*);
lean_object* lean_io_current_dir();
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Handle_readToEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Tried to read from handle containing non UTF-8 data."};
static const lean_object* l_IO_FS_Handle_readToEnd___closed__0 = (const lean_object*)&l_IO_FS_Handle_readToEnd___closed__0_value;
static const lean_ctor_object l_IO_FS_Handle_readToEnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_Handle_readToEnd___closed__0_value)}};
static const lean_object* l_IO_FS_Handle_readToEnd___closed__1 = (const lean_object*)&l_IO_FS_Handle_readToEnd___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_IO_FS_Handle_lines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_IO_FS_Handle_lines___closed__0 = (const lean_object*)&l_IO_FS_Handle_lines___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object*);
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__0 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "root"};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__1 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__2 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__3 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__4 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__5 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__6 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__6_value;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__8 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__9 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__9_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__10 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__11 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__11_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fileName"};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__12 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__13 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__13_value;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__14;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__15 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__16;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__18 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__18_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__19 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprDirEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprDirEntry_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprDirEntry___closed__0 = (const lean_object*)&l_IO_FS_instReprDirEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprDirEntry = (const lean_object*)&l_IO_FS_instReprDirEntry___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "IO.FS.FileType.dir"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__0 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__0_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__0_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__1 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__1_value;
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "IO.FS.FileType.file"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__2 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__2_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__3 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__3_value;
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "IO.FS.FileType.symlink"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__4 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__4_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__4_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__5 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__5_value;
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IO.FS.FileType.other"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__6 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__6_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__6_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__7 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__7_value;
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprFileType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprFileType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprFileType___closed__0 = (const lean_object*)&l_IO_FS_instReprFileType___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprFileType = (const lean_object*)&l_IO_FS_instReprFileType___closed__0_value;
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instBEqFileType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instBEqFileType_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instBEqFileType___closed__0 = (const lean_object*)&l_IO_FS_instBEqFileType___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instBEqFileType = (const lean_object*)&l_IO_FS_instBEqFileType___closed__0_value;
static const lean_string_object l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sec"};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__0 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__1 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__2 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__3 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__3_value;
static lean_once_cell_t l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__4;
static const lean_string_object l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nsec"};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__5 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__6 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__6_value;
static lean_once_cell_t l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprSystemTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprSystemTime_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprSystemTime___closed__0 = (const lean_object*)&l_IO_FS_instReprSystemTime___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprSystemTime = (const lean_object*)&l_IO_FS_instReprSystemTime___closed__0_value;
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instBEqSystemTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instBEqSystemTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instBEqSystemTime___closed__0 = (const lean_object*)&l_IO_FS_instBEqSystemTime___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instBEqSystemTime = (const lean_object*)&l_IO_FS_instBEqSystemTime___closed__0_value;
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instOrdSystemTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instOrdSystemTime_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instOrdSystemTime___closed__0 = (const lean_object*)&l_IO_FS_instOrdSystemTime___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instOrdSystemTime = (const lean_object*)&l_IO_FS_instOrdSystemTime___closed__0_value;
static lean_once_cell_t l_IO_FS_instInhabitedSystemTime_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_IO_FS_instInhabitedSystemTime_default___closed__0;
static lean_once_cell_t l_IO_FS_instInhabitedSystemTime_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instInhabitedSystemTime_default___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime_default;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_instLTSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_instLESystemTime;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "accessed"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__0 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__0_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__0_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__1 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__1_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__1_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__2 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__2_value),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__3 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__3_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "modified"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__4 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__4_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__4_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__5 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__5_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byteSize"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__6 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__6_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__6_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__7 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__7_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__8 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__8_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__8_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__9 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__9_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "numLinks"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__10 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__10_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__10_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__11 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprMetadata_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprMetadata___closed__0 = (const lean_object*)&l_IO_FS_instReprMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprMetadata = (const lean_object*)&l_IO_FS_instReprMetadata___closed__0_value;
lean_object* lean_io_read_dir(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object*, lean_object*);
lean_object* lean_io_symlink_metadata(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_IO_FS_readBinFile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_readBinFile___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_readFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Tried to read file '"};
static const lean_object* l_IO_FS_readFile___closed__0 = (const lean_object*)&l_IO_FS_readFile___closed__0_value;
static const lean_string_object l_IO_FS_readFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' containing non UTF-8 data."};
static const lean_object* l_IO_FS_readFile___closed__1 = (const lean_object*)&l_IO_FS_readFile___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_withStdin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_withStdin___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_withStdin___redArg___closed__0 = (const lean_object*)&l_IO_withStdin___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_println___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_println___redArg___closed__0 = (const lean_object*)&l_IO_println___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_eprint(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_appDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "IO.appDir: unexpected filename '"};
static const lean_object* l_IO_appDir___closed__0 = (const lean_object*)&l_IO_appDir___closed__0_value;
static const lean_string_object l_IO_appDir___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_IO_appDir___closed__1 = (const lean_object*)&l_IO_appDir___closed__1_value;
LEAN_EXPORT lean_object* l_IO_appDir();
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_withTempFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_createTempFile___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_withTempFile___redArg___closed__0 = (const lean_object*)&l_IO_FS_withTempFile___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_withTempDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_createTempDir___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_withTempDir___redArg___closed__0 = (const lean_object*)&l_IO_FS_withTempDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_get_current_dir();
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object*);
lean_object* lean_io_process_set_current_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object*, lean_object*);
uint32_t lean_io_process_get_pid();
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_kill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_io_process_child_pid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_IO_Process_output___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_IO_Process_output___closed__0 = (const lean_object*)&l_IO_Process_output___closed__0_value;
static const lean_ctor_object l_IO_Process_output___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_IO_Process_output___closed__1 = (const lean_object*)&l_IO_Process_output___closed__1_value;
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_Process_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "process '"};
static const lean_object* l_IO_Process_run___closed__0 = (const lean_object*)&l_IO_Process_run___closed__0_value;
static const lean_string_object l_IO_Process_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' exited with code "};
static const lean_object* l_IO_Process_run___closed__1 = (const lean_object*)&l_IO_Process_run___closed__1_value;
static const lean_string_object l_IO_Process_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_IO_Process_run___closed__2 = (const lean_object*)&l_IO_Process_run___closed__2_value;
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_force_exit(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_io_get_tid();
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object*);
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object*);
lean_object* lean_chmod(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___closed__0 = (const lean_object*)&l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instMonadLiftSTRealWorldBaseIO = (const lean_object*)&l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_new();
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_CancelToken_isSetExport___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid UTF-8"};
static const lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__0 = (const lean_object*)&l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value;
static const lean_ctor_object l_IO_FS_Stream_ofBuffer___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value)}};
static const lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__1 = (const lean_object*)&l_IO_FS_Stream_ofBuffer___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_Stream_ofBuffer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_Stream_ofBuffer___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_IO_FS_Stream_ofBuffer___closed__0 = (const lean_object*)&l_IO_FS_Stream_ofBuffer___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static const lean_ctor_object l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(1024ULL)}};
LEAN_EXPORT const lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1 = (const lean_object*)&l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readToEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Tried to read from stream containing non UTF-8 data."};
static const lean_object* l_IO_FS_Stream_readToEnd___closed__0 = (const lean_object*)&l_IO_FS_Stream_readToEnd___closed__0_value;
static const lean_ctor_object l_IO_FS_Stream_readToEnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_Stream_readToEnd___closed__0_value)}};
static const lean_object* l_IO_FS_Stream_readToEnd___closed__1 = (const lean_object*)&l_IO_FS_Stream_readToEnd___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_IO_FS_withIsolatedStreams___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__0;
static lean_once_cell_t l_IO_FS_withIsolatedStreams___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_termPrintln_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termPrintln!__"};
static const lean_object* l_termPrintln_x21_____00__closed__0 = (const lean_object*)&l_termPrintln_x21_____00__closed__0_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 121, 220, 17, 1, 74, 122, 9)}};
static const lean_object* l_termPrintln_x21_____00__closed__1 = (const lean_object*)&l_termPrintln_x21_____00__closed__1_value;
static const lean_string_object l_termPrintln_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_termPrintln_x21_____00__closed__2 = (const lean_object*)&l_termPrintln_x21_____00__closed__2_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_termPrintln_x21_____00__closed__3 = (const lean_object*)&l_termPrintln_x21_____00__closed__3_value;
static const lean_string_object l_termPrintln_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "println! "};
static const lean_object* l_termPrintln_x21_____00__closed__4 = (const lean_object*)&l_termPrintln_x21_____00__closed__4_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__4_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__5 = (const lean_object*)&l_termPrintln_x21_____00__closed__5_value;
static const lean_string_object l_termPrintln_x21_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_termPrintln_x21_____00__closed__6 = (const lean_object*)&l_termPrintln_x21_____00__closed__6_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_termPrintln_x21_____00__closed__7 = (const lean_object*)&l_termPrintln_x21_____00__closed__7_value;
static const lean_string_object l_termPrintln_x21_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_termPrintln_x21_____00__closed__8 = (const lean_object*)&l_termPrintln_x21_____00__closed__8_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_termPrintln_x21_____00__closed__9 = (const lean_object*)&l_termPrintln_x21_____00__closed__9_value;
static const lean_string_object l_termPrintln_x21_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_termPrintln_x21_____00__closed__10 = (const lean_object*)&l_termPrintln_x21_____00__closed__10_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_termPrintln_x21_____00__closed__11 = (const lean_object*)&l_termPrintln_x21_____00__closed__11_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_termPrintln_x21_____00__closed__12 = (const lean_object*)&l_termPrintln_x21_____00__closed__12_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__9_value),((lean_object*)&l_termPrintln_x21_____00__closed__12_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__13 = (const lean_object*)&l_termPrintln_x21_____00__closed__13_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__7_value),((lean_object*)&l_termPrintln_x21_____00__closed__13_value),((lean_object*)&l_termPrintln_x21_____00__closed__12_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__14 = (const lean_object*)&l_termPrintln_x21_____00__closed__14_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__3_value),((lean_object*)&l_termPrintln_x21_____00__closed__5_value),((lean_object*)&l_termPrintln_x21_____00__closed__14_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__15 = (const lean_object*)&l_termPrintln_x21_____00__closed__15_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__15_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__16 = (const lean_object*)&l_termPrintln_x21_____00__closed__16_value;
LEAN_EXPORT const lean_object* l_termPrintln_x21____ = (const lean_object*)&l_termPrintln_x21_____00__closed__16_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_2),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IO.println"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IO"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "println"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(2, 76, 19, 202, 4, 69, 238, 60)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(113, 81, 230, 194, 109, 88, 193, 19)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(2, 76, 19, 202, 4, 69, 238, 60)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_2),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termS!_"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(30, 130, 93, 49, 63, 146, 201, 153)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s!"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42_value;
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_multi_threaded(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_IO_RealWorld_nonemptyType(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_instMonadBaseIO___closed__0(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_instMonadST(lean_box(0));
return v___x_2_;
}
}
static lean_object* _init_l_instMonadBaseIO(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_instMonadBaseIO___closed__0, &l_instMonadBaseIO___closed__0_once, _init_l_instMonadBaseIO___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg(lean_object* v_f_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_apply_1(v_x_9_, lean_box(0));
v___x_12_ = lean_apply_1(v_f_8_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object* v_f_13_, lean_object* v_x_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_BaseIO_map___redArg(v_f_13_, v_x_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_f_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_apply_1(v_x_20_, lean_box(0));
v___x_23_ = lean_apply_1(v_f_19_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_f_26_, lean_object* v_x_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_BaseIO_map(v_00_u03b1_24_, v_00_u03b2_25_, v_f_26_, v_x_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object* v_act_30_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_apply_1(v_act_30_, lean_box(0));
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object* v_act_34_, lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_BaseIO_toEIO___redArg(v_act_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object* v_00_u03b1_37_, lean_object* v_00_u03b5_38_, lean_object* v_act_39_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_apply_1(v_act_39_, lean_box(0));
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b5_44_, lean_object* v_act_45_, lean_object* v_s_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_BaseIO_toEIO(v_00_u03b1_43_, v_00_u03b5_44_, v_act_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object* v_00_u03b1_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_apply_1(v___y_49_, lean_box(0));
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object* v_00_u03b1_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_instMonadLiftBaseIOEIO___lam__0(v_00_u03b1_53_, v___y_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* v_00_u03b5_58_){
_start:
{
lean_object* v___f_59_; 
v___f_59_ = ((lean_object*)(l_instMonadLiftBaseIOEIO___closed__0));
return v___f_59_;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object* v_act_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_apply_1(v_act_60_, lean_box(0));
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 1);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_a_71_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_62_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_62_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 0);
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object* v_act_79_, lean_object* v_s_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_EIO_toBaseIO___redArg(v_act_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* v_00_u03b5_82_, lean_object* v_00_u03b1_83_, lean_object* v_act_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_apply_1(v_act_84_, lean_box(0));
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 1);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_a_95_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_86_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_86_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 0);
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object* v_00_u03b5_103_, lean_object* v_00_u03b1_104_, lean_object* v_act_105_, lean_object* v_s_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_EIO_toBaseIO(v_00_u03b5_103_, v_00_u03b1_104_, v_act_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object* v_act_108_, lean_object* v_h_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_apply_1(v_act_108_, lean_box(0));
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; 
lean_dec_ref(v_h_109_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v___x_111_);
return v_a_112_;
}
else
{
lean_object* v_a_113_; lean_object* v___x_114_; 
v_a_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_113_);
lean_dec_ref(v___x_111_);
v___x_114_ = lean_apply_2(v_h_109_, v_a_113_, lean_box(0));
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object* v_act_115_, lean_object* v_h_116_, lean_object* v_s_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_EIO_catchExceptions___redArg(v_act_115_, v_h_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* v_00_u03b5_119_, lean_object* v_00_u03b1_120_, lean_object* v_act_121_, lean_object* v_h_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_1(v_act_121_, lean_box(0));
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; 
lean_dec_ref(v_h_122_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v___x_124_);
return v_a_125_;
}
else
{
lean_object* v_a_126_; lean_object* v___x_127_; 
v_a_126_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_126_);
lean_dec_ref(v___x_124_);
v___x_127_ = lean_apply_2(v_h_122_, v_a_126_, lean_box(0));
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object* v_00_u03b5_128_, lean_object* v_00_u03b1_129_, lean_object* v_act_130_, lean_object* v_h_131_, lean_object* v_s_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_EIO_catchExceptions(v_00_u03b5_128_, v_00_u03b1_129_, v_act_130_, v_h_131_);
return v_res_133_;
}
}
static lean_object* _init_l_instMonadEIO___closed__0(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* v_00_u03b5_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_instMonadEIO___closed__0, &l_instMonadEIO___closed__0_once, _init_l_instMonadEIO___closed__0);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* v_00_u03b5_138_){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_instMonadFinallyEIO___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object* v_00_u03b5_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = ((lean_object*)(l_instMonadAttachEIO___closed__0));
return v___f_142_;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__0(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_instMonadExceptOfEST(lean_box(0), lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* v_00_u03b5_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_instMonadExceptOfEIO___closed__0, &l_instMonadExceptOfEIO___closed__0_once, _init_l_instMonadExceptOfEIO___closed__0);
return v___x_145_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__0(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_instMonadExceptOfEIO___closed__0, &l_instMonadExceptOfEIO___closed__0_once, _init_l_instMonadExceptOfEIO___closed__0);
v___x_147_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__1(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_obj_once(&l_instOrElseEIO___closed__0, &l_instOrElseEIO___closed__0_once, _init_l_instOrElseEIO___closed__0);
v___x_149_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_149_, 0, lean_box(0));
lean_closure_set(v___x_149_, 1, lean_box(0));
lean_closure_set(v___x_149_, 2, v___x_148_);
lean_closure_set(v___x_149_, 3, lean_box(0));
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* v_00_u03b5_150_, lean_object* v_00_u03b1_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_instOrElseEIO___closed__1, &l_instOrElseEIO___closed__1_once, _init_l_instOrElseEIO___closed__1);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object* v_inst_153_){
_start:
{
lean_object* v___f_154_; 
v___f_154_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_154_, 0, v_inst_153_);
return v___f_154_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* v_00_u03b5_155_, lean_object* v_00_u03b1_156_, lean_object* v_inst_157_){
_start:
{
lean_object* v___f_158_; 
v___f_158_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_158_, 0, v_inst_157_);
return v___f_158_;
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object* v_f_159_, lean_object* v_x_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_1(v_x_160_, lean_box(0));
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_171_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_171_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_apply_1(v_f_159_, v_a_163_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_167_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_f_159_);
v_a_172_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_162_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_162_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object* v_f_180_, lean_object* v_x_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_EIO_map___redArg(v_f_180_, v_x_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_EIO_map(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_00_u03b5_186_, lean_object* v_f_187_, lean_object* v_x_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_apply_1(v_x_188_, lean_box(0));
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_199_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_apply_1(v_f_187_, v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_f_187_);
v_a_200_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_190_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_190_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_00_u03b5_210_, lean_object* v_f_211_, lean_object* v_x_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_EIO_map(v_00_u03b1_208_, v_00_u03b2_209_, v_00_u03b5_210_, v_f_211_, v_x_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object* v_e_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_e_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object* v_e_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_EIO_throw___redArg(v_e_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw(lean_object* v_00_u03b5_221_, lean_object* v_00_u03b1_222_, lean_object* v_e_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_e_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object* v_00_u03b5_226_, lean_object* v_00_u03b1_227_, lean_object* v_e_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_EIO_throw(v_00_u03b5_226_, v_00_u03b1_227_, v_e_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object* v_x_231_, lean_object* v_handle_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_apply_1(v_x_231_, lean_box(0));
if (lean_obj_tag(v___x_234_) == 0)
{
lean_dec_ref(v_handle_232_);
return v___x_234_;
}
else
{
lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_234_);
v___x_236_ = lean_apply_2(v_handle_232_, v_a_235_, lean_box(0));
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object* v_x_237_, lean_object* v_handle_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_EIO_tryCatch___redArg(v_x_237_, v_handle_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object* v_00_u03b5_241_, lean_object* v_00_u03b1_242_, lean_object* v_x_243_, lean_object* v_handle_244_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_apply_1(v_x_243_, lean_box(0));
if (lean_obj_tag(v___x_246_) == 0)
{
lean_dec_ref(v_handle_244_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref(v___x_246_);
v___x_248_ = lean_apply_2(v_handle_244_, v_a_247_, lean_box(0));
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object* v_00_u03b5_249_, lean_object* v_00_u03b1_250_, lean_object* v_x_251_, lean_object* v_handle_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_EIO_tryCatch(v_00_u03b5_249_, v_00_u03b1_250_, v_x_251_, v_handle_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object* v_e_255_){
_start:
{
if (lean_obj_tag(v_e_255_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v_e_255_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_e_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v_e_255_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v_e_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_265_ = lean_ctor_get(v_e_255_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_e_255_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v_e_255_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v_e_255_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 0);
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object* v_e_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_EIO_ofExcept___redArg(v_e_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object* v_00_u03b5_276_, lean_object* v_00_u03b1_277_, lean_object* v_e_278_){
_start:
{
if (lean_obj_tag(v_e_278_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_a_280_ = lean_ctor_get(v_e_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_e_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v_e_278_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v_e_278_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 1);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_a_288_ = lean_ctor_get(v_e_278_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_e_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v_e_278_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v_e_278_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 0);
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object* v_00_u03b5_296_, lean_object* v_00_u03b1_297_, lean_object* v_e_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_EIO_ofExcept(v_00_u03b5_296_, v_00_u03b1_297_, v_e_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object* v_f_301_, lean_object* v_m_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_apply_1(v_m_302_, lean_box(0));
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_f_301_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_a_313_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v___x_304_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_304_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_apply_1(v_f_301_, v_a_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object* v_f_322_, lean_object* v_m_323_, lean_object* v_s_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_EIO_adapt___redArg(v_f_322_, v_m_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object* v_00_u03b5_326_, lean_object* v_00_u03b5_x27_327_, lean_object* v_00_u03b1_328_, lean_object* v_f_329_, lean_object* v_m_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_apply_1(v_m_330_, lean_box(0));
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_f_329_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v_a_341_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_349_ == 0)
{
v___x_343_ = v___x_332_;
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_332_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_apply_1(v_f_329_, v_a_341_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_345_);
v___x_347_ = v___x_343_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object* v_00_u03b5_350_, lean_object* v_00_u03b5_x27_351_, lean_object* v_00_u03b1_352_, lean_object* v_f_353_, lean_object* v_m_354_, lean_object* v_s_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_EIO_adapt(v_00_u03b5_350_, v_00_u03b5_x27_351_, v_00_u03b1_352_, v_f_353_, v_m_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object* v_f_357_, lean_object* v_m_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_apply_1(v_m_358_, lean_box(0));
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_f_357_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_a_369_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_377_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_apply_1(v_f_357_, v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object* v_f_378_, lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_EIO_adaptExcept___redArg(v_f_378_, v_m_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object* v_00_u03b5_382_, lean_object* v_00_u03b5_x27_383_, lean_object* v_00_u03b1_384_, lean_object* v_f_385_, lean_object* v_m_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_apply_1(v_m_386_, lean_box(0));
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_f_385_);
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_a_397_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v___x_388_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_388_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_apply_1(v_f_385_, v_a_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object* v_00_u03b5_406_, lean_object* v_00_u03b5_x27_407_, lean_object* v_00_u03b1_408_, lean_object* v_f_409_, lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_EIO_adaptExcept(v_00_u03b5_406_, v_00_u03b5_x27_407_, v_00_u03b1_408_, v_f_409_, v_m_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object* v_act_413_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_apply_1(v_act_413_, lean_box(0));
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object* v_act_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_BaseIO_toIO___redArg(v_act_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* v_00_u03b1_420_, lean_object* v_act_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_apply_1(v_act_421_, lean_box(0));
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object* v_00_u03b1_425_, lean_object* v_act_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_BaseIO_toIO(v_00_u03b1_425_, v_act_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object* v_f_429_, lean_object* v_act_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = lean_apply_1(v_act_430_, lean_box(0));
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v_f_429_);
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_apply_1(v_f_429_, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object* v_f_450_, lean_object* v_act_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_EIO_toIO___redArg(v_f_450_, v_act_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* v_00_u03b5_454_, lean_object* v_00_u03b1_455_, lean_object* v_f_456_, lean_object* v_act_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_apply_1(v_act_457_, lean_box(0));
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_f_456_);
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_476_; 
v_a_468_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_470_ = v___x_459_;
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_459_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_apply_1(v_f_456_, v_a_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_472_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object* v_00_u03b5_477_, lean_object* v_00_u03b1_478_, lean_object* v_f_479_, lean_object* v_act_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_EIO_toIO(v_00_u03b5_477_, v_00_u03b1_478_, v_f_479_, v_act_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object* v_act_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_apply_1(v_act_483_, lean_box(0));
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_494_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_a_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_a_495_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v___x_485_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_485_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_a_495_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 0);
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object* v_act_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_EIO_toIO_x27___redArg(v_act_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* v_00_u03b5_507_, lean_object* v_00_u03b1_508_, lean_object* v_act_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_apply_1(v_act_509_, lean_box(0));
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_a_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_a_521_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_529_ == 0)
{
v___x_523_ = v___x_511_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_511_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 0);
lean_ctor_set(v___x_523_, 0, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object* v_00_u03b5_530_, lean_object* v_00_u03b1_531_, lean_object* v_act_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_EIO_toIO_x27(v_00_u03b5_530_, v_00_u03b1_531_, v_act_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object* v_f_535_, lean_object* v_act_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_apply_1(v_act_536_, lean_box(0));
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_f_535_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_apply_1(v_f_535_, v_a_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object* v_f_556_, lean_object* v_act_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_IO_toEIO___redArg(v_f_556_, v_act_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* v_00_u03b5_560_, lean_object* v_00_u03b1_561_, lean_object* v_f_562_, lean_object* v_act_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_apply_1(v_act_563_, lean_box(0));
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_f_562_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
v_a_574_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v___x_565_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_565_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_apply_1(v_f_562_, v_a_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object* v_00_u03b5_583_, lean_object* v_00_u03b1_584_, lean_object* v_f_585_, lean_object* v_act_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_IO_toEIO(v_00_u03b5_583_, v_00_u03b1_584_, v_f_585_, v_act_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object* v_fn_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_apply_1(v_fn_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* v_00_u03b1_592_, lean_object* v_fn_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_unsafeBaseIO___redArg(v_fn_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object* v_fn_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_596_, 0, lean_box(0));
lean_closure_set(v___x_596_, 1, lean_box(0));
lean_closure_set(v___x_596_, 2, v_fn_595_);
v___x_597_ = l_unsafeBaseIO___redArg(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* v_00_u03b5_598_, lean_object* v_00_u03b1_599_, lean_object* v_fn_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_601_, 0, lean_box(0));
lean_closure_set(v___x_601_, 1, lean_box(0));
lean_closure_set(v___x_601_, 2, v_fn_600_);
v___x_602_ = l_unsafeBaseIO___redArg(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object* v_fn_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_604_, 0, lean_box(0));
lean_closure_set(v___x_604_, 1, lean_box(0));
lean_closure_set(v___x_604_, 2, v_fn_603_);
v___x_605_ = l_unsafeBaseIO___redArg(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* v_00_u03b1_606_, lean_object* v_fn_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_608_, 0, lean_box(0));
lean_closure_set(v___x_608_, 1, lean_box(0));
lean_closure_set(v___x_608_, 2, v_fn_607_);
v___x_609_ = l_unsafeBaseIO___redArg(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object* v_00_u03b1_614_, lean_object* v_msg_615_, lean_object* v_fn_616_, lean_object* v_a_00___x40___internal___hyg_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = lean_io_timeit(v_msg_615_, v_fn_616_);
lean_dec_ref(v_msg_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* v_00_u03b1_623_, lean_object* v_msg_624_, lean_object* v_fn_625_, lean_object* v_a_00___x40___internal___hyg_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = lean_io_allocprof(v_msg_624_, v_fn_625_);
lean_dec_ref(v_msg_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* v_a_00___x40___internal___hyg_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = lean_io_initializing();
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* v_00_u03b1_636_, lean_object* v_act_637_, lean_object* v_prio_638_, lean_object* v_a_00___x40___internal___hyg_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = lean_io_as_task(v_act_637_, v_prio_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_f_650_, lean_object* v_t_651_, lean_object* v_prio_652_, lean_object* v_sync_653_, lean_object* v_a_00___x40___internal___hyg_654_){
_start:
{
uint8_t v_sync_boxed_655_; lean_object* v_res_656_; 
v_sync_boxed_655_ = lean_unbox(v_sync_653_);
v_res_656_ = lean_io_map_task(v_f_650_, v_t_651_, v_prio_652_, v_sync_boxed_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_t_666_, lean_object* v_f_667_, lean_object* v_prio_668_, lean_object* v_sync_669_, lean_object* v_a_00___x40___internal___hyg_670_){
_start:
{
uint8_t v_sync_boxed_671_; lean_object* v_res_672_; 
v_sync_boxed_671_ = lean_unbox(v_sync_669_);
v_res_672_ = lean_io_bind_task(v_t_666_, v_f_667_, v_prio_668_, v_sync_boxed_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object* v_t_673_, lean_object* v_f_674_, lean_object* v_prio_675_, uint8_t v_sync_676_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_io_map_task(v_f_674_, v_t_673_, v_prio_675_, v_sync_676_);
lean_dec_ref(v___x_678_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object* v_t_680_, lean_object* v_f_681_, lean_object* v_prio_682_, lean_object* v_sync_683_, lean_object* v_a_684_){
_start:
{
uint8_t v_sync_boxed_685_; lean_object* v_res_686_; 
v_sync_boxed_685_ = lean_unbox(v_sync_683_);
v_res_686_ = l_BaseIO_chainTask___redArg(v_t_680_, v_f_681_, v_prio_682_, v_sync_boxed_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object* v_00_u03b1_687_, lean_object* v_t_688_, lean_object* v_f_689_, lean_object* v_prio_690_, uint8_t v_sync_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_BaseIO_chainTask___redArg(v_t_688_, v_f_689_, v_prio_690_, v_sync_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object* v_00_u03b1_694_, lean_object* v_t_695_, lean_object* v_f_696_, lean_object* v_prio_697_, lean_object* v_sync_698_, lean_object* v_a_699_){
_start:
{
uint8_t v_sync_boxed_700_; lean_object* v_res_701_; 
v_sync_boxed_700_ = lean_unbox(v_sync_698_);
v_res_701_ = l_BaseIO_chainTask(v_00_u03b1_694_, v_t_695_, v_f_696_, v_prio_697_, v_sync_boxed_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object* v_x_702_, lean_object* v_f_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_704_);
lean_ctor_set(v___x_706_, 1, v_x_702_);
v___x_707_ = l_List_reverse___redArg(v___x_706_);
v___x_708_ = lean_apply_2(v_f_703_, v___x_707_, lean_box(0));
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object* v_x_709_, lean_object* v_f_710_, lean_object* v_a_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(v_x_709_, v_f_710_, v_a_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object* v_x_714_, lean_object* v_f_715_, lean_object* v_prio_716_, lean_object* v_sync_717_, lean_object* v_tail_718_, lean_object* v_a_719_, lean_object* v___y_720_){
_start:
{
uint8_t v_sync_boxed_721_; lean_object* v_res_722_; 
v_sync_boxed_721_ = lean_unbox(v_sync_717_);
v_res_722_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(v_x_714_, v_f_715_, v_prio_716_, v_sync_boxed_721_, v_tail_718_, v_a_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object* v_f_723_, lean_object* v_prio_724_, uint8_t v_sync_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
if (v_sync_725_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = l_List_reverse___redArg(v_x_727_);
v___x_730_ = lean_apply_1(v_f_723_, v___x_729_);
v___x_731_ = lean_io_as_task(v___x_730_, v_prio_724_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v_prio_724_);
v___x_732_ = l_List_reverse___redArg(v_x_727_);
v___x_733_ = lean_apply_2(v_f_723_, v___x_732_, lean_box(0));
v___x_734_ = lean_task_pure(v___x_733_);
return v___x_734_;
}
}
else
{
lean_object* v_tail_735_; 
v_tail_735_ = lean_ctor_get(v_x_726_, 1);
if (lean_obj_tag(v_tail_735_) == 0)
{
lean_object* v_head_736_; lean_object* v___f_737_; lean_object* v___x_738_; 
v_head_736_ = lean_ctor_get(v_x_726_, 0);
lean_inc(v_head_736_);
lean_dec_ref(v_x_726_);
v___f_737_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_737_, 0, v_x_727_);
lean_closure_set(v___f_737_, 1, v_f_723_);
v___x_738_ = lean_io_map_task(v___f_737_, v_head_736_, v_prio_724_, v_sync_725_);
return v___x_738_;
}
else
{
lean_object* v_head_739_; lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___x_742_; 
lean_inc(v_tail_735_);
v_head_739_ = lean_ctor_get(v_x_726_, 0);
lean_inc(v_head_739_);
lean_dec_ref(v_x_726_);
v___x_740_ = lean_box(v_sync_725_);
lean_inc(v_prio_724_);
v___f_741_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_741_, 0, v_x_727_);
lean_closure_set(v___f_741_, 1, v_f_723_);
lean_closure_set(v___f_741_, 2, v_prio_724_);
lean_closure_set(v___f_741_, 3, v___x_740_);
lean_closure_set(v___f_741_, 4, v_tail_735_);
v___x_742_ = lean_io_bind_task(v_head_739_, v___f_741_, v_prio_724_, v_sync_725_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object* v_x_743_, lean_object* v_f_744_, lean_object* v_prio_745_, uint8_t v_sync_746_, lean_object* v_tail_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v_a_748_);
lean_ctor_set(v___x_750_, 1, v_x_743_);
v___x_751_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_744_, v_prio_745_, v_sync_746_, v_tail_747_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object* v_f_752_, lean_object* v_prio_753_, lean_object* v_sync_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_a_757_){
_start:
{
uint8_t v_sync_boxed_758_; lean_object* v_res_759_; 
v_sync_boxed_758_ = lean_unbox(v_sync_754_);
v_res_759_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_752_, v_prio_753_, v_sync_boxed_758_, v_x_755_, v_x_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_f_762_, lean_object* v_prio_763_, uint8_t v_sync_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_762_, v_prio_763_, v_sync_764_, v_x_765_, v_x_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_f_771_, lean_object* v_prio_772_, lean_object* v_sync_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_a_776_){
_start:
{
uint8_t v_sync_boxed_777_; lean_object* v_res_778_; 
v_sync_boxed_777_ = lean_unbox(v_sync_773_);
v_res_778_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go(v_00_u03b1_769_, v_00_u03b2_770_, v_f_771_, v_prio_772_, v_sync_boxed_777_, v_x_774_, v_x_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object* v_f_779_, lean_object* v_tasks_780_, lean_object* v_prio_781_, uint8_t v_sync_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_box(0);
v___x_785_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_779_, v_prio_781_, v_sync_782_, v_tasks_780_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object* v_f_786_, lean_object* v_tasks_787_, lean_object* v_prio_788_, lean_object* v_sync_789_, lean_object* v_a_790_){
_start:
{
uint8_t v_sync_boxed_791_; lean_object* v_res_792_; 
v_sync_boxed_791_ = lean_unbox(v_sync_789_);
v_res_792_ = l_BaseIO_mapTasks___redArg(v_f_786_, v_tasks_787_, v_prio_788_, v_sync_boxed_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* v_00_u03b1_793_, lean_object* v_00_u03b2_794_, lean_object* v_f_795_, lean_object* v_tasks_796_, lean_object* v_prio_797_, uint8_t v_sync_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_BaseIO_mapTasks___redArg(v_f_795_, v_tasks_796_, v_prio_797_, v_sync_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_f_803_, lean_object* v_tasks_804_, lean_object* v_prio_805_, lean_object* v_sync_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_sync_boxed_808_; lean_object* v_res_809_; 
v_sync_boxed_808_ = lean_unbox(v_sync_806_);
v_res_809_ = l_BaseIO_mapTasks(v_00_u03b1_801_, v_00_u03b2_802_, v_f_803_, v_tasks_804_, v_prio_805_, v_sync_boxed_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object* v_act_810_, lean_object* v_prio_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_813_, 0, lean_box(0));
lean_closure_set(v___x_813_, 1, lean_box(0));
lean_closure_set(v___x_813_, 2, v_act_810_);
v___x_814_ = lean_io_as_task(v___x_813_, v_prio_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object* v_act_815_, lean_object* v_prio_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_EIO_asTask___redArg(v_act_815_, v_prio_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* v_00_u03b5_819_, lean_object* v_00_u03b1_820_, lean_object* v_act_821_, lean_object* v_prio_822_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_824_, 0, lean_box(0));
lean_closure_set(v___x_824_, 1, lean_box(0));
lean_closure_set(v___x_824_, 2, v_act_821_);
v___x_825_ = lean_io_as_task(v___x_824_, v_prio_822_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object* v_00_u03b5_826_, lean_object* v_00_u03b1_827_, lean_object* v_act_828_, lean_object* v_prio_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_EIO_asTask(v_00_u03b5_826_, v_00_u03b1_827_, v_act_828_, v_prio_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object* v_f_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_apply_2(v_f_832_, v_a_833_, lean_box(0));
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_835_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_835_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object* v_f_852_, lean_object* v_a_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_EIO_mapTask___redArg___lam__0(v_f_852_, v_a_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object* v_f_856_, lean_object* v_t_857_, lean_object* v_prio_858_, uint8_t v_sync_859_){
_start:
{
lean_object* v___f_861_; lean_object* v___x_862_; 
v___f_861_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_861_, 0, v_f_856_);
v___x_862_ = lean_io_map_task(v___f_861_, v_t_857_, v_prio_858_, v_sync_859_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object* v_f_863_, lean_object* v_t_864_, lean_object* v_prio_865_, lean_object* v_sync_866_, lean_object* v_a_867_){
_start:
{
uint8_t v_sync_boxed_868_; lean_object* v_res_869_; 
v_sync_boxed_868_ = lean_unbox(v_sync_866_);
v_res_869_ = l_EIO_mapTask___redArg(v_f_863_, v_t_864_, v_prio_865_, v_sync_boxed_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b5_871_, lean_object* v_00_u03b2_872_, lean_object* v_f_873_, lean_object* v_t_874_, lean_object* v_prio_875_, uint8_t v_sync_876_){
_start:
{
lean_object* v___f_878_; lean_object* v___x_879_; 
v___f_878_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_878_, 0, v_f_873_);
v___x_879_ = lean_io_map_task(v___f_878_, v_t_874_, v_prio_875_, v_sync_876_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b5_881_, lean_object* v_00_u03b2_882_, lean_object* v_f_883_, lean_object* v_t_884_, lean_object* v_prio_885_, lean_object* v_sync_886_, lean_object* v_a_887_){
_start:
{
uint8_t v_sync_boxed_888_; lean_object* v_res_889_; 
v_sync_boxed_888_ = lean_unbox(v_sync_886_);
v_res_889_ = l_EIO_mapTask(v_00_u03b1_880_, v_00_u03b5_881_, v_00_u03b2_882_, v_f_883_, v_t_884_, v_prio_885_, v_sync_boxed_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object* v_f_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_2(v_f_890_, v_a_891_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
return v_a_894_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_a_895_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 0);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_task_pure(v___x_900_);
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object* v_f_904_, lean_object* v_a_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_EIO_bindTask___redArg___lam__0(v_f_904_, v_a_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object* v_t_908_, lean_object* v_f_909_, lean_object* v_prio_910_, uint8_t v_sync_911_){
_start:
{
lean_object* v___f_913_; lean_object* v___x_914_; 
v___f_913_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_913_, 0, v_f_909_);
v___x_914_ = lean_io_bind_task(v_t_908_, v___f_913_, v_prio_910_, v_sync_911_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object* v_t_915_, lean_object* v_f_916_, lean_object* v_prio_917_, lean_object* v_sync_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_sync_boxed_920_; lean_object* v_res_921_; 
v_sync_boxed_920_ = lean_unbox(v_sync_918_);
v_res_921_ = l_EIO_bindTask___redArg(v_t_915_, v_f_916_, v_prio_917_, v_sync_boxed_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b5_923_, lean_object* v_00_u03b2_924_, lean_object* v_t_925_, lean_object* v_f_926_, lean_object* v_prio_927_, uint8_t v_sync_928_){
_start:
{
lean_object* v___f_930_; lean_object* v___x_931_; 
v___f_930_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_930_, 0, v_f_926_);
v___x_931_ = lean_io_bind_task(v_t_925_, v___f_930_, v_prio_927_, v_sync_928_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b5_933_, lean_object* v_00_u03b2_934_, lean_object* v_t_935_, lean_object* v_f_936_, lean_object* v_prio_937_, lean_object* v_sync_938_, lean_object* v_a_939_){
_start:
{
uint8_t v_sync_boxed_940_; lean_object* v_res_941_; 
v_sync_boxed_940_ = lean_unbox(v_sync_938_);
v_res_941_ = l_EIO_bindTask(v_00_u03b1_932_, v_00_u03b5_933_, v_00_u03b2_934_, v_t_935_, v_f_936_, v_prio_937_, v_sync_boxed_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object* v_f_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_apply_2(v_f_942_, v_a_943_, lean_box(0));
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 1);
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_945_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_945_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 0);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object* v_f_962_, lean_object* v_a_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_EIO_chainTask___redArg___lam__0(v_f_962_, v_a_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object* v_t_966_, lean_object* v_f_967_, lean_object* v_prio_968_, uint8_t v_sync_969_){
_start:
{
lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___f_971_ = lean_alloc_closure((void*)(l_EIO_chainTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_971_, 0, v_f_967_);
v___x_972_ = lean_io_map_task(v___f_971_, v_t_966_, v_prio_968_, v_sync_969_);
lean_dec_ref(v___x_972_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object* v_t_975_, lean_object* v_f_976_, lean_object* v_prio_977_, lean_object* v_sync_978_, lean_object* v_a_979_){
_start:
{
uint8_t v_sync_boxed_980_; lean_object* v_res_981_; 
v_sync_boxed_980_ = lean_unbox(v_sync_978_);
v_res_981_ = l_EIO_chainTask___redArg(v_t_975_, v_f_976_, v_prio_977_, v_sync_boxed_980_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b5_983_, lean_object* v_t_984_, lean_object* v_f_985_, lean_object* v_prio_986_, uint8_t v_sync_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_EIO_chainTask___redArg(v_t_984_, v_f_985_, v_prio_986_, v_sync_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b5_991_, lean_object* v_t_992_, lean_object* v_f_993_, lean_object* v_prio_994_, lean_object* v_sync_995_, lean_object* v_a_996_){
_start:
{
uint8_t v_sync_boxed_997_; lean_object* v_res_998_; 
v_sync_boxed_997_ = lean_unbox(v_sync_995_);
v_res_998_ = l_EIO_chainTask(v_00_u03b1_990_, v_00_u03b5_991_, v_t_992_, v_f_993_, v_prio_994_, v_sync_boxed_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object* v_f_999_, lean_object* v_as_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_apply_2(v_f_999_, v_as_1000_, lean_box(0));
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 1);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 0);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_1019_, lean_object* v_as_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_EIO_mapTasks___redArg___lam__0(v_f_1019_, v_as_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object* v_f_1023_, lean_object* v_tasks_1024_, lean_object* v_prio_1025_, uint8_t v_sync_1026_){
_start:
{
lean_object* v___f_1028_; lean_object* v___x_1029_; 
v___f_1028_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1028_, 0, v_f_1023_);
v___x_1029_ = l_BaseIO_mapTasks___redArg(v___f_1028_, v_tasks_1024_, v_prio_1025_, v_sync_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object* v_f_1030_, lean_object* v_tasks_1031_, lean_object* v_prio_1032_, lean_object* v_sync_1033_, lean_object* v_a_1034_){
_start:
{
uint8_t v_sync_boxed_1035_; lean_object* v_res_1036_; 
v_sync_boxed_1035_ = lean_unbox(v_sync_1033_);
v_res_1036_ = l_EIO_mapTasks___redArg(v_f_1030_, v_tasks_1031_, v_prio_1032_, v_sync_boxed_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* v_00_u03b1_1037_, lean_object* v_00_u03b5_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_f_1040_, lean_object* v_tasks_1041_, lean_object* v_prio_1042_, uint8_t v_sync_1043_){
_start:
{
lean_object* v___f_1045_; lean_object* v___x_1046_; 
v___f_1045_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1045_, 0, v_f_1040_);
v___x_1046_ = l_BaseIO_mapTasks___redArg(v___f_1045_, v_tasks_1041_, v_prio_1042_, v_sync_1043_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b5_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_f_1050_, lean_object* v_tasks_1051_, lean_object* v_prio_1052_, lean_object* v_sync_1053_, lean_object* v_a_1054_){
_start:
{
uint8_t v_sync_boxed_1055_; lean_object* v_res_1056_; 
v_sync_boxed_1055_ = lean_unbox(v_sync_1053_);
v_res_1056_ = l_EIO_mapTasks(v_00_u03b1_1047_, v_00_u03b5_1048_, v_00_u03b2_1049_, v_f_1050_, v_tasks_1051_, v_prio_1052_, v_sync_boxed_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object* v_inst_1057_, lean_object* v_e_1058_){
_start:
{
if (lean_obj_tag(v_e_1058_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1069_; 
v_a_1060_ = lean_ctor_get(v_e_1058_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_e_1058_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1062_ = v_e_1058_;
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v_e_1058_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = lean_apply_1(v_inst_1057_, v_a_1060_);
v___x_1065_ = lean_mk_io_user_error(v___x_1064_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_inst_1057_);
v_a_1070_ = lean_ctor_get(v_e_1058_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_e_1058_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v_e_1058_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v_e_1058_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 0);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object* v_inst_1078_, lean_object* v_e_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_IO_ofExcept___redArg(v_inst_1078_, v_e_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* v_00_u03b5_1082_, lean_object* v_00_u03b1_1083_, lean_object* v_inst_1084_, lean_object* v_e_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_IO_ofExcept___redArg(v_inst_1084_, v_e_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object* v_00_u03b5_1088_, lean_object* v_00_u03b1_1089_, lean_object* v_inst_1090_, lean_object* v_e_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_IO_ofExcept(v_00_u03b5_1088_, v_00_u03b1_1089_, v_inst_1090_, v_e_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object* v_fn_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_apply_1(v_fn_1094_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object* v_fn_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_IO_lazyPure___redArg(v_fn_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* v_00_u03b1_1102_, lean_object* v_fn_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_IO_lazyPure___redArg(v_fn_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_fn_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_IO_lazyPure(v_00_u03b1_1106_, v_fn_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* v_a_00___x40___internal___hyg_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = lean_io_mono_ms_now();
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* v_a_00___x40___internal___hyg_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = lean_io_mono_nanos_now();
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* v_nBytes_1118_, lean_object* v_a_00___x40___internal___hyg_1119_){
_start:
{
size_t v_nBytes_boxed_1120_; lean_object* v_res_1121_; 
v_nBytes_boxed_1120_ = lean_unbox_usize(v_nBytes_1118_);
lean_dec(v_nBytes_1118_);
v_res_1121_ = lean_io_get_random_bytes(v_nBytes_boxed_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object* v_x_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object* v_s_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_IO_sleep___lam__0(v_x_1126_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t v_ms_1128_){
_start:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___f_1130_ = lean_alloc_closure((void*)(l_IO_sleep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1130_, 0, lean_box(0));
v___x_1131_ = lean_dbg_sleep(v_ms_1128_, v___f_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* v_ms_1132_, lean_object* v_s_1133_){
_start:
{
uint32_t v_ms_boxed_1134_; lean_object* v_res_1135_; 
v_ms_boxed_1134_ = lean_unbox_uint32(v_ms_1132_);
lean_dec(v_ms_1132_);
v_res_1135_ = l_IO_sleep(v_ms_boxed_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object* v_act_1136_, lean_object* v_prio_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1139_, 0, lean_box(0));
lean_closure_set(v___x_1139_, 1, lean_box(0));
lean_closure_set(v___x_1139_, 2, v_act_1136_);
v___x_1140_ = lean_io_as_task(v___x_1139_, v_prio_1137_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object* v_act_1141_, lean_object* v_prio_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_IO_asTask___redArg(v_act_1141_, v_prio_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* v_00_u03b1_1145_, lean_object* v_act_1146_, lean_object* v_prio_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1149_, 0, lean_box(0));
lean_closure_set(v___x_1149_, 1, lean_box(0));
lean_closure_set(v___x_1149_, 2, v_act_1146_);
v___x_1150_ = lean_io_as_task(v___x_1149_, v_prio_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object* v_00_u03b1_1151_, lean_object* v_act_1152_, lean_object* v_prio_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_IO_asTask(v_00_u03b1_1151_, v_act_1152_, v_prio_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object* v_f_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_apply_2(v_f_1156_, v_a_1157_, lean_box(0));
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 1);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_a_1168_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1159_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1159_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 0);
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object* v_f_1176_, lean_object* v_a_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_IO_mapTask___redArg___lam__0(v_f_1176_, v_a_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object* v_f_1180_, lean_object* v_t_1181_, lean_object* v_prio_1182_, uint8_t v_sync_1183_){
_start:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; 
v___f_1185_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1185_, 0, v_f_1180_);
v___x_1186_ = lean_io_map_task(v___f_1185_, v_t_1181_, v_prio_1182_, v_sync_1183_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object* v_f_1187_, lean_object* v_t_1188_, lean_object* v_prio_1189_, lean_object* v_sync_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_sync_boxed_1192_; lean_object* v_res_1193_; 
v_sync_boxed_1192_ = lean_unbox(v_sync_1190_);
v_res_1193_ = l_IO_mapTask___redArg(v_f_1187_, v_t_1188_, v_prio_1189_, v_sync_boxed_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_f_1196_, lean_object* v_t_1197_, lean_object* v_prio_1198_, uint8_t v_sync_1199_){
_start:
{
lean_object* v___f_1201_; lean_object* v___x_1202_; 
v___f_1201_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1201_, 0, v_f_1196_);
v___x_1202_ = lean_io_map_task(v___f_1201_, v_t_1197_, v_prio_1198_, v_sync_1199_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_f_1205_, lean_object* v_t_1206_, lean_object* v_prio_1207_, lean_object* v_sync_1208_, lean_object* v_a_1209_){
_start:
{
uint8_t v_sync_boxed_1210_; lean_object* v_res_1211_; 
v_sync_boxed_1210_ = lean_unbox(v_sync_1208_);
v_res_1211_ = l_IO_mapTask(v_00_u03b1_1203_, v_00_u03b2_1204_, v_f_1205_, v_t_1206_, v_prio_1207_, v_sync_boxed_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object* v_f_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_apply_2(v_f_1212_, v_a_1213_, lean_box(0));
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
return v_a_1216_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_a_1217_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1219_ = v___x_1215_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1215_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 0);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_task_pure(v___x_1222_);
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object* v_f_1226_, lean_object* v_a_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_IO_bindTask___redArg___lam__0(v_f_1226_, v_a_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object* v_t_1230_, lean_object* v_f_1231_, lean_object* v_prio_1232_, uint8_t v_sync_1233_){
_start:
{
lean_object* v___f_1235_; lean_object* v___x_1236_; 
v___f_1235_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1235_, 0, v_f_1231_);
v___x_1236_ = lean_io_bind_task(v_t_1230_, v___f_1235_, v_prio_1232_, v_sync_1233_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object* v_t_1237_, lean_object* v_f_1238_, lean_object* v_prio_1239_, lean_object* v_sync_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_sync_boxed_1242_; lean_object* v_res_1243_; 
v_sync_boxed_1242_ = lean_unbox(v_sync_1240_);
v_res_1243_ = l_IO_bindTask___redArg(v_t_1237_, v_f_1238_, v_prio_1239_, v_sync_boxed_1242_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* v_00_u03b1_1244_, lean_object* v_00_u03b2_1245_, lean_object* v_t_1246_, lean_object* v_f_1247_, lean_object* v_prio_1248_, uint8_t v_sync_1249_){
_start:
{
lean_object* v___f_1251_; lean_object* v___x_1252_; 
v___f_1251_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1251_, 0, v_f_1247_);
v___x_1252_ = lean_io_bind_task(v_t_1246_, v___f_1251_, v_prio_1248_, v_sync_1249_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_t_1255_, lean_object* v_f_1256_, lean_object* v_prio_1257_, lean_object* v_sync_1258_, lean_object* v_a_1259_){
_start:
{
uint8_t v_sync_boxed_1260_; lean_object* v_res_1261_; 
v_sync_boxed_1260_ = lean_unbox(v_sync_1258_);
v_res_1261_ = l_IO_bindTask(v_00_u03b1_1253_, v_00_u03b2_1254_, v_t_1255_, v_f_1256_, v_prio_1257_, v_sync_boxed_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object* v_t_1262_, lean_object* v_f_1263_, lean_object* v_prio_1264_, uint8_t v_sync_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_EIO_chainTask___redArg(v_t_1262_, v_f_1263_, v_prio_1264_, v_sync_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object* v_t_1268_, lean_object* v_f_1269_, lean_object* v_prio_1270_, lean_object* v_sync_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v_sync_boxed_1273_; lean_object* v_res_1274_; 
v_sync_boxed_1273_ = lean_unbox(v_sync_1271_);
v_res_1274_ = l_IO_chainTask___redArg(v_t_1268_, v_f_1269_, v_prio_1270_, v_sync_boxed_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object* v_00_u03b1_1275_, lean_object* v_t_1276_, lean_object* v_f_1277_, lean_object* v_prio_1278_, uint8_t v_sync_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_EIO_chainTask___redArg(v_t_1276_, v_f_1277_, v_prio_1278_, v_sync_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_t_1283_, lean_object* v_f_1284_, lean_object* v_prio_1285_, lean_object* v_sync_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v_sync_boxed_1288_; lean_object* v_res_1289_; 
v_sync_boxed_1288_ = lean_unbox(v_sync_1286_);
v_res_1289_ = l_IO_chainTask(v_00_u03b1_1282_, v_t_1283_, v_f_1284_, v_prio_1285_, v_sync_boxed_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object* v_f_1290_, lean_object* v_as_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_apply_2(v_f_1290_, v_as_1291_, lean_box(0));
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 1);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_a_1302_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1293_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1293_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 0);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_1310_, lean_object* v_as_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_IO_mapTasks___redArg___lam__0(v_f_1310_, v_as_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object* v_f_1314_, lean_object* v_tasks_1315_, lean_object* v_prio_1316_, uint8_t v_sync_1317_){
_start:
{
lean_object* v___f_1319_; lean_object* v___x_1320_; 
v___f_1319_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1319_, 0, v_f_1314_);
v___x_1320_ = l_BaseIO_mapTasks___redArg(v___f_1319_, v_tasks_1315_, v_prio_1316_, v_sync_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object* v_f_1321_, lean_object* v_tasks_1322_, lean_object* v_prio_1323_, lean_object* v_sync_1324_, lean_object* v_a_1325_){
_start:
{
uint8_t v_sync_boxed_1326_; lean_object* v_res_1327_; 
v_sync_boxed_1326_ = lean_unbox(v_sync_1324_);
v_res_1327_ = l_IO_mapTasks___redArg(v_f_1321_, v_tasks_1322_, v_prio_1323_, v_sync_boxed_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_f_1330_, lean_object* v_tasks_1331_, lean_object* v_prio_1332_, uint8_t v_sync_1333_){
_start:
{
lean_object* v___f_1335_; lean_object* v___x_1336_; 
v___f_1335_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1335_, 0, v_f_1330_);
v___x_1336_ = l_BaseIO_mapTasks___redArg(v___f_1335_, v_tasks_1331_, v_prio_1332_, v_sync_1333_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_f_1339_, lean_object* v_tasks_1340_, lean_object* v_prio_1341_, lean_object* v_sync_1342_, lean_object* v_a_1343_){
_start:
{
uint8_t v_sync_boxed_1344_; lean_object* v_res_1345_; 
v_sync_boxed_1344_ = lean_unbox(v_sync_1342_);
v_res_1345_ = l_IO_mapTasks(v_00_u03b1_1337_, v_00_u03b2_1338_, v_f_1339_, v_tasks_1340_, v_prio_1341_, v_sync_boxed_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* v_a_00___x40___internal___hyg_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = lean_io_check_canceled();
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_a_00___x40___internal___hyg_1354_, lean_object* v_a_00___x40___internal___hyg_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = lean_io_cancel(v_a_00___x40___internal___hyg_1354_);
lean_dec_ref(v_a_00___x40___internal___hyg_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx(uint8_t v_x_1357_){
_start:
{
switch(v_x_1357_)
{
case 0:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
return v___x_1358_;
}
case 1:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_unsigned_to_nat(1u);
return v___x_1359_;
}
default: 
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_unsigned_to_nat(2u);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___boxed(lean_object* v_x_1361_){
_start:
{
uint8_t v_x_boxed_1362_; lean_object* v_res_1363_; 
v_x_boxed_1362_ = lean_unbox(v_x_1361_);
v_res_1363_ = l_IO_TaskState_ctorIdx(v_x_boxed_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t v_x_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_IO_TaskState_ctorIdx(v_x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object* v_x_1366_){
_start:
{
uint8_t v_x_4__boxed_1367_; lean_object* v_res_1368_; 
v_x_4__boxed_1367_ = lean_unbox(v_x_1366_);
v_res_1368_ = l_IO_TaskState_toCtorIdx(v_x_4__boxed_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object* v_k_1369_){
_start:
{
lean_inc(v_k_1369_);
return v_k_1369_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object* v_k_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_IO_TaskState_ctorElim___redArg(v_k_1370_);
lean_dec(v_k_1370_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object* v_motive_1372_, lean_object* v_ctorIdx_1373_, uint8_t v_t_1374_, lean_object* v_h_1375_, lean_object* v_k_1376_){
_start:
{
lean_inc(v_k_1376_);
return v_k_1376_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object* v_motive_1377_, lean_object* v_ctorIdx_1378_, lean_object* v_t_1379_, lean_object* v_h_1380_, lean_object* v_k_1381_){
_start:
{
uint8_t v_t_boxed_1382_; lean_object* v_res_1383_; 
v_t_boxed_1382_ = lean_unbox(v_t_1379_);
v_res_1383_ = l_IO_TaskState_ctorElim(v_motive_1377_, v_ctorIdx_1378_, v_t_boxed_1382_, v_h_1380_, v_k_1381_);
lean_dec(v_k_1381_);
lean_dec(v_ctorIdx_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object* v_waiting_1384_){
_start:
{
lean_inc(v_waiting_1384_);
return v_waiting_1384_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object* v_waiting_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_IO_TaskState_waiting_elim___redArg(v_waiting_1385_);
lean_dec(v_waiting_1385_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object* v_motive_1387_, uint8_t v_t_1388_, lean_object* v_h_1389_, lean_object* v_waiting_1390_){
_start:
{
lean_inc(v_waiting_1390_);
return v_waiting_1390_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object* v_motive_1391_, lean_object* v_t_1392_, lean_object* v_h_1393_, lean_object* v_waiting_1394_){
_start:
{
uint8_t v_t_boxed_1395_; lean_object* v_res_1396_; 
v_t_boxed_1395_ = lean_unbox(v_t_1392_);
v_res_1396_ = l_IO_TaskState_waiting_elim(v_motive_1391_, v_t_boxed_1395_, v_h_1393_, v_waiting_1394_);
lean_dec(v_waiting_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object* v_running_1397_){
_start:
{
lean_inc(v_running_1397_);
return v_running_1397_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object* v_running_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_IO_TaskState_running_elim___redArg(v_running_1398_);
lean_dec(v_running_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object* v_motive_1400_, uint8_t v_t_1401_, lean_object* v_h_1402_, lean_object* v_running_1403_){
_start:
{
lean_inc(v_running_1403_);
return v_running_1403_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object* v_motive_1404_, lean_object* v_t_1405_, lean_object* v_h_1406_, lean_object* v_running_1407_){
_start:
{
uint8_t v_t_boxed_1408_; lean_object* v_res_1409_; 
v_t_boxed_1408_ = lean_unbox(v_t_1405_);
v_res_1409_ = l_IO_TaskState_running_elim(v_motive_1404_, v_t_boxed_1408_, v_h_1406_, v_running_1407_);
lean_dec(v_running_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object* v_finished_1410_){
_start:
{
lean_inc(v_finished_1410_);
return v_finished_1410_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object* v_finished_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_IO_TaskState_finished_elim___redArg(v_finished_1411_);
lean_dec(v_finished_1411_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object* v_motive_1413_, uint8_t v_t_1414_, lean_object* v_h_1415_, lean_object* v_finished_1416_){
_start:
{
lean_inc(v_finished_1416_);
return v_finished_1416_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object* v_motive_1417_, lean_object* v_t_1418_, lean_object* v_h_1419_, lean_object* v_finished_1420_){
_start:
{
uint8_t v_t_boxed_1421_; lean_object* v_res_1422_; 
v_t_boxed_1421_ = lean_unbox(v_t_1418_);
v_res_1422_ = l_IO_TaskState_finished_elim(v_motive_1417_, v_t_boxed_1421_, v_h_1419_, v_finished_1420_);
lean_dec(v_finished_1420_);
return v_res_1422_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState_default(void){
_start:
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
return v___x_1423_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState(void){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = 0;
return v___x_1424_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__6(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(2u);
v___x_1435_ = lean_nat_to_int(v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__7(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_to_int(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t v_x_1438_, lean_object* v_prec_1439_){
_start:
{
lean_object* v___y_1441_; lean_object* v___y_1448_; lean_object* v___y_1455_; 
switch(v_x_1438_)
{
case 0:
{
lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = lean_unsigned_to_nat(1024u);
v___x_1462_ = lean_nat_dec_le(v___x_1461_, v_prec_1439_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_1441_ = v___x_1463_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_1441_ = v___x_1464_;
goto v___jp_1440_;
}
}
case 1:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_unsigned_to_nat(1024u);
v___x_1466_ = lean_nat_dec_le(v___x_1465_, v_prec_1439_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_1448_ = v___x_1467_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_1448_ = v___x_1468_;
goto v___jp_1447_;
}
}
default: 
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = lean_unsigned_to_nat(1024u);
v___x_1470_ = lean_nat_dec_le(v___x_1469_, v_prec_1439_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_1455_ = v___x_1471_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_1455_ = v___x_1472_;
goto v___jp_1454_;
}
}
}
v___jp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1442_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__1));
v___x_1443_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = 0;
v___x_1445_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*1, v___x_1444_);
v___x_1446_ = l_Repr_addAppParen(v___x_1445_, v_prec_1439_);
return v___x_1446_;
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1449_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__3));
v___x_1450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = 0;
v___x_1452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*1, v___x_1451_);
v___x_1453_ = l_Repr_addAppParen(v___x_1452_, v_prec_1439_);
return v___x_1453_;
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1456_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__5));
v___x_1457_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = 0;
v___x_1459_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*1, v___x_1458_);
v___x_1460_ = l_Repr_addAppParen(v___x_1459_, v_prec_1439_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object* v_x_1473_, lean_object* v_prec_1474_){
_start:
{
uint8_t v_x_177__boxed_1475_; lean_object* v_res_1476_; 
v_x_177__boxed_1475_ = lean_unbox(v_x_1473_);
v_res_1476_ = l_IO_instReprTaskState_repr(v_x_177__boxed_1475_, v_prec_1474_);
lean_dec(v_prec_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object* v_n_1479_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_nat_dec_le(v_n_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_dec_le(v_n_1479_, v___x_1482_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; 
v___x_1484_ = 2;
return v___x_1484_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
return v___x_1485_;
}
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object* v_n_1487_){
_start:
{
uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_res_1488_ = l_IO_TaskState_ofNat(v_n_1487_);
lean_dec(v_n_1487_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t v_x_1490_, uint8_t v_y_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = l_IO_TaskState_ctorIdx(v_x_1490_);
v___x_1493_ = l_IO_TaskState_ctorIdx(v_y_1491_);
v___x_1494_ = lean_nat_dec_eq(v___x_1492_, v___x_1493_);
lean_dec(v___x_1493_);
lean_dec(v___x_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object* v_x_1495_, lean_object* v_y_1496_){
_start:
{
uint8_t v_x_13__boxed_1497_; uint8_t v_y_14__boxed_1498_; uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_x_13__boxed_1497_ = lean_unbox(v_x_1495_);
v_y_14__boxed_1498_ = lean_unbox(v_y_1496_);
v_res_1499_ = l_IO_instDecidableEqTaskState(v_x_13__boxed_1497_, v_y_14__boxed_1498_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t v_x_1501_, uint8_t v_y_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1503_ = l_IO_TaskState_ctorIdx(v_x_1501_);
v___x_1504_ = l_IO_TaskState_ctorIdx(v_y_1502_);
v___x_1505_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_nat_dec_eq(v___x_1503_, v___x_1504_);
lean_dec(v___x_1504_);
lean_dec(v___x_1503_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; 
v___x_1507_ = 2;
return v___x_1507_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = 1;
return v___x_1508_;
}
}
else
{
uint8_t v___x_1509_; 
lean_dec(v___x_1504_);
lean_dec(v___x_1503_);
v___x_1509_ = 0;
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object* v_x_1510_, lean_object* v_y_1511_){
_start:
{
uint8_t v_x_30__boxed_1512_; uint8_t v_y_31__boxed_1513_; uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_x_30__boxed_1512_ = lean_unbox(v_x_1510_);
v_y_31__boxed_1513_ = lean_unbox(v_y_1511_);
v_res_1514_ = l_IO_instOrdTaskState_ord(v_x_30__boxed_1512_, v_y_31__boxed_1513_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
static lean_object* _init_l_IO_instLTTaskState(void){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_box(0);
return v___x_1518_;
}
}
static lean_object* _init_l_IO_instLETaskState(void){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_box(0);
return v___x_1519_;
}
}
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t v_x_1520_, uint8_t v_y_1521_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = l_IO_instOrdTaskState_ord(v_x_1520_, v_y_1521_);
if (v___x_1522_ == 2)
{
return v_y_1521_;
}
else
{
return v_x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* v_x_1523_, lean_object* v_y_1524_){
_start:
{
uint8_t v_x_boxed_1525_; uint8_t v_y_boxed_1526_; uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_x_boxed_1525_ = lean_unbox(v_x_1523_);
v_y_boxed_1526_ = lean_unbox(v_y_1524_);
v_res_1527_ = l_IO_instMinTaskState___lam__0(v_x_boxed_1525_, v_y_boxed_1526_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t v_x_1531_, uint8_t v_y_1532_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = l_IO_instOrdTaskState_ord(v_x_1531_, v_y_1532_);
if (v___x_1533_ == 2)
{
return v_x_1531_;
}
else
{
return v_y_1532_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* v_x_1534_, lean_object* v_y_1535_){
_start:
{
uint8_t v_x_boxed_1536_; uint8_t v_y_boxed_1537_; uint8_t v_res_1538_; lean_object* v_r_1539_; 
v_x_boxed_1536_ = lean_unbox(v_x_1534_);
v_y_boxed_1537_ = lean_unbox(v_y_1535_);
v_res_1538_ = l_IO_instMaxTaskState___lam__0(v_x_boxed_1536_, v_y_boxed_1537_);
v_r_1539_ = lean_box(v_res_1538_);
return v_r_1539_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t v_x_1545_){
_start:
{
switch(v_x_1545_)
{
case 0:
{
lean_object* v___x_1546_; 
v___x_1546_ = ((lean_object*)(l_IO_TaskState_toString___closed__0));
return v___x_1546_;
}
case 1:
{
lean_object* v___x_1547_; 
v___x_1547_ = ((lean_object*)(l_IO_TaskState_toString___closed__1));
return v___x_1547_;
}
default: 
{
lean_object* v___x_1548_; 
v___x_1548_ = ((lean_object*)(l_IO_TaskState_toString___closed__2));
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object* v_x_1549_){
_start:
{
uint8_t v_x_31__boxed_1550_; lean_object* v_res_1551_; 
v_x_31__boxed_1550_ = lean_unbox(v_x_1549_);
v_res_1551_ = l_IO_TaskState_toString(v_x_31__boxed_1550_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_a_00___x40___internal___hyg_1558_, lean_object* v_a_00___x40___internal___hyg_1559_){
_start:
{
uint8_t v_res_1560_; lean_object* v_r_1561_; 
v_res_1560_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_1558_);
lean_dec_ref(v_a_00___x40___internal___hyg_1558_);
v_r_1561_ = lean_box(v_res_1560_);
return v_r_1561_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object* v_task_1562_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_io_get_task_state(v_task_1562_);
if (v___x_1564_ == 2)
{
uint8_t v___x_1565_; 
v___x_1565_ = 1;
return v___x_1565_;
}
else
{
uint8_t v___x_1566_; 
v___x_1566_ = 0;
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* v_task_1567_, lean_object* v_a_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_IO_hasFinished___redArg(v_task_1567_);
lean_dec_ref(v_task_1567_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object* v_00_u03b1_1571_, lean_object* v_task_1572_){
_start:
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_io_get_task_state(v_task_1572_);
if (v___x_1574_ == 2)
{
uint8_t v___x_1575_; 
v___x_1575_ = 1;
return v___x_1575_;
}
else
{
uint8_t v___x_1576_; 
v___x_1576_ = 0;
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_task_1578_, lean_object* v_a_1579_){
_start:
{
uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_res_1580_ = l_IO_hasFinished(v_00_u03b1_1577_, v_task_1578_);
lean_dec_ref(v_task_1578_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_t_1586_, lean_object* v_a_00___x40___internal___hyg_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = lean_io_wait(v_t_1586_);
return v_res_1588_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__10));
v___x_1616_ = l_Lean_mkAtom(v___x_1615_);
return v___x_1616_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__12, &l_IO_waitAny___auto__1___closed__12_once, _init_l_IO_waitAny___auto__1___closed__12);
v___x_1618_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1619_ = lean_array_push(v___x_1618_, v___x_1617_);
return v___x_1619_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__18(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__17));
v___x_1629_ = lean_string_utf8_byte_size(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__19(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1630_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__18, &l_IO_waitAny___auto__1___closed__18_once, _init_l_IO_waitAny___auto__1___closed__18);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__17));
v___x_1633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___x_1631_);
lean_ctor_set(v___x_1633_, 2, v___x_1630_);
return v___x_1633_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1639_ = lean_box(0);
v___x_1640_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__22));
v___x_1641_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__19, &l_IO_waitAny___auto__1___closed__19_once, _init_l_IO_waitAny___auto__1___closed__19);
v___x_1642_ = lean_box(2);
v___x_1643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___x_1641_);
lean_ctor_set(v___x_1643_, 2, v___x_1640_);
lean_ctor_set(v___x_1643_, 3, v___x_1639_);
return v___x_1643_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__24(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__23, &l_IO_waitAny___auto__1___closed__23_once, _init_l_IO_waitAny___auto__1___closed__23);
v___x_1645_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1646_ = lean_array_push(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__27));
v___x_1655_ = l_Lean_mkAtom(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__28, &l_IO_waitAny___auto__1___closed__28_once, _init_l_IO_waitAny___auto__1___closed__28);
v___x_1657_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1658_ = lean_array_push(v___x_1657_, v___x_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__29, &l_IO_waitAny___auto__1___closed__29_once, _init_l_IO_waitAny___auto__1___closed__29);
v___x_1660_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__26));
v___x_1661_ = lean_box(2);
v___x_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v___x_1660_);
lean_ctor_set(v___x_1662_, 2, v___x_1659_);
return v___x_1662_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__30, &l_IO_waitAny___auto__1___closed__30_once, _init_l_IO_waitAny___auto__1___closed__30);
v___x_1664_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1665_ = lean_array_push(v___x_1664_, v___x_1663_);
return v___x_1665_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1666_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__31, &l_IO_waitAny___auto__1___closed__31_once, _init_l_IO_waitAny___auto__1___closed__31);
v___x_1667_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_1668_ = lean_box(2);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1667_);
lean_ctor_set(v___x_1669_, 2, v___x_1666_);
return v___x_1669_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__32, &l_IO_waitAny___auto__1___closed__32_once, _init_l_IO_waitAny___auto__1___closed__32);
v___x_1671_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__24, &l_IO_waitAny___auto__1___closed__24_once, _init_l_IO_waitAny___auto__1___closed__24);
v___x_1672_ = lean_array_push(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__33, &l_IO_waitAny___auto__1___closed__33_once, _init_l_IO_waitAny___auto__1___closed__33);
v___x_1674_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_1675_ = lean_box(2);
v___x_1676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
lean_ctor_set(v___x_1676_, 2, v___x_1673_);
return v___x_1676_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__34, &l_IO_waitAny___auto__1___closed__34_once, _init_l_IO_waitAny___auto__1___closed__34);
v___x_1678_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__13, &l_IO_waitAny___auto__1___closed__13_once, _init_l_IO_waitAny___auto__1___closed__13);
v___x_1679_ = lean_array_push(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__35, &l_IO_waitAny___auto__1___closed__35_once, _init_l_IO_waitAny___auto__1___closed__35);
v___x_1681_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__11));
v___x_1682_ = lean_box(2);
v___x_1683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
lean_ctor_set(v___x_1683_, 2, v___x_1680_);
return v___x_1683_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__36, &l_IO_waitAny___auto__1___closed__36_once, _init_l_IO_waitAny___auto__1___closed__36);
v___x_1685_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1686_ = lean_array_push(v___x_1685_, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1687_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__37, &l_IO_waitAny___auto__1___closed__37_once, _init_l_IO_waitAny___auto__1___closed__37);
v___x_1688_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_1689_ = lean_box(2);
v___x_1690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___x_1688_);
lean_ctor_set(v___x_1690_, 2, v___x_1687_);
return v___x_1690_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__38, &l_IO_waitAny___auto__1___closed__38_once, _init_l_IO_waitAny___auto__1___closed__38);
v___x_1692_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1693_ = lean_array_push(v___x_1692_, v___x_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__39, &l_IO_waitAny___auto__1___closed__39_once, _init_l_IO_waitAny___auto__1___closed__39);
v___x_1695_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__7));
v___x_1696_ = lean_box(2);
v___x_1697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v___x_1694_);
return v___x_1697_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__40, &l_IO_waitAny___auto__1___closed__40_once, _init_l_IO_waitAny___auto__1___closed__40);
v___x_1699_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_1700_ = lean_array_push(v___x_1699_, v___x_1698_);
return v___x_1700_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__42(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1701_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
v___x_1702_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__4));
v___x_1703_ = lean_box(2);
v___x_1704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v___x_1702_);
lean_ctor_set(v___x_1704_, 2, v___x_1701_);
return v___x_1704_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1(void){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__42, &l_IO_waitAny___auto__1___closed__42_once, _init_l_IO_waitAny___auto__1___closed__42);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* v_00_u03b1_1710_, lean_object* v_tasks_1711_, lean_object* v_h_1712_, lean_object* v_a_00___x40___internal___hyg_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = lean_io_wait_any(v_tasks_1711_);
lean_dec(v_tasks_1711_);
return v_res_1714_;
}
}
static lean_object* _init_l_IO_waitAny_x27___auto__1(void){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__42, &l_IO_waitAny___auto__1___closed__42_once, _init_l_IO_waitAny___auto__1___closed__42);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object* v___x_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v_a_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
if (lean_obj_tag(v_a_1719_) == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_array_to_list(v_a_1720_);
return v___x_1721_;
}
else
{
lean_object* v_head_1722_; lean_object* v_tail_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_head_1722_ = lean_ctor_get(v_a_1719_, 0);
lean_inc(v_head_1722_);
v_tail_1723_ = lean_ctor_get(v_a_1719_, 1);
lean_inc(v_tail_1723_);
lean_dec_ref(v_a_1719_);
v___x_1724_ = lean_array_get_size(v_a_1720_);
v___f_1725_ = lean_alloc_closure((void*)(l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1725_, 0, v___x_1724_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = 1;
v___x_1728_ = lean_task_map(v___f_1725_, v_head_1722_, v___x_1726_, v___x_1727_);
v___x_1729_ = lean_array_push(v_a_1720_, v___x_1728_);
v_a_1719_ = v_tail_1723_;
v_a_1720_ = v___x_1729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object* v_tasks_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1747_; 
v___x_1735_ = ((lean_object*)(l_IO_waitAny_x27___redArg___closed__0));
lean_inc(v_tasks_1733_);
v___x_1736_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_tasks_1733_, v___x_1735_);
v___x_1737_ = lean_io_wait_any(v___x_1736_);
lean_dec(v___x_1736_);
v_fst_1738_ = lean_ctor_get(v___x_1737_, 0);
v_snd_1739_ = lean_ctor_get(v___x_1737_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_inc(v_fst_1738_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_inc(v_tasks_1733_);
v___x_1743_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), v_tasks_1733_, v_tasks_1733_, v_fst_1738_, v___x_1735_);
lean_dec(v_tasks_1733_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 1, v___x_1743_);
lean_ctor_set(v___x_1741_, 0, v_snd_1739_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_snd_1739_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object* v_tasks_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_IO_waitAny_x27___redArg(v_tasks_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object* v_00_u03b1_1751_, lean_object* v_tasks_1752_, lean_object* v_h_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_IO_waitAny_x27___redArg(v_tasks_1752_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_tasks_1757_, lean_object* v_h_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_IO_waitAny_x27(v_00_u03b1_1756_, v_tasks_1757_, v_h_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object* v_00_u03b1_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_a_1762_, v_a_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* v_a_00___x40___internal___hyg_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = lean_io_get_num_heartbeats();
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* v_count_1770_, lean_object* v_a_00___x40___internal___hyg_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = lean_io_set_heartbeats(v_count_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object* v_count_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_io_get_num_heartbeats();
v___x_1776_ = lean_nat_add(v___x_1775_, v_count_1773_);
lean_dec(v___x_1775_);
v___x_1777_ = lean_io_set_heartbeats(v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* v_count_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_IO_addHeartbeats(v_count_1778_);
lean_dec(v_count_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t v_x_1781_){
_start:
{
switch(v_x_1781_)
{
case 0:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_unsigned_to_nat(0u);
return v___x_1782_;
}
case 1:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_unsigned_to_nat(1u);
return v___x_1783_;
}
case 2:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_unsigned_to_nat(2u);
return v___x_1784_;
}
case 3:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_unsigned_to_nat(3u);
return v___x_1785_;
}
default: 
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_unsigned_to_nat(4u);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object* v_x_1787_){
_start:
{
uint8_t v_x_boxed_1788_; lean_object* v_res_1789_; 
v_x_boxed_1788_ = lean_unbox(v_x_1787_);
v_res_1789_ = l_IO_FS_Mode_ctorIdx(v_x_boxed_1788_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t v_x_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_IO_FS_Mode_ctorIdx(v_x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object* v_x_1792_){
_start:
{
uint8_t v_x_4__boxed_1793_; lean_object* v_res_1794_; 
v_x_4__boxed_1793_ = lean_unbox(v_x_1792_);
v_res_1794_ = l_IO_FS_Mode_toCtorIdx(v_x_4__boxed_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object* v_k_1795_){
_start:
{
lean_inc(v_k_1795_);
return v_k_1795_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object* v_k_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_IO_FS_Mode_ctorElim___redArg(v_k_1796_);
lean_dec(v_k_1796_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object* v_motive_1798_, lean_object* v_ctorIdx_1799_, uint8_t v_t_1800_, lean_object* v_h_1801_, lean_object* v_k_1802_){
_start:
{
lean_inc(v_k_1802_);
return v_k_1802_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object* v_motive_1803_, lean_object* v_ctorIdx_1804_, lean_object* v_t_1805_, lean_object* v_h_1806_, lean_object* v_k_1807_){
_start:
{
uint8_t v_t_boxed_1808_; lean_object* v_res_1809_; 
v_t_boxed_1808_ = lean_unbox(v_t_1805_);
v_res_1809_ = l_IO_FS_Mode_ctorElim(v_motive_1803_, v_ctorIdx_1804_, v_t_boxed_1808_, v_h_1806_, v_k_1807_);
lean_dec(v_k_1807_);
lean_dec(v_ctorIdx_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object* v_read_1810_){
_start:
{
lean_inc(v_read_1810_);
return v_read_1810_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object* v_read_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_IO_FS_Mode_read_elim___redArg(v_read_1811_);
lean_dec(v_read_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object* v_motive_1813_, uint8_t v_t_1814_, lean_object* v_h_1815_, lean_object* v_read_1816_){
_start:
{
lean_inc(v_read_1816_);
return v_read_1816_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object* v_motive_1817_, lean_object* v_t_1818_, lean_object* v_h_1819_, lean_object* v_read_1820_){
_start:
{
uint8_t v_t_boxed_1821_; lean_object* v_res_1822_; 
v_t_boxed_1821_ = lean_unbox(v_t_1818_);
v_res_1822_ = l_IO_FS_Mode_read_elim(v_motive_1817_, v_t_boxed_1821_, v_h_1819_, v_read_1820_);
lean_dec(v_read_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object* v_write_1823_){
_start:
{
lean_inc(v_write_1823_);
return v_write_1823_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object* v_write_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_IO_FS_Mode_write_elim___redArg(v_write_1824_);
lean_dec(v_write_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object* v_motive_1826_, uint8_t v_t_1827_, lean_object* v_h_1828_, lean_object* v_write_1829_){
_start:
{
lean_inc(v_write_1829_);
return v_write_1829_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object* v_motive_1830_, lean_object* v_t_1831_, lean_object* v_h_1832_, lean_object* v_write_1833_){
_start:
{
uint8_t v_t_boxed_1834_; lean_object* v_res_1835_; 
v_t_boxed_1834_ = lean_unbox(v_t_1831_);
v_res_1835_ = l_IO_FS_Mode_write_elim(v_motive_1830_, v_t_boxed_1834_, v_h_1832_, v_write_1833_);
lean_dec(v_write_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object* v_writeNew_1836_){
_start:
{
lean_inc(v_writeNew_1836_);
return v_writeNew_1836_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object* v_writeNew_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_IO_FS_Mode_writeNew_elim___redArg(v_writeNew_1837_);
lean_dec(v_writeNew_1837_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object* v_motive_1839_, uint8_t v_t_1840_, lean_object* v_h_1841_, lean_object* v_writeNew_1842_){
_start:
{
lean_inc(v_writeNew_1842_);
return v_writeNew_1842_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object* v_motive_1843_, lean_object* v_t_1844_, lean_object* v_h_1845_, lean_object* v_writeNew_1846_){
_start:
{
uint8_t v_t_boxed_1847_; lean_object* v_res_1848_; 
v_t_boxed_1847_ = lean_unbox(v_t_1844_);
v_res_1848_ = l_IO_FS_Mode_writeNew_elim(v_motive_1843_, v_t_boxed_1847_, v_h_1845_, v_writeNew_1846_);
lean_dec(v_writeNew_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object* v_readWrite_1849_){
_start:
{
lean_inc(v_readWrite_1849_);
return v_readWrite_1849_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object* v_readWrite_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_IO_FS_Mode_readWrite_elim___redArg(v_readWrite_1850_);
lean_dec(v_readWrite_1850_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object* v_motive_1852_, uint8_t v_t_1853_, lean_object* v_h_1854_, lean_object* v_readWrite_1855_){
_start:
{
lean_inc(v_readWrite_1855_);
return v_readWrite_1855_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object* v_motive_1856_, lean_object* v_t_1857_, lean_object* v_h_1858_, lean_object* v_readWrite_1859_){
_start:
{
uint8_t v_t_boxed_1860_; lean_object* v_res_1861_; 
v_t_boxed_1860_ = lean_unbox(v_t_1857_);
v_res_1861_ = l_IO_FS_Mode_readWrite_elim(v_motive_1856_, v_t_boxed_1860_, v_h_1858_, v_readWrite_1859_);
lean_dec(v_readWrite_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object* v_append_1862_){
_start:
{
lean_inc(v_append_1862_);
return v_append_1862_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object* v_append_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_IO_FS_Mode_append_elim___redArg(v_append_1863_);
lean_dec(v_append_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object* v_motive_1865_, uint8_t v_t_1866_, lean_object* v_h_1867_, lean_object* v_append_1868_){
_start:
{
lean_inc(v_append_1868_);
return v_append_1868_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object* v_motive_1869_, lean_object* v_t_1870_, lean_object* v_h_1871_, lean_object* v_append_1872_){
_start:
{
uint8_t v_t_boxed_1873_; lean_object* v_res_1874_; 
v_t_boxed_1873_ = lean_unbox(v_t_1870_);
v_res_1874_ = l_IO_FS_Mode_append_elim(v_motive_1869_, v_t_boxed_1873_, v_h_1871_, v_append_1872_);
lean_dec(v_append_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0(){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object* v_s_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_IO_FS_instInhabitedStream_default___lam__0();
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(size_t v_x_1883_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object* v_x_1887_, lean_object* v___y_1888_){
_start:
{
size_t v_x_207__boxed_1889_; lean_object* v_res_1890_; 
v_x_207__boxed_1889_ = lean_unbox_usize(v_x_1887_);
lean_dec(v_x_1887_);
v_res_1890_ = l_IO_FS_instInhabitedStream_default___lam__1(v_x_207__boxed_1889_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object* v_x_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_1895_);
lean_dec_ref(v_x_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3(){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object* v_s_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_IO_FS_instInhabitedStream_default___lam__3();
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(lean_object* v_x_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object* v_x_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_1907_);
lean_dec_ref(v_x_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t v___x_1910_){
_start:
{
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object* v___x_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v___x_254__boxed_1914_; uint8_t v_res_1915_; lean_object* v_r_1916_; 
v___x_254__boxed_1914_ = lean_unbox(v___x_1912_);
v_res_1915_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_254__boxed_1914_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* v_a_00___x40___internal___hyg_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = lean_get_stdin();
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* v_a_00___x40___internal___hyg_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = lean_get_stdout();
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* v_a_00___x40___internal___hyg_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = lean_get_stderr();
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* v_a_00___x40___internal___hyg_1945_, lean_object* v_a_00___x40___internal___hyg_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* v_a_00___x40___internal___hyg_1950_, lean_object* v_a_00___x40___internal___hyg_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* v_a_00___x40___internal___hyg_1955_, lean_object* v_a_00___x40___internal___hyg_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object* v_a_1958_, lean_object* v_f_1959_){
_start:
{
lean_object* v___x_1961_; 
lean_inc_ref(v_f_1959_);
v___x_1961_ = lean_apply_2(v_f_1959_, v_a_1958_, lean_box(0));
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1972_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1972_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1972_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
if (lean_obj_tag(v_a_1962_) == 0)
{
lean_object* v_val_1966_; 
lean_del_object(v___x_1964_);
v_val_1966_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_val_1966_);
lean_dec_ref(v_a_1962_);
v_a_1958_ = v_val_1966_;
goto _start;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1970_; 
lean_dec_ref(v_f_1959_);
v_val_1968_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_val_1968_);
lean_dec_ref(v_a_1962_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_val_1968_);
v___x_1970_ = v___x_1964_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_val_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_f_1959_);
v_a_1973_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1961_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1961_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object* v_a_1981_, lean_object* v_f_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_IO_iterate___redArg(v_a_1981_, v_f_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* v_00_u03b1_1985_, lean_object* v_00_u03b2_1986_, lean_object* v_a_1987_, lean_object* v_f_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_IO_iterate___redArg(v_a_1987_, v_f_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object* v_00_u03b1_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_a_1993_, lean_object* v_f_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_IO_iterate(v_00_u03b1_1991_, v_00_u03b2_1992_, v_a_1993_, v_f_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* v_fn_2000_, lean_object* v_mode_2001_, lean_object* v_a_00___x40___internal___hyg_2002_){
_start:
{
uint8_t v_mode_boxed_2003_; lean_object* v_res_2004_; 
v_mode_boxed_2003_ = lean_unbox(v_mode_2001_);
v_res_2004_ = lean_io_prim_handle_mk(v_fn_2000_, v_mode_boxed_2003_);
lean_dec_ref(v_fn_2000_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* v_h_2008_, lean_object* v_exclusive_2009_, lean_object* v_a_00___x40___internal___hyg_2010_){
_start:
{
uint8_t v_exclusive_boxed_2011_; lean_object* v_res_2012_; 
v_exclusive_boxed_2011_ = lean_unbox(v_exclusive_2009_);
v_res_2012_ = lean_io_prim_handle_lock(v_h_2008_, v_exclusive_boxed_2011_);
lean_dec(v_h_2008_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* v_h_2016_, lean_object* v_exclusive_2017_, lean_object* v_a_00___x40___internal___hyg_2018_){
_start:
{
uint8_t v_exclusive_boxed_2019_; lean_object* v_res_2020_; 
v_exclusive_boxed_2019_ = lean_unbox(v_exclusive_2017_);
v_res_2020_ = lean_io_prim_handle_try_lock(v_h_2016_, v_exclusive_boxed_2019_);
lean_dec(v_h_2016_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* v_h_2023_, lean_object* v_a_00___x40___internal___hyg_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = lean_io_prim_handle_unlock(v_h_2023_);
lean_dec(v_h_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* v_h_2028_, lean_object* v_a_00___x40___internal___hyg_2029_){
_start:
{
uint8_t v_res_2030_; lean_object* v_r_2031_; 
v_res_2030_ = lean_io_prim_handle_is_tty(v_h_2028_);
lean_dec(v_h_2028_);
v_r_2031_ = lean_box(v_res_2030_);
return v_r_2031_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* v_h_2034_, lean_object* v_a_00___x40___internal___hyg_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = lean_io_prim_handle_flush(v_h_2034_);
lean_dec(v_h_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* v_h_2039_, lean_object* v_a_00___x40___internal___hyg_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = lean_io_prim_handle_rewind(v_h_2039_);
lean_dec(v_h_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* v_h_2044_, lean_object* v_a_00___x40___internal___hyg_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = lean_io_prim_handle_truncate(v_h_2044_);
lean_dec(v_h_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* v_h_2050_, lean_object* v_bytes_2051_, lean_object* v_a_00___x40___internal___hyg_2052_){
_start:
{
size_t v_bytes_boxed_2053_; lean_object* v_res_2054_; 
v_bytes_boxed_2053_ = lean_unbox_usize(v_bytes_2051_);
lean_dec(v_bytes_2051_);
v_res_2054_ = lean_io_prim_handle_read(v_h_2050_, v_bytes_boxed_2053_);
lean_dec(v_h_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* v_h_2058_, lean_object* v_buffer_2059_, lean_object* v_a_00___x40___internal___hyg_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = lean_io_prim_handle_write(v_h_2058_, v_buffer_2059_);
lean_dec_ref(v_buffer_2059_);
lean_dec(v_h_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* v_h_2064_, lean_object* v_a_00___x40___internal___hyg_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = lean_io_prim_handle_get_line(v_h_2064_);
lean_dec(v_h_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* v_h_2070_, lean_object* v_s_2071_, lean_object* v_a_00___x40___internal___hyg_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = lean_io_prim_handle_put_str(v_h_2070_, v_s_2071_);
lean_dec_ref(v_s_2071_);
lean_dec(v_h_2070_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* v_fname_2076_, lean_object* v_a_00___x40___internal___hyg_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = lean_io_realpath(v_fname_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* v_fname_2081_, lean_object* v_a_00___x40___internal___hyg_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = lean_io_remove_file(v_fname_2081_);
lean_dec_ref(v_fname_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* v_a_00___x40___internal___hyg_2086_, lean_object* v_a_00___x40___internal___hyg_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_2086_);
lean_dec_ref(v_a_00___x40___internal___hyg_2086_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* v_a_00___x40___internal___hyg_2091_, lean_object* v_a_00___x40___internal___hyg_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = lean_io_create_dir(v_a_00___x40___internal___hyg_2091_);
lean_dec_ref(v_a_00___x40___internal___hyg_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* v_old_2097_, lean_object* v_new_2098_, lean_object* v_a_00___x40___internal___hyg_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = lean_io_rename(v_old_2097_, v_new_2098_);
lean_dec_ref(v_new_2098_);
lean_dec_ref(v_old_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object* v_orig_2104_, lean_object* v_link_2105_, lean_object* v_a_00___x40___internal___hyg_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = lean_io_hard_link(v_orig_2104_, v_link_2105_);
lean_dec_ref(v_link_2105_);
lean_dec_ref(v_orig_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* v_a_00___x40___internal___hyg_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = lean_io_create_tempfile();
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* v_a_00___x40___internal___hyg_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = lean_io_create_tempdir();
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* v_var_2116_, lean_object* v_a_00___x40___internal___hyg_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = lean_io_getenv(v_var_2116_);
lean_dec_ref(v_var_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* v_a_00___x40___internal___hyg_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = lean_io_app_path();
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* v_a_00___x40___internal___hyg_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = lean_io_current_dir();
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object* v_fn_2125_, uint8_t v_mode_2126_, lean_object* v_f_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_io_prim_handle_mk(v_fn_2125_, v_mode_2126_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = lean_apply_2(v_f_2127_, v_a_2130_, lean_box(0));
return v___x_2131_;
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_f_2127_);
v_a_2132_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2129_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2129_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* v_fn_2140_, lean_object* v_mode_2141_, lean_object* v_f_2142_, lean_object* v_a_2143_){
_start:
{
uint8_t v_mode_boxed_2144_; lean_object* v_res_2145_; 
v_mode_boxed_2144_ = lean_unbox(v_mode_2141_);
v_res_2145_ = l_IO_FS_withFile___redArg(v_fn_2140_, v_mode_boxed_2144_, v_f_2142_);
lean_dec_ref(v_fn_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* v_00_u03b1_2146_, lean_object* v_fn_2147_, uint8_t v_mode_2148_, lean_object* v_f_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = lean_io_prim_handle_mk(v_fn_2147_, v_mode_2148_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = lean_apply_2(v_f_2149_, v_a_2152_, lean_box(0));
return v___x_2153_;
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_f_2149_);
v_a_2154_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2151_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2151_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_fn_2163_, lean_object* v_mode_2164_, lean_object* v_f_2165_, lean_object* v_a_2166_){
_start:
{
uint8_t v_mode_boxed_2167_; lean_object* v_res_2168_; 
v_mode_boxed_2167_ = lean_unbox(v_mode_2164_);
v_res_2168_ = l_IO_FS_withFile(v_00_u03b1_2162_, v_fn_2163_, v_mode_boxed_2167_, v_f_2165_);
lean_dec_ref(v_fn_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* v_h_2169_, lean_object* v_s_2170_){
_start:
{
uint32_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = 10;
v___x_2173_ = lean_string_push(v_s_2170_, v___x_2172_);
v___x_2174_ = lean_io_prim_handle_put_str(v_h_2169_, v___x_2173_);
lean_dec_ref(v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* v_h_2175_, lean_object* v_s_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_IO_FS_Handle_putStrLn(v_h_2175_, v_s_2176_);
lean_dec(v_h_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object* v_h_2179_, lean_object* v_acc_2180_){
_start:
{
size_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((size_t)1024ULL);
v___x_2183_ = lean_io_prim_handle_read(v_h_2179_, v___x_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2197_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint8_t v___x_2188_; 
v___x_2188_ = l_ByteArray_isEmpty(v_a_2184_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_del_object(v___x_2186_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_byte_array_size(v_acc_2180_);
v___x_2191_ = lean_byte_array_size(v_a_2184_);
v___x_2192_ = lean_byte_array_copy_slice(v_a_2184_, v___x_2189_, v_acc_2180_, v___x_2190_, v___x_2191_, v___x_2188_);
lean_dec(v_a_2184_);
v_acc_2180_ = v___x_2192_;
goto _start;
}
else
{
lean_object* v___x_2195_; 
lean_dec(v_a_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v_acc_2180_);
v___x_2195_ = v___x_2186_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_acc_2180_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_dec_ref(v_acc_2180_);
return v___x_2183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* v_h_2198_, lean_object* v_acc_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2198_, v_acc_2199_);
lean_dec(v_h_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* v_h_2202_, lean_object* v_buf_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2202_, v_buf_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* v_h_2206_, lean_object* v_buf_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_IO_FS_Handle_readBinToEndInto(v_h_2206_, v_buf_2207_);
lean_dec(v_h_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* v_h_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = l_ByteArray_empty;
v___x_2213_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2210_, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* v_h_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_IO_FS_Handle_readBinToEnd(v_h_2214_);
lean_dec(v_h_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* v_h_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_IO_FS_Handle_readBinToEnd(v_h_2220_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2236_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2236_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2236_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_string_validate_utf8(v_a_2223_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_dec(v_a_2223_);
v___x_2228_ = ((lean_object*)(l_IO_FS_Handle_readToEnd___closed__1));
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 1);
lean_ctor_set(v___x_2225_, 0, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_string_from_utf8_unchecked(v_a_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2232_);
v___x_2234_ = v___x_2225_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_a_2237_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2222_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2222_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* v_h_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_IO_FS_Handle_readToEnd(v_h_2245_);
lean_dec(v_h_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object* v_h_2248_, lean_object* v_lines_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_io_prim_handle_get_line(v_h_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2307_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2307_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2307_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___y_2257_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint32_t v___y_2264_; uint32_t v___y_2272_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = lean_string_length(v_a_2252_);
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_nat_dec_eq(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_string_utf8_byte_size(v_a_2252_);
lean_inc(v_a_2252_);
v___x_2298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2298_, 0, v_a_2252_);
lean_ctor_set(v___x_2298_, 1, v___x_2295_);
lean_ctor_set(v___x_2298_, 2, v___x_2297_);
v___x_2299_ = l_String_Slice_Pos_prev_x3f(v___x_2298_, v___x_2297_);
if (lean_obj_tag(v___x_2299_) == 0)
{
uint32_t v___x_2300_; 
lean_dec_ref(v___x_2298_);
v___x_2300_ = 65;
v___y_2272_ = v___x_2300_;
goto v___jp_2271_;
}
else
{
lean_object* v_val_2301_; lean_object* v___x_2302_; 
v_val_2301_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2301_);
lean_dec_ref(v___x_2299_);
v___x_2302_ = l_String_Slice_Pos_get_x3f(v___x_2298_, v_val_2301_);
lean_dec(v_val_2301_);
lean_dec_ref(v___x_2298_);
if (lean_obj_tag(v___x_2302_) == 0)
{
uint32_t v___x_2303_; 
v___x_2303_ = 65;
v___y_2272_ = v___x_2303_;
goto v___jp_2271_;
}
else
{
lean_object* v_val_2304_; uint32_t v___x_2305_; 
v_val_2304_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2304_);
lean_dec_ref(v___x_2302_);
v___x_2305_ = lean_unbox_uint32(v_val_2304_);
lean_dec(v_val_2304_);
v___y_2272_ = v___x_2305_;
goto v___jp_2271_;
}
}
}
else
{
lean_object* v___x_2306_; 
lean_del_object(v___x_2254_);
lean_dec(v_a_2252_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_lines_2249_);
return v___x_2306_;
}
v___jp_2256_:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_array_push(v_lines_2249_, v___y_2257_);
v_lines_2249_ = v___x_2258_;
goto _start;
}
v___jp_2260_:
{
uint32_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = 13;
v___x_2266_ = lean_uint32_dec_eq(v___y_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_dec(v___y_2263_);
lean_dec(v___y_2261_);
v___y_2257_ = v___y_2262_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = lean_string_utf8_byte_size(v___y_2262_);
lean_inc(v___y_2263_);
lean_inc_ref(v___y_2262_);
v___x_2268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2268_, 0, v___y_2262_);
lean_ctor_set(v___x_2268_, 1, v___y_2263_);
lean_ctor_set(v___x_2268_, 2, v___x_2267_);
v___x_2269_ = l_String_Slice_Pos_prevn(v___x_2268_, v___x_2267_, v___y_2261_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = lean_string_utf8_extract(v___y_2262_, v___y_2263_, v___x_2269_);
lean_dec(v___x_2269_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
v___y_2257_ = v___x_2270_;
goto v___jp_2256_;
}
}
v___jp_2271_:
{
uint32_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = 10;
v___x_2274_ = lean_uint32_dec_eq(v___y_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_array_push(v_lines_2249_, v_a_2252_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2275_);
v___x_2277_ = v___x_2254_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2254_);
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2281_ = lean_string_utf8_byte_size(v_a_2252_);
lean_inc(v_a_2252_);
v___x_2282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2252_);
lean_ctor_set(v___x_2282_, 1, v___x_2280_);
lean_ctor_set(v___x_2282_, 2, v___x_2281_);
v___x_2283_ = l_String_Slice_Pos_prevn(v___x_2282_, v___x_2281_, v___x_2279_);
lean_dec_ref(v___x_2282_);
v___x_2284_ = lean_string_utf8_extract(v_a_2252_, v___x_2280_, v___x_2283_);
lean_dec(v___x_2283_);
lean_dec(v_a_2252_);
v___x_2285_ = lean_string_utf8_byte_size(v___x_2284_);
lean_inc_ref(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2280_);
lean_ctor_set(v___x_2286_, 2, v___x_2285_);
v___x_2287_ = l_String_Slice_Pos_prev_x3f(v___x_2286_, v___x_2285_);
if (lean_obj_tag(v___x_2287_) == 0)
{
uint32_t v___x_2288_; 
lean_dec_ref(v___x_2286_);
v___x_2288_ = 65;
v___y_2261_ = v___x_2279_;
v___y_2262_ = v___x_2284_;
v___y_2263_ = v___x_2280_;
v___y_2264_ = v___x_2288_;
goto v___jp_2260_;
}
else
{
lean_object* v_val_2289_; lean_object* v___x_2290_; 
v_val_2289_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2289_);
lean_dec_ref(v___x_2287_);
v___x_2290_ = l_String_Slice_Pos_get_x3f(v___x_2286_, v_val_2289_);
lean_dec(v_val_2289_);
lean_dec_ref(v___x_2286_);
if (lean_obj_tag(v___x_2290_) == 0)
{
uint32_t v___x_2291_; 
v___x_2291_ = 65;
v___y_2261_ = v___x_2279_;
v___y_2262_ = v___x_2284_;
v___y_2263_ = v___x_2280_;
v___y_2264_ = v___x_2291_;
goto v___jp_2260_;
}
else
{
lean_object* v_val_2292_; uint32_t v___x_2293_; 
v_val_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2292_);
lean_dec_ref(v___x_2290_);
v___x_2293_ = lean_unbox_uint32(v_val_2292_);
lean_dec(v_val_2292_);
v___y_2261_ = v___x_2279_;
v___y_2262_ = v___x_2284_;
v___y_2263_ = v___x_2280_;
v___y_2264_ = v___x_2293_;
goto v___jp_2260_;
}
}
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_lines_2249_);
v_a_2308_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2251_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2251_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* v_h_2316_, lean_object* v_lines_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_2316_, v_lines_2317_);
lean_dec(v_h_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object* v_h_2322_){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_2325_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_2322_, v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* v_h_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_IO_FS_Handle_lines(v_h_2326_);
lean_dec(v_h_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* v_fname_2329_){
_start:
{
uint8_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = 0;
v___x_2332_ = lean_io_prim_handle_mk(v_fname_2329_, v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l_IO_FS_Handle_lines(v_a_2333_);
lean_dec(v_a_2333_);
return v___x_2334_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_a_2335_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2332_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2332_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* v_fname_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_IO_FS_lines(v_fname_2343_);
lean_dec_ref(v_fname_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* v_fname_2346_, lean_object* v_content_2347_){
_start:
{
uint8_t v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = 1;
v___x_2350_ = lean_io_prim_handle_mk(v_fname_2346_, v___x_2349_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = lean_io_prim_handle_write(v_a_2351_, v_content_2347_);
lean_dec(v_a_2351_);
return v___x_2352_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2350_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2350_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* v_fname_2361_, lean_object* v_content_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_IO_FS_writeBinFile(v_fname_2361_, v_content_2362_);
lean_dec_ref(v_content_2362_);
lean_dec_ref(v_fname_2361_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* v_fname_2365_, lean_object* v_content_2366_){
_start:
{
uint8_t v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = 1;
v___x_2369_ = lean_io_prim_handle_mk(v_fname_2365_, v___x_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = lean_io_prim_handle_put_str(v_a_2370_, v_content_2366_);
lean_dec(v_a_2370_);
return v___x_2371_;
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2369_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2369_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* v_fname_2380_, lean_object* v_content_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_IO_FS_writeFile(v_fname_2380_, v_content_2381_);
lean_dec_ref(v_content_2381_);
lean_dec_ref(v_fname_2380_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* v_strm_2384_, lean_object* v_s_2385_){
_start:
{
lean_object* v_putStr_2387_; uint32_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_putStr_2387_ = lean_ctor_get(v_strm_2384_, 4);
lean_inc_ref(v_putStr_2387_);
lean_dec_ref(v_strm_2384_);
v___x_2388_ = 10;
v___x_2389_ = lean_string_push(v_s_2385_, v___x_2388_);
v___x_2390_ = lean_apply_2(v_putStr_2387_, v___x_2389_, lean_box(0));
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* v_strm_2391_, lean_object* v_s_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_IO_FS_Stream_putStrLn(v_strm_2391_, v_s_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_nat_to_int(v_a_2395_);
return v___x_2396_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(8u);
v___x_2411_ = lean_nat_to_int(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(12u);
v___x_2422_ = lean_nat_to_int(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__0));
v___x_2425_ = lean_string_length(v___x_2424_);
return v___x_2425_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__16, &l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
v___x_2427_ = lean_nat_to_int(v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* v_x_2432_){
_start:
{
lean_object* v_root_2433_; lean_object* v_fileName_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2473_; 
v_root_2433_ = lean_ctor_get(v_x_2432_, 0);
v_fileName_2434_ = lean_ctor_get(v_x_2432_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_x_2432_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2436_ = v_x_2432_;
v_isShared_2437_ = v_isSharedCheck_2473_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_fileName_2434_);
lean_inc(v_root_2433_);
lean_dec(v_x_2432_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2473_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2438_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_2439_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__6));
v___x_2440_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_2441_ = lean_unsigned_to_nat(0u);
v___x_2442_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__9));
v___x_2443_ = l_String_quote(v_root_2433_);
v___x_2444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 5);
lean_ctor_set(v___x_2436_, 1, v___x_2444_);
lean_ctor_set(v___x_2436_, 0, v___x_2442_);
v___x_2446_ = v___x_2436_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2447_ = l_Repr_addAppParen(v___x_2446_, v___x_2441_);
v___x_2448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2440_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = 0;
v___x_2450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2439_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_2453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_box(1);
v___x_2455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__13));
v___x_2457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___x_2438_);
v___x_2459_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_2460_ = l_String_quote(v_fileName_2434_);
v___x_2461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2459_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*1, v___x_2449_);
v___x_2464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2458_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_2466_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2464_);
v___x_2468_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_2469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2465_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*1, v___x_2449_);
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* v_x_2474_, lean_object* v_prec_2475_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* v_x_2477_, lean_object* v_prec_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_IO_FS_instReprDirEntry_repr(v_x_2477_, v_prec_2478_);
lean_dec(v_prec_2478_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* v_entry_2482_){
_start:
{
lean_object* v_root_2483_; lean_object* v_fileName_2484_; lean_object* v___x_2485_; 
v_root_2483_ = lean_ctor_get(v_entry_2482_, 0);
lean_inc_ref(v_root_2483_);
v_fileName_2484_ = lean_ctor_get(v_entry_2482_, 1);
lean_inc_ref(v_fileName_2484_);
lean_dec_ref(v_entry_2482_);
v___x_2485_ = l_System_FilePath_join(v_root_2483_, v_fileName_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t v_x_2486_){
_start:
{
switch(v_x_2486_)
{
case 0:
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_unsigned_to_nat(0u);
return v___x_2487_;
}
case 1:
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_unsigned_to_nat(1u);
return v___x_2488_;
}
case 2:
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_unsigned_to_nat(2u);
return v___x_2489_;
}
default: 
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_unsigned_to_nat(3u);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object* v_x_2491_){
_start:
{
uint8_t v_x_boxed_2492_; lean_object* v_res_2493_; 
v_x_boxed_2492_ = lean_unbox(v_x_2491_);
v_res_2493_ = l_IO_FS_FileType_ctorIdx(v_x_boxed_2492_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t v_x_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_IO_FS_FileType_ctorIdx(v_x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object* v_x_2496_){
_start:
{
uint8_t v_x_4__boxed_2497_; lean_object* v_res_2498_; 
v_x_4__boxed_2497_ = lean_unbox(v_x_2496_);
v_res_2498_ = l_IO_FS_FileType_toCtorIdx(v_x_4__boxed_2497_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* v_k_2499_){
_start:
{
lean_inc(v_k_2499_);
return v_k_2499_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* v_k_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_IO_FS_FileType_ctorElim___redArg(v_k_2500_);
lean_dec(v_k_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object* v_motive_2502_, lean_object* v_ctorIdx_2503_, uint8_t v_t_2504_, lean_object* v_h_2505_, lean_object* v_k_2506_){
_start:
{
lean_inc(v_k_2506_);
return v_k_2506_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* v_motive_2507_, lean_object* v_ctorIdx_2508_, lean_object* v_t_2509_, lean_object* v_h_2510_, lean_object* v_k_2511_){
_start:
{
uint8_t v_t_boxed_2512_; lean_object* v_res_2513_; 
v_t_boxed_2512_ = lean_unbox(v_t_2509_);
v_res_2513_ = l_IO_FS_FileType_ctorElim(v_motive_2507_, v_ctorIdx_2508_, v_t_boxed_2512_, v_h_2510_, v_k_2511_);
lean_dec(v_k_2511_);
lean_dec(v_ctorIdx_2508_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* v_dir_2514_){
_start:
{
lean_inc(v_dir_2514_);
return v_dir_2514_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* v_dir_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_2515_);
lean_dec(v_dir_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object* v_motive_2517_, uint8_t v_t_2518_, lean_object* v_h_2519_, lean_object* v_dir_2520_){
_start:
{
lean_inc(v_dir_2520_);
return v_dir_2520_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* v_motive_2521_, lean_object* v_t_2522_, lean_object* v_h_2523_, lean_object* v_dir_2524_){
_start:
{
uint8_t v_t_boxed_2525_; lean_object* v_res_2526_; 
v_t_boxed_2525_ = lean_unbox(v_t_2522_);
v_res_2526_ = l_IO_FS_FileType_dir_elim(v_motive_2521_, v_t_boxed_2525_, v_h_2523_, v_dir_2524_);
lean_dec(v_dir_2524_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* v_file_2527_){
_start:
{
lean_inc(v_file_2527_);
return v_file_2527_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* v_file_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_IO_FS_FileType_file_elim___redArg(v_file_2528_);
lean_dec(v_file_2528_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object* v_motive_2530_, uint8_t v_t_2531_, lean_object* v_h_2532_, lean_object* v_file_2533_){
_start:
{
lean_inc(v_file_2533_);
return v_file_2533_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* v_motive_2534_, lean_object* v_t_2535_, lean_object* v_h_2536_, lean_object* v_file_2537_){
_start:
{
uint8_t v_t_boxed_2538_; lean_object* v_res_2539_; 
v_t_boxed_2538_ = lean_unbox(v_t_2535_);
v_res_2539_ = l_IO_FS_FileType_file_elim(v_motive_2534_, v_t_boxed_2538_, v_h_2536_, v_file_2537_);
lean_dec(v_file_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* v_symlink_2540_){
_start:
{
lean_inc(v_symlink_2540_);
return v_symlink_2540_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* v_symlink_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_2541_);
lean_dec(v_symlink_2541_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object* v_motive_2543_, uint8_t v_t_2544_, lean_object* v_h_2545_, lean_object* v_symlink_2546_){
_start:
{
lean_inc(v_symlink_2546_);
return v_symlink_2546_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* v_motive_2547_, lean_object* v_t_2548_, lean_object* v_h_2549_, lean_object* v_symlink_2550_){
_start:
{
uint8_t v_t_boxed_2551_; lean_object* v_res_2552_; 
v_t_boxed_2551_ = lean_unbox(v_t_2548_);
v_res_2552_ = l_IO_FS_FileType_symlink_elim(v_motive_2547_, v_t_boxed_2551_, v_h_2549_, v_symlink_2550_);
lean_dec(v_symlink_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* v_other_2553_){
_start:
{
lean_inc(v_other_2553_);
return v_other_2553_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* v_other_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_IO_FS_FileType_other_elim___redArg(v_other_2554_);
lean_dec(v_other_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object* v_motive_2556_, uint8_t v_t_2557_, lean_object* v_h_2558_, lean_object* v_other_2559_){
_start:
{
lean_inc(v_other_2559_);
return v_other_2559_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* v_motive_2560_, lean_object* v_t_2561_, lean_object* v_h_2562_, lean_object* v_other_2563_){
_start:
{
uint8_t v_t_boxed_2564_; lean_object* v_res_2565_; 
v_t_boxed_2564_ = lean_unbox(v_t_2561_);
v_res_2565_ = l_IO_FS_FileType_other_elim(v_motive_2560_, v_t_boxed_2564_, v_h_2562_, v_other_2563_);
lean_dec(v_other_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t v_x_2578_, lean_object* v_prec_2579_){
_start:
{
lean_object* v___y_2581_; lean_object* v___y_2588_; lean_object* v___y_2595_; lean_object* v___y_2602_; 
switch(v_x_2578_)
{
case 0:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_unsigned_to_nat(1024u);
v___x_2609_ = lean_nat_dec_le(v___x_2608_, v_prec_2579_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2581_ = v___x_2610_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2581_ = v___x_2611_;
goto v___jp_2580_;
}
}
case 1:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_unsigned_to_nat(1024u);
v___x_2613_ = lean_nat_dec_le(v___x_2612_, v_prec_2579_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2588_ = v___x_2614_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2588_ = v___x_2615_;
goto v___jp_2587_;
}
}
case 2:
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(1024u);
v___x_2617_ = lean_nat_dec_le(v___x_2616_, v_prec_2579_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2595_ = v___x_2618_;
goto v___jp_2594_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2595_ = v___x_2619_;
goto v___jp_2594_;
}
}
default: 
{
lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = lean_unsigned_to_nat(1024u);
v___x_2621_ = lean_nat_dec_le(v___x_2620_, v_prec_2579_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2602_ = v___x_2622_;
goto v___jp_2601_;
}
else
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2602_ = v___x_2623_;
goto v___jp_2601_;
}
}
}
v___jp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2582_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__1));
v___x_2583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = 0;
v___x_2585_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*1, v___x_2584_);
v___x_2586_ = l_Repr_addAppParen(v___x_2585_, v_prec_2579_);
return v___x_2586_;
}
v___jp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2589_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__3));
v___x_2590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___y_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = 0;
v___x_2592_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set_uint8(v___x_2592_, sizeof(void*)*1, v___x_2591_);
v___x_2593_ = l_Repr_addAppParen(v___x_2592_, v_prec_2579_);
return v___x_2593_;
}
v___jp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2596_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__5));
v___x_2597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___y_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = 0;
v___x_2599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1, v___x_2598_);
v___x_2600_ = l_Repr_addAppParen(v___x_2599_, v_prec_2579_);
return v___x_2600_;
}
v___jp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2603_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__7));
v___x_2604_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___y_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = 0;
v___x_2606_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*1, v___x_2605_);
v___x_2607_ = l_Repr_addAppParen(v___x_2606_, v_prec_2579_);
return v___x_2607_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* v_x_2624_, lean_object* v_prec_2625_){
_start:
{
uint8_t v_x_229__boxed_2626_; lean_object* v_res_2627_; 
v_x_229__boxed_2626_ = lean_unbox(v_x_2624_);
v_res_2627_ = l_IO_FS_instReprFileType_repr(v_x_229__boxed_2626_, v_prec_2625_);
lean_dec(v_prec_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t v_x_2630_, uint8_t v_y_2631_){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = l_IO_FS_FileType_ctorIdx(v_x_2630_);
v___x_2633_ = l_IO_FS_FileType_ctorIdx(v_y_2631_);
v___x_2634_ = lean_nat_dec_eq(v___x_2632_, v___x_2633_);
lean_dec(v___x_2633_);
lean_dec(v___x_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* v_x_2635_, lean_object* v_y_2636_){
_start:
{
uint8_t v_x_17__boxed_2637_; uint8_t v_y_18__boxed_2638_; uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_x_17__boxed_2637_ = lean_unbox(v_x_2635_);
v_y_18__boxed_2638_ = lean_unbox(v_y_2636_);
v_res_2639_ = l_IO_FS_instBEqFileType_beq(v_x_17__boxed_2637_, v_y_18__boxed_2638_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_unsigned_to_nat(7u);
v___x_2653_ = lean_nat_to_int(v___x_2652_);
return v___x_2653_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = lean_nat_to_int(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* v_x_2659_){
_start:
{
lean_object* v_sec_2660_; uint32_t v_nsec_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___y_2666_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_sec_2660_ = lean_ctor_get(v_x_2659_, 0);
v_nsec_2661_ = lean_ctor_get_uint32(v_x_2659_, sizeof(void*)*1);
v___x_2662_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_2663_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__3));
v___x_2664_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__4, &l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_2694_ = lean_int_dec_lt(v_sec_2660_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = l_Int_repr(v_sec_2660_);
v___x_2696_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
v___y_2666_ = v___x_2696_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = l_Int_repr(v_sec_2660_);
v___x_2698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
v___x_2699_ = l_Repr_addAppParen(v___x_2698_, v___x_2692_);
v___y_2666_ = v___x_2699_;
goto v___jp_2665_;
}
v___jp_2665_:
{
lean_object* v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2664_);
lean_ctor_set(v___x_2667_, 1, v___y_2666_);
v___x_2668_ = 0;
v___x_2669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set_uint8(v___x_2669_, sizeof(void*)*1, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2663_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_2672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = lean_box(1);
v___x_2674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__6));
v___x_2676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___x_2662_);
v___x_2678_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_2679_ = lean_uint32_to_nat(v_nsec_2661_);
v___x_2680_ = l_Nat_reprFast(v___x_2679_);
v___x_2681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2678_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*1, v___x_2668_);
v___x_2684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2677_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_2686_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_2687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v___x_2684_);
v___x_2688_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_2689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2685_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*1, v___x_2668_);
return v___x_2691_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* v_x_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_2700_);
lean_dec_ref(v_x_2700_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* v_x_2702_, lean_object* v_prec_2703_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_2702_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* v_x_2705_, lean_object* v_prec_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_IO_FS_instReprSystemTime_repr(v_x_2705_, v_prec_2706_);
lean_dec(v_prec_2706_);
lean_dec_ref(v_x_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
lean_object* v_sec_2712_; uint32_t v_nsec_2713_; lean_object* v_sec_2714_; uint32_t v_nsec_2715_; uint8_t v___x_2716_; 
v_sec_2712_ = lean_ctor_get(v_x_2710_, 0);
v_nsec_2713_ = lean_ctor_get_uint32(v_x_2710_, sizeof(void*)*1);
v_sec_2714_ = lean_ctor_get(v_x_2711_, 0);
v_nsec_2715_ = lean_ctor_get_uint32(v_x_2711_, sizeof(void*)*1);
v___x_2716_ = lean_int_dec_eq(v_sec_2712_, v_sec_2714_);
if (v___x_2716_ == 0)
{
return v___x_2716_;
}
else
{
uint8_t v___x_2717_; 
v___x_2717_ = lean_uint32_dec_eq(v_nsec_2713_, v_nsec_2715_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_IO_FS_instBEqSystemTime_beq(v_x_2718_, v_x_2719_);
lean_dec_ref(v_x_2719_);
lean_dec_ref(v_x_2718_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* v_x_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v_sec_2726_; uint32_t v_nsec_2727_; lean_object* v_sec_2728_; uint32_t v_nsec_2729_; uint8_t v___x_2730_; 
v_sec_2726_ = lean_ctor_get(v_x_2724_, 0);
v_nsec_2727_ = lean_ctor_get_uint32(v_x_2724_, sizeof(void*)*1);
v_sec_2728_ = lean_ctor_get(v_x_2725_, 0);
v_nsec_2729_ = lean_ctor_get_uint32(v_x_2725_, sizeof(void*)*1);
v___x_2730_ = lean_int_dec_lt(v_sec_2726_, v_sec_2728_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_int_dec_eq(v_sec_2726_, v_sec_2728_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
v___x_2732_ = 2;
return v___x_2732_;
}
else
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_uint32_dec_lt(v_nsec_2727_, v_nsec_2729_);
if (v___x_2733_ == 0)
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_uint32_dec_eq(v_nsec_2727_, v_nsec_2729_);
if (v___x_2734_ == 0)
{
uint8_t v___x_2735_; 
v___x_2735_ = 2;
return v___x_2735_;
}
else
{
uint8_t v___x_2736_; 
v___x_2736_ = 1;
return v___x_2736_;
}
}
else
{
uint8_t v___x_2737_; 
v___x_2737_ = 0;
return v___x_2737_;
}
}
}
else
{
uint8_t v___x_2738_; 
v___x_2738_ = 0;
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
uint8_t v_res_2741_; lean_object* v_r_2742_; 
v_res_2741_ = l_IO_FS_instOrdSystemTime_ord(v_x_2739_, v_x_2740_);
lean_dec_ref(v_x_2740_);
lean_dec_ref(v_x_2739_);
v_r_2742_ = lean_box(v_res_2741_);
return v_r_2742_;
}
}
static uint32_t _init_l_IO_FS_instInhabitedSystemTime_default___closed__0(void){
_start:
{
lean_object* v___x_2745_; uint32_t v___x_2746_; 
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_uint32_of_nat(v___x_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__1(void){
_start:
{
uint32_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_uint32_once(&l_IO_FS_instInhabitedSystemTime_default___closed__0, &l_IO_FS_instInhabitedSystemTime_default___closed__0_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__0);
v___x_2748_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_2749_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set_uint32(v___x_2749_, sizeof(void*)*1, v___x_2747_);
return v___x_2749_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default(void){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_IO_FS_instInhabitedSystemTime_default___closed__1, &l_IO_FS_instInhabitedSystemTime_default___closed__1_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__1);
return v___x_2750_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime(void){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_IO_FS_instInhabitedSystemTime_default;
return v___x_2751_;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime(void){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_box(0);
return v___x_2752_;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime(void){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_box(0);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* v_x_2775_){
_start:
{
lean_object* v_accessed_2776_; lean_object* v_modified_2777_; uint64_t v_byteSize_2778_; uint8_t v_type_2779_; uint64_t v_numLinks_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_accessed_2776_ = lean_ctor_get(v_x_2775_, 0);
v_modified_2777_ = lean_ctor_get(v_x_2775_, 1);
v_byteSize_2778_ = lean_ctor_get_uint64(v_x_2775_, sizeof(void*)*2);
v_type_2779_ = lean_ctor_get_uint8(v_x_2775_, sizeof(void*)*2 + 16);
v_numLinks_2780_ = lean_ctor_get_uint64(v_x_2775_, sizeof(void*)*2 + 8);
v___x_2781_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_2782_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__3));
v___x_2783_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_2784_ = lean_unsigned_to_nat(0u);
v___x_2785_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_2776_);
v___x_2786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2783_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = 0;
v___x_2788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*1, v___x_2787_);
v___x_2789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2782_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_box(1);
v___x_2793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__5));
v___x_2795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2781_);
v___x_2797_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_2777_);
v___x_2798_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2783_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*1, v___x_2787_);
v___x_2800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2796_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2790_);
v___x_2802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v___x_2792_);
v___x_2803_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__7));
v___x_2804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2781_);
v___x_2806_ = lean_uint64_to_nat(v_byteSize_2778_);
v___x_2807_ = l_Nat_reprFast(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2783_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set_uint8(v___x_2810_, sizeof(void*)*1, v___x_2787_);
v___x_2811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2805_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___x_2790_);
v___x_2813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v___x_2792_);
v___x_2814_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__9));
v___x_2815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___x_2781_);
v___x_2817_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_2818_ = l_IO_FS_instReprFileType_repr(v_type_2779_, v___x_2784_);
v___x_2819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*1, v___x_2787_);
v___x_2821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2816_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___x_2790_);
v___x_2823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2792_);
v___x_2824_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__11));
v___x_2825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v___x_2781_);
v___x_2827_ = lean_uint64_to_nat(v_numLinks_2780_);
v___x_2828_ = l_Nat_reprFast(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2783_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*1, v___x_2787_);
v___x_2832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2826_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_2834_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_2835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
lean_ctor_set(v___x_2835_, 1, v___x_2832_);
v___x_2836_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_2837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2833_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*1, v___x_2787_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* v_x_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_2840_);
lean_dec_ref(v_x_2840_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* v_x_2842_, lean_object* v_prec_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* v_x_2845_, lean_object* v_prec_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_IO_FS_instReprMetadata_repr(v_x_2845_, v_prec_2846_);
lean_dec(v_prec_2846_);
lean_dec_ref(v_x_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* v_a_00___x40___internal___hyg_2852_, lean_object* v_a_00___x40___internal___hyg_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = lean_io_read_dir(v_a_00___x40___internal___hyg_2852_);
lean_dec_ref(v_a_00___x40___internal___hyg_2852_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* v_a_00___x40___internal___hyg_2857_, lean_object* v_a_00___x40___internal___hyg_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = lean_io_metadata(v_a_00___x40___internal___hyg_2857_);
lean_dec_ref(v_a_00___x40___internal___hyg_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* v_a_00___x40___internal___hyg_2862_, lean_object* v_a_00___x40___internal___hyg_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_2862_);
lean_dec_ref(v_a_00___x40___internal___hyg_2862_);
return v_res_2864_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object* v_p_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_io_metadata(v_p_2865_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; uint8_t v_type_2869_; uint8_t v___x_2870_; uint8_t v___x_2871_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2867_);
v_type_2869_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*2 + 16);
lean_dec(v_a_2868_);
v___x_2870_ = 0;
v___x_2871_ = l_IO_FS_instBEqFileType_beq(v_type_2869_, v___x_2870_);
return v___x_2871_;
}
else
{
uint8_t v___x_2872_; 
lean_dec_ref(v___x_2867_);
v___x_2872_ = 0;
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* v_p_2873_, lean_object* v_a_2874_){
_start:
{
uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_res_2875_ = l_System_FilePath_isDir(v_p_2873_);
lean_dec_ref(v_p_2873_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object* v_p_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_io_metadata(v_p_2877_);
if (lean_obj_tag(v___x_2879_) == 0)
{
uint8_t v___x_2880_; 
lean_dec_ref(v___x_2879_);
v___x_2880_ = 1;
return v___x_2880_;
}
else
{
uint8_t v___x_2881_; 
lean_dec_ref(v___x_2879_);
v___x_2881_ = 0;
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* v_p_2882_, lean_object* v_a_2883_){
_start:
{
uint8_t v_res_2884_; lean_object* v_r_2885_; 
v_res_2884_ = l_System_FilePath_pathExists(v_p_2882_);
lean_dec_ref(v_p_2882_);
v_r_2885_ = lean_box(v_res_2884_);
return v_r_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* v_enter_2886_, lean_object* v_p_2887_, lean_object* v_as_2888_, size_t v_sz_2889_, size_t v_i_2890_, lean_object* v_b_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_a_2895_; lean_object* v_snd_2896_; uint8_t v___x_2900_; 
v___x_2900_ = lean_usize_dec_lt(v_i_2890_, v_sz_2889_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec_ref(v_p_2887_);
lean_dec_ref(v_enter_2886_);
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v_b_2891_);
lean_ctor_set(v___x_2901_, 1, v___y_2892_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
else
{
lean_object* v___x_2903_; lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2903_ = lean_box(0);
v_a_2904_ = lean_array_uget_borrowed(v_as_2888_, v_i_2890_);
lean_inc(v_a_2904_);
v___x_2905_ = l_IO_FS_DirEntry_path(v_a_2904_);
lean_inc_ref(v___x_2905_);
v___x_2906_ = lean_array_push(v___y_2892_, v___x_2905_);
v___x_2907_ = lean_io_metadata(v___x_2905_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; uint8_t v_type_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v_type_2909_ = lean_ctor_get_uint8(v_a_2908_, sizeof(void*)*2 + 16);
lean_dec(v_a_2908_);
switch(v_type_2909_)
{
case 2:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_io_realpath(v___x_2905_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; uint8_t v___x_2912_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
v___x_2912_ = l_System_FilePath_isDir(v_a_2911_);
if (v___x_2912_ == 0)
{
lean_dec(v_a_2911_);
v_a_2895_ = v___x_2903_;
v_snd_2896_ = v___x_2906_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2913_; 
lean_inc_ref(v_enter_2886_);
lean_inc_ref(v_p_2887_);
v___x_2913_ = lean_apply_2(v_enter_2886_, v_p_2887_, lean_box(0));
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; uint8_t v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
v___x_2915_ = lean_unbox(v_a_2914_);
lean_dec(v_a_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v_a_2911_);
v_a_2895_ = v___x_2903_;
v_snd_2896_ = v___x_2906_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2916_; 
lean_inc_ref(v_enter_2886_);
v___x_2916_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_2886_, v_a_2911_, v___x_2906_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v_snd_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref(v___x_2916_);
v_snd_2918_ = lean_ctor_get(v_a_2917_, 1);
lean_inc(v_snd_2918_);
lean_dec(v_a_2917_);
v_a_2895_ = v___x_2903_;
v_snd_2896_ = v_snd_2918_;
goto v___jp_2894_;
}
else
{
lean_dec_ref(v_p_2887_);
lean_dec_ref(v_enter_2886_);
return v___x_2916_;
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_a_2911_);
lean_dec_ref(v___x_2906_);
lean_dec_ref(v_p_2887_);
lean_dec_ref(v_enter_2886_);
v_a_2919_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2913_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2913_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v___x_2906_);
lean_dec_ref(v_p_2887_);
lean_dec_ref(v_enter_2886_);
v_a_2927_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2910_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2910_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
case 0:
{
lean_object* v___x_2935_; 
lean_inc_ref(v_enter_2886_);
v___x_2935_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_2886_, v___x_2905_, v___x_2906_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v_snd_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
v_snd_2937_ = lean_ctor_get(v_a_2936_, 1);
lean_inc(v_snd_2937_);
lean_dec(v_a_2936_);
v_a_2895_ = v___x_2903_;
v_snd_2896_ = v_snd_2937_;
goto v___jp_2894_;
}
else
{
lean_dec_ref(v_p_2887_);
lean_dec_ref(v_enter_2886_);
return v___x_2935_;
}
}
default: 
{
lean_dec_ref(v___x_2905_);
v_a_2895_ = v___x_2903_;
v_snd_2896_ = v___x_2906_;
goto v___jp_2894_;
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v___x_2905_);
v_a_2938_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2907_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2907_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
if (lean_obj_tag(v_a_2938_) == 11)
{
lean_dec_ref(v_a_2938_);
lean_del_object(v___x_2940_);
v_a_2895_ = v___x_2903_;
v_snd_2896_ = v___x_2906_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2943_; 
lean_dec_ref(v___x_2906_);
lean_dec_ref(v_p_2887_);
lean_dec_ref(v_enter_2886_);
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
v___jp_2894_:
{
size_t v___x_2897_; size_t v___x_2898_; 
v___x_2897_ = ((size_t)1ULL);
v___x_2898_ = lean_usize_add(v_i_2890_, v___x_2897_);
v_i_2890_ = v___x_2898_;
v_b_2891_ = v_a_2895_;
v___y_2892_ = v_snd_2896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* v_enter_2946_, lean_object* v_p_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2950_; 
lean_inc_ref(v_enter_2946_);
lean_inc_ref(v_p_2947_);
v___x_2950_ = lean_apply_2(v_enter_2946_, v_p_2947_, lean_box(0));
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2992_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2992_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2992_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_unbox(v_a_2951_);
lean_dec(v_a_2951_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
lean_dec_ref(v_p_2947_);
lean_dec_ref(v_enter_2946_);
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v_a_2948_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2957_);
v___x_2959_ = v___x_2953_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
else
{
lean_object* v___x_2961_; 
lean_del_object(v___x_2953_);
v___x_2961_ = lean_io_read_dir(v_p_2947_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; size_t v_sz_2964_; size_t v___x_2965_; lean_object* v___x_2966_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = lean_box(0);
v_sz_2964_ = lean_array_size(v_a_2962_);
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_2946_, v_p_2947_, v_a_2962_, v_sz_2964_, v___x_2965_, v___x_2963_, v_a_2948_);
lean_dec(v_a_2962_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2983_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2983_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2983_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_snd_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2981_; 
v_snd_2971_ = lean_ctor_get(v_a_2967_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_a_2967_, 0);
lean_dec(v_unused_2982_);
v___x_2973_ = v_a_2967_;
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_snd_2971_);
lean_dec(v_a_2967_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2963_);
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_snd_2971_);
v___x_2976_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2978_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2976_);
v___x_2978_ = v___x_2969_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
else
{
return v___x_2966_;
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v_a_2948_);
lean_dec_ref(v_p_2947_);
lean_dec_ref(v_enter_2946_);
v_a_2984_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2961_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2961_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v_a_2948_);
lean_dec_ref(v_p_2947_);
lean_dec_ref(v_enter_2946_);
v_a_2993_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2950_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2950_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* v_enter_3001_, lean_object* v_p_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3001_, v_p_3002_, v_a_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* v_enter_3006_, lean_object* v_p_3007_, lean_object* v_as_3008_, lean_object* v_sz_3009_, lean_object* v_i_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3009_);
lean_dec(v_sz_3009_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3010_);
lean_dec(v_i_3010_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3006_, v_p_3007_, v_as_3008_, v_sz_boxed_3014_, v_i_boxed_3015_, v_b_3011_, v___y_3012_);
lean_dec_ref(v_as_3008_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* v_p_3017_, lean_object* v_enter_3018_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3021_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3018_, v_p_3017_, v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3030_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3030_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3030_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_snd_3026_; lean_object* v___x_3028_; 
v_snd_3026_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_snd_3026_);
lean_dec(v_a_3022_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v_snd_3026_);
v___x_3028_ = v___x_3024_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_snd_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
v_a_3031_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3021_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3021_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* v_p_3039_, lean_object* v_enter_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_System_FilePath_walkDir(v_p_3039_, v_enter_3040_);
return v_res_3042_;
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_mk_empty_byte_array(v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* v_fname_3045_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_io_metadata(v_fname_3045_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = 0;
v___x_3050_ = lean_io_prim_handle_mk(v_fname_3045_, v___x_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; uint64_t v_byteSize_3052_; size_t v___x_3053_; size_t v___x_3054_; uint8_t v___x_3055_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v_byteSize_3052_ = lean_ctor_get_uint64(v_a_3048_, sizeof(void*)*2);
lean_dec(v_a_3048_);
v___x_3053_ = lean_uint64_to_usize(v_byteSize_3052_);
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = lean_usize_dec_lt(v___x_3054_, v___x_3053_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_obj_once(&l_IO_FS_readBinFile___closed__0, &l_IO_FS_readBinFile___closed__0_once, _init_l_IO_FS_readBinFile___closed__0);
v___x_3057_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3051_, v___x_3056_);
lean_dec(v_a_3051_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_io_prim_handle_read(v_a_3051_, v___x_3053_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3051_, v_a_3059_);
lean_dec(v_a_3051_);
return v___x_3060_;
}
else
{
lean_dec(v_a_3051_);
return v___x_3058_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_3048_);
v_a_3061_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3050_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3050_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3047_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3047_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* v_fname_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_IO_FS_readBinFile(v_fname_3077_);
lean_dec_ref(v_fname_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* v_fname_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_IO_FS_readBinFile(v_fname_3082_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3102_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3102_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3102_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_string_validate_utf8(v_a_3085_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_dec(v_a_3085_);
v___x_3090_ = ((lean_object*)(l_IO_FS_readFile___closed__0));
v___x_3091_ = lean_string_append(v___x_3090_, v_fname_3082_);
v___x_3092_ = ((lean_object*)(l_IO_FS_readFile___closed__1));
v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3094_);
v___x_3096_ = v___x_3087_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = lean_string_from_utf8_unchecked(v_a_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3098_);
v___x_3100_ = v___x_3087_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_a_3103_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3084_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3084_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* v_fname_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_IO_FS_readFile(v_fname_3111_);
lean_dec_ref(v_fname_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* v_x_3114_){
_start:
{
lean_object* v_fst_3115_; 
v_fst_3115_ = lean_ctor_get(v_x_3114_, 0);
lean_inc(v_fst_3115_);
return v_fst_3115_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* v_x_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_IO_withStdin___redArg___lam__0(v_x_3116_);
lean_dec_ref(v_x_3116_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* v___x_3118_, lean_object* v_x_3119_){
_start:
{
lean_inc(v___x_3118_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* v___x_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_IO_withStdin___redArg___lam__1(v___x_3120_, v_x_3121_);
lean_dec(v_x_3121_);
lean_dec(v___x_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* v_toFunctor_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_x_3126_, lean_object* v___f_3127_, lean_object* v_prev_3128_){
_start:
{
lean_object* v_map_3129_; lean_object* v_mapConst_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v_y_3136_; lean_object* v___x_3137_; 
v_map_3129_ = lean_ctor_get(v_toFunctor_3123_, 0);
lean_inc(v_map_3129_);
v_mapConst_3130_ = lean_ctor_get(v_toFunctor_3123_, 1);
lean_inc(v_mapConst_3130_);
lean_dec_ref(v_toFunctor_3123_);
v___x_3131_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3131_, 0, v_prev_3128_);
v___x_3132_ = lean_apply_2(v_inst_3124_, lean_box(0), v___x_3131_);
v___x_3133_ = lean_box(0);
v___x_3134_ = lean_apply_4(v_mapConst_3130_, lean_box(0), lean_box(0), v___x_3133_, v___x_3132_);
v___f_3135_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3135_, 0, v___x_3134_);
v_y_3136_ = lean_apply_4(v_inst_3125_, lean_box(0), lean_box(0), v_x_3126_, v___f_3135_);
v___x_3137_ = lean_apply_4(v_map_3129_, lean_box(0), lean_box(0), v___f_3127_, v_y_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_h_3142_, lean_object* v_x_3143_){
_start:
{
lean_object* v_toApplicative_3144_; lean_object* v_toBind_3145_; lean_object* v_toFunctor_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; 
v_toApplicative_3144_ = lean_ctor_get(v_inst_3139_, 0);
lean_inc_ref(v_toApplicative_3144_);
v_toBind_3145_ = lean_ctor_get(v_inst_3139_, 1);
lean_inc(v_toBind_3145_);
lean_dec_ref(v_inst_3139_);
v_toFunctor_3146_ = lean_ctor_get(v_toApplicative_3144_, 0);
lean_inc_ref(v_toFunctor_3146_);
lean_dec_ref(v_toApplicative_3144_);
v___f_3147_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3148_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3148_, 0, v_h_3142_);
lean_inc(v_inst_3141_);
v___x_3149_ = lean_apply_2(v_inst_3141_, lean_box(0), v___x_3148_);
v___f_3150_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3150_, 0, v_toFunctor_3146_);
lean_closure_set(v___f_3150_, 1, v_inst_3141_);
lean_closure_set(v___f_3150_, 2, v_inst_3140_);
lean_closure_set(v___f_3150_, 3, v_x_3143_);
lean_closure_set(v___f_3150_, 4, v___f_3147_);
v___x_3151_ = lean_apply_4(v_toBind_3145_, lean_box(0), lean_box(0), v___x_3149_, v___f_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* v_m_3152_, lean_object* v_00_u03b1_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_h_3157_, lean_object* v_x_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_IO_withStdin___redArg(v_inst_3154_, v_inst_3155_, v_inst_3156_, v_h_3157_, v_x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* v_toFunctor_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_x_3163_, lean_object* v___f_3164_, lean_object* v_prev_3165_){
_start:
{
lean_object* v_map_3166_; lean_object* v_mapConst_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___f_3172_; lean_object* v_y_3173_; lean_object* v___x_3174_; 
v_map_3166_ = lean_ctor_get(v_toFunctor_3160_, 0);
lean_inc(v_map_3166_);
v_mapConst_3167_ = lean_ctor_get(v_toFunctor_3160_, 1);
lean_inc(v_mapConst_3167_);
lean_dec_ref(v_toFunctor_3160_);
v___x_3168_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3168_, 0, v_prev_3165_);
v___x_3169_ = lean_apply_2(v_inst_3161_, lean_box(0), v___x_3168_);
v___x_3170_ = lean_box(0);
v___x_3171_ = lean_apply_4(v_mapConst_3167_, lean_box(0), lean_box(0), v___x_3170_, v___x_3169_);
v___f_3172_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3172_, 0, v___x_3171_);
v_y_3173_ = lean_apply_4(v_inst_3162_, lean_box(0), lean_box(0), v_x_3163_, v___f_3172_);
v___x_3174_ = lean_apply_4(v_map_3166_, lean_box(0), lean_box(0), v___f_3164_, v_y_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_h_3178_, lean_object* v_x_3179_){
_start:
{
lean_object* v_toApplicative_3180_; lean_object* v_toBind_3181_; lean_object* v_toFunctor_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___f_3186_; lean_object* v___x_3187_; 
v_toApplicative_3180_ = lean_ctor_get(v_inst_3175_, 0);
lean_inc_ref(v_toApplicative_3180_);
v_toBind_3181_ = lean_ctor_get(v_inst_3175_, 1);
lean_inc(v_toBind_3181_);
lean_dec_ref(v_inst_3175_);
v_toFunctor_3182_ = lean_ctor_get(v_toApplicative_3180_, 0);
lean_inc_ref(v_toFunctor_3182_);
lean_dec_ref(v_toApplicative_3180_);
v___f_3183_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3184_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3184_, 0, v_h_3178_);
lean_inc(v_inst_3177_);
v___x_3185_ = lean_apply_2(v_inst_3177_, lean_box(0), v___x_3184_);
v___f_3186_ = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3186_, 0, v_toFunctor_3182_);
lean_closure_set(v___f_3186_, 1, v_inst_3177_);
lean_closure_set(v___f_3186_, 2, v_inst_3176_);
lean_closure_set(v___f_3186_, 3, v_x_3179_);
lean_closure_set(v___f_3186_, 4, v___f_3183_);
v___x_3187_ = lean_apply_4(v_toBind_3181_, lean_box(0), lean_box(0), v___x_3185_, v___f_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* v_m_3188_, lean_object* v_00_u03b1_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_h_3193_, lean_object* v_x_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_IO_withStdout___redArg(v_inst_3190_, v_inst_3191_, v_inst_3192_, v_h_3193_, v_x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* v_toFunctor_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_x_3199_, lean_object* v___f_3200_, lean_object* v_prev_3201_){
_start:
{
lean_object* v_map_3202_; lean_object* v_mapConst_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___f_3208_; lean_object* v_y_3209_; lean_object* v___x_3210_; 
v_map_3202_ = lean_ctor_get(v_toFunctor_3196_, 0);
lean_inc(v_map_3202_);
v_mapConst_3203_ = lean_ctor_get(v_toFunctor_3196_, 1);
lean_inc(v_mapConst_3203_);
lean_dec_ref(v_toFunctor_3196_);
v___x_3204_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_3204_, 0, v_prev_3201_);
v___x_3205_ = lean_apply_2(v_inst_3197_, lean_box(0), v___x_3204_);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_apply_4(v_mapConst_3203_, lean_box(0), lean_box(0), v___x_3206_, v___x_3205_);
v___f_3208_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3208_, 0, v___x_3207_);
v_y_3209_ = lean_apply_4(v_inst_3198_, lean_box(0), lean_box(0), v_x_3199_, v___f_3208_);
v___x_3210_ = lean_apply_4(v_map_3202_, lean_box(0), lean_box(0), v___f_3200_, v_y_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_h_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v_toApplicative_3216_; lean_object* v_toBind_3217_; lean_object* v_toFunctor_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; 
v_toApplicative_3216_ = lean_ctor_get(v_inst_3211_, 0);
lean_inc_ref(v_toApplicative_3216_);
v_toBind_3217_ = lean_ctor_get(v_inst_3211_, 1);
lean_inc(v_toBind_3217_);
lean_dec_ref(v_inst_3211_);
v_toFunctor_3218_ = lean_ctor_get(v_toApplicative_3216_, 0);
lean_inc_ref(v_toFunctor_3218_);
lean_dec_ref(v_toApplicative_3216_);
v___f_3219_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3220_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_3220_, 0, v_h_3214_);
lean_inc(v_inst_3213_);
v___x_3221_ = lean_apply_2(v_inst_3213_, lean_box(0), v___x_3220_);
v___f_3222_ = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3222_, 0, v_toFunctor_3218_);
lean_closure_set(v___f_3222_, 1, v_inst_3213_);
lean_closure_set(v___f_3222_, 2, v_inst_3212_);
lean_closure_set(v___f_3222_, 3, v_x_3215_);
lean_closure_set(v___f_3222_, 4, v___f_3219_);
v___x_3223_ = lean_apply_4(v_toBind_3217_, lean_box(0), lean_box(0), v___x_3221_, v___f_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* v_m_3224_, lean_object* v_00_u03b1_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_h_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_IO_withStderr___redArg(v_inst_3226_, v_inst_3227_, v_inst_3228_, v_h_3229_, v_x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* v_inst_3232_, lean_object* v_s_3233_){
_start:
{
lean_object* v___x_3235_; lean_object* v_putStr_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3235_ = lean_get_stdout();
v_putStr_3236_ = lean_ctor_get(v___x_3235_, 4);
lean_inc_ref(v_putStr_3236_);
lean_dec_ref(v___x_3235_);
v___x_3237_ = lean_apply_1(v_inst_3232_, v_s_3233_);
v___x_3238_ = lean_apply_2(v_putStr_3236_, v___x_3237_, lean_box(0));
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* v_inst_3239_, lean_object* v_s_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_IO_print___redArg(v_inst_3239_, v_s_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* v_00_u03b1_3243_, lean_object* v_inst_3244_, lean_object* v_s_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_IO_print___redArg(v_inst_3244_, v_s_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* v_00_u03b1_3248_, lean_object* v_inst_3249_, lean_object* v_s_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_IO_print(v_00_u03b1_3248_, v_inst_3249_, v_s_3250_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* v_inst_3254_, lean_object* v_s_3255_){
_start:
{
lean_object* v___f_3257_; lean_object* v___x_3258_; uint32_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___f_3257_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_3258_ = lean_apply_1(v_inst_3254_, v_s_3255_);
v___x_3259_ = 10;
v___x_3260_ = lean_string_push(v___x_3258_, v___x_3259_);
v___x_3261_ = l_IO_print___redArg(v___f_3257_, v___x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* v_inst_3262_, lean_object* v_s_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_IO_println___redArg(v_inst_3262_, v_s_3263_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* v_00_u03b1_3266_, lean_object* v_inst_3267_, lean_object* v_s_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_IO_println___redArg(v_inst_3267_, v_s_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* v_00_u03b1_3271_, lean_object* v_inst_3272_, lean_object* v_s_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_IO_println(v_00_u03b1_3271_, v_inst_3272_, v_s_3273_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* v_inst_3276_, lean_object* v_s_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v_putStr_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3279_ = lean_get_stderr();
v_putStr_3280_ = lean_ctor_get(v___x_3279_, 4);
lean_inc_ref(v_putStr_3280_);
lean_dec_ref(v___x_3279_);
v___x_3281_ = lean_apply_1(v_inst_3276_, v_s_3277_);
v___x_3282_ = lean_apply_2(v_putStr_3280_, v___x_3281_, lean_box(0));
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* v_inst_3283_, lean_object* v_s_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_IO_eprint___redArg(v_inst_3283_, v_s_3284_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* v_00_u03b1_3287_, lean_object* v_inst_3288_, lean_object* v_s_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_IO_eprint___redArg(v_inst_3288_, v_s_3289_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_inst_3293_, lean_object* v_s_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_IO_eprint(v_00_u03b1_3292_, v_inst_3293_, v_s_3294_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* v_inst_3297_, lean_object* v_s_3298_){
_start:
{
lean_object* v___f_3300_; lean_object* v___x_3301_; uint32_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___f_3300_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_3301_ = lean_apply_1(v_inst_3297_, v_s_3298_);
v___x_3302_ = 10;
v___x_3303_ = lean_string_push(v___x_3301_, v___x_3302_);
v___x_3304_ = l_IO_eprint___redArg(v___f_3300_, v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* v_inst_3305_, lean_object* v_s_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_IO_eprintln___redArg(v_inst_3305_, v_s_3306_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* v_00_u03b1_3309_, lean_object* v_inst_3310_, lean_object* v_s_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_IO_eprintln___redArg(v_inst_3310_, v_s_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_inst_3315_, lean_object* v_s_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_IO_eprintln(v_00_u03b1_3314_, v_inst_3315_, v_s_3316_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* v_s_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v_putStr_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_get_stderr();
v_putStr_3322_ = lean_ctor_get(v___x_3321_, 4);
lean_inc_ref(v_putStr_3322_);
lean_dec_ref(v___x_3321_);
v___x_3323_ = lean_apply_2(v_putStr_3322_, v_s_3319_, lean_box(0));
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* v_s_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_3324_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* v_s_3327_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_3327_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* v_s_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = lean_io_eprint(v_s_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* v_s_3333_){
_start:
{
uint32_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = 10;
v___x_3336_ = lean_string_push(v_s_3333_, v___x_3335_);
v___x_3337_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* v_s_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* v_s_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* v_s_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = lean_io_eprintln(v_s_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_io_app_path();
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3366_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3366_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3366_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; 
lean_inc(v_a_3351_);
v___x_3355_ = l_System_FilePath_parent(v_a_3351_);
if (lean_obj_tag(v___x_3355_) == 1)
{
lean_object* v_val_3356_; lean_object* v___x_3357_; 
lean_del_object(v___x_3353_);
lean_dec(v_a_3351_);
v_val_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_val_3356_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = lean_io_realpath(v_val_3356_);
return v___x_3357_;
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
lean_dec(v___x_3355_);
v___x_3358_ = ((lean_object*)(l_IO_appDir___closed__0));
v___x_3359_ = lean_string_append(v___x_3358_, v_a_3351_);
lean_dec(v_a_3351_);
v___x_3360_ = ((lean_object*)(l_IO_appDir___closed__1));
v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
v___x_3362_ = lean_mk_io_user_error(v___x_3361_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 1);
lean_ctor_set(v___x_3353_, 0, v___x_3362_);
v___x_3364_ = v___x_3353_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_IO_appDir();
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* v_p_3369_){
_start:
{
uint8_t v___x_3386_; 
v___x_3386_ = l_System_FilePath_isDir(v_p_3369_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_inc_ref(v_p_3369_);
v___x_3387_ = l_System_FilePath_parent(v_p_3369_);
if (lean_obj_tag(v___x_3387_) == 1)
{
lean_object* v_val_3388_; lean_object* v___x_3389_; 
v_val_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_val_3388_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = l_IO_FS_createDirAll(v_val_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_dec_ref(v___x_3389_);
goto v___jp_3371_;
}
else
{
lean_dec_ref(v_p_3369_);
return v___x_3389_;
}
}
else
{
lean_dec(v___x_3387_);
goto v___jp_3371_;
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v_p_3369_);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
return v___x_3391_;
}
v___jp_3371_:
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_io_create_dir(v_p_3369_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_dec_ref(v_p_3369_);
return v___x_3372_;
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3385_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3385_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3385_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
uint8_t v___x_3377_; 
v___x_3377_ = l_System_FilePath_isDir(v_p_3369_);
lean_dec_ref(v_p_3369_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3379_; 
if (v_isShared_3376_ == 0)
{
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3373_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v_a_3373_);
v___x_3381_ = lean_box(0);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3381_);
v___x_3383_ = v___x_3375_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* v_p_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_IO_FS_createDirAll(v_p_3392_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* v_as_3395_, size_t v_sz_3396_, size_t v_i_3397_, lean_object* v_b_3398_){
_start:
{
lean_object* v_a_3401_; uint8_t v___x_3405_; 
v___x_3405_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_b_3398_);
return v___x_3406_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_a_3407_ = lean_array_uget_borrowed(v_as_3395_, v_i_3397_);
lean_inc(v_a_3407_);
v___x_3408_ = l_IO_FS_DirEntry_path(v_a_3407_);
v___x_3409_ = lean_io_symlink_metadata(v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; uint8_t v_type_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; uint8_t v___x_3414_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref(v___x_3409_);
v_type_3411_ = lean_ctor_get_uint8(v_a_3410_, sizeof(void*)*2 + 16);
lean_dec(v_a_3410_);
v___x_3412_ = lean_box(0);
v___x_3413_ = 0;
v___x_3414_ = l_IO_FS_instBEqFileType_beq(v_type_3411_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_io_remove_file(v___x_3408_);
lean_dec_ref(v___x_3408_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_dec_ref(v___x_3415_);
v_a_3401_ = v___x_3412_;
goto v___jp_3400_;
}
else
{
return v___x_3415_;
}
}
else
{
lean_object* v___x_3416_; 
v___x_3416_ = l_IO_FS_removeDirAll(v___x_3408_);
lean_dec_ref(v___x_3408_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_dec_ref(v___x_3416_);
v_a_3401_ = v___x_3412_;
goto v___jp_3400_;
}
else
{
return v___x_3416_;
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v___x_3408_);
v_a_3417_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3409_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3409_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
v___jp_3400_:
{
size_t v___x_3402_; size_t v___x_3403_; 
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3397_, v___x_3402_);
v_i_3397_ = v___x_3403_;
v_b_3398_ = v_a_3401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* v_p_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_io_read_dir(v_p_3425_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; size_t v_sz_3430_; size_t v___x_3431_; lean_object* v___x_3432_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = lean_box(0);
v_sz_3430_ = lean_array_size(v_a_3428_);
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_3428_, v_sz_3430_, v___x_3431_, v___x_3429_);
lean_dec(v_a_3428_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v___x_3433_; 
lean_dec_ref(v___x_3432_);
v___x_3433_ = lean_io_remove_dir(v_p_3425_);
return v___x_3433_;
}
else
{
return v___x_3432_;
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3427_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3427_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* v_p_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_IO_FS_removeDirAll(v_p_3442_);
lean_dec_ref(v_p_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* v_as_3445_, lean_object* v_sz_3446_, lean_object* v_i_3447_, lean_object* v_b_3448_, lean_object* v___y_3449_){
_start:
{
size_t v_sz_boxed_3450_; size_t v_i_boxed_3451_; lean_object* v_res_3452_; 
v_sz_boxed_3450_ = lean_unbox_usize(v_sz_3446_);
lean_dec(v_sz_3446_);
v_i_boxed_3451_ = lean_unbox_usize(v_i_3447_);
lean_dec(v_i_3447_);
v_res_3452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_3445_, v_sz_boxed_3450_, v_i_boxed_3451_, v_b_3448_);
lean_dec_ref(v_as_3445_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* v_toFunctor_3453_, lean_object* v_f_3454_, lean_object* v_inst_3455_, lean_object* v_inst_3456_, lean_object* v___f_3457_, lean_object* v_____x_3458_){
_start:
{
lean_object* v_fst_3459_; lean_object* v_snd_3460_; lean_object* v_map_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v_y_3466_; lean_object* v___x_3467_; 
v_fst_3459_ = lean_ctor_get(v_____x_3458_, 0);
lean_inc(v_fst_3459_);
v_snd_3460_ = lean_ctor_get(v_____x_3458_, 1);
lean_inc(v_snd_3460_);
lean_dec_ref(v_____x_3458_);
v_map_3461_ = lean_ctor_get(v_toFunctor_3453_, 0);
lean_inc(v_map_3461_);
lean_dec_ref(v_toFunctor_3453_);
lean_inc(v_snd_3460_);
v___x_3462_ = lean_apply_2(v_f_3454_, v_fst_3459_, v_snd_3460_);
v___x_3463_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_3463_, 0, v_snd_3460_);
v___x_3464_ = lean_apply_2(v_inst_3455_, lean_box(0), v___x_3463_);
v___f_3465_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3465_, 0, v___x_3464_);
v_y_3466_ = lean_apply_4(v_inst_3456_, lean_box(0), lean_box(0), v___x_3462_, v___f_3465_);
v___x_3467_ = lean_apply_4(v_map_3461_, lean_box(0), lean_box(0), v___f_3457_, v_y_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* v_inst_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_f_3472_){
_start:
{
lean_object* v_toApplicative_3473_; lean_object* v_toBind_3474_; lean_object* v_toFunctor_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___f_3479_; lean_object* v___x_3480_; 
v_toApplicative_3473_ = lean_ctor_get(v_inst_3469_, 0);
lean_inc_ref(v_toApplicative_3473_);
v_toBind_3474_ = lean_ctor_get(v_inst_3469_, 1);
lean_inc(v_toBind_3474_);
lean_dec_ref(v_inst_3469_);
v_toFunctor_3475_ = lean_ctor_get(v_toApplicative_3473_, 0);
lean_inc_ref(v_toFunctor_3475_);
lean_dec_ref(v_toApplicative_3473_);
v___f_3476_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3477_ = ((lean_object*)(l_IO_FS_withTempFile___redArg___closed__0));
lean_inc(v_inst_3471_);
v___x_3478_ = lean_apply_2(v_inst_3471_, lean_box(0), v___x_3477_);
v___f_3479_ = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3479_, 0, v_toFunctor_3475_);
lean_closure_set(v___f_3479_, 1, v_f_3472_);
lean_closure_set(v___f_3479_, 2, v_inst_3471_);
lean_closure_set(v___f_3479_, 3, v_inst_3470_);
lean_closure_set(v___f_3479_, 4, v___f_3476_);
v___x_3480_ = lean_apply_4(v_toBind_3474_, lean_box(0), lean_box(0), v___x_3478_, v___f_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* v_m_3481_, lean_object* v_00_u03b1_3482_, lean_object* v_inst_3483_, lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_f_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_IO_FS_withTempFile___redArg(v_inst_3483_, v_inst_3484_, v_inst_3485_, v_f_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* v_toFunctor_3488_, lean_object* v_f_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v___f_3492_, lean_object* v_path_3493_){
_start:
{
lean_object* v_map_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___f_3498_; lean_object* v_y_3499_; lean_object* v___x_3500_; 
v_map_3494_ = lean_ctor_get(v_toFunctor_3488_, 0);
lean_inc(v_map_3494_);
lean_dec_ref(v_toFunctor_3488_);
lean_inc_ref(v_path_3493_);
v___x_3495_ = lean_apply_1(v_f_3489_, v_path_3493_);
v___x_3496_ = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(v___x_3496_, 0, v_path_3493_);
v___x_3497_ = lean_apply_2(v_inst_3490_, lean_box(0), v___x_3496_);
v___f_3498_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3498_, 0, v___x_3497_);
v_y_3499_ = lean_apply_4(v_inst_3491_, lean_box(0), lean_box(0), v___x_3495_, v___f_3498_);
v___x_3500_ = lean_apply_4(v_map_3494_, lean_box(0), lean_box(0), v___f_3492_, v_y_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* v_inst_3502_, lean_object* v_inst_3503_, lean_object* v_inst_3504_, lean_object* v_f_3505_){
_start:
{
lean_object* v_toApplicative_3506_; lean_object* v_toBind_3507_; lean_object* v_toFunctor_3508_; lean_object* v___f_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; 
v_toApplicative_3506_ = lean_ctor_get(v_inst_3502_, 0);
lean_inc_ref(v_toApplicative_3506_);
v_toBind_3507_ = lean_ctor_get(v_inst_3502_, 1);
lean_inc(v_toBind_3507_);
lean_dec_ref(v_inst_3502_);
v_toFunctor_3508_ = lean_ctor_get(v_toApplicative_3506_, 0);
lean_inc_ref(v_toFunctor_3508_);
lean_dec_ref(v_toApplicative_3506_);
v___f_3509_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3510_ = ((lean_object*)(l_IO_FS_withTempDir___redArg___closed__0));
lean_inc(v_inst_3504_);
v___x_3511_ = lean_apply_2(v_inst_3504_, lean_box(0), v___x_3510_);
v___f_3512_ = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3512_, 0, v_toFunctor_3508_);
lean_closure_set(v___f_3512_, 1, v_f_3505_);
lean_closure_set(v___f_3512_, 2, v_inst_3504_);
lean_closure_set(v___f_3512_, 3, v_inst_3503_);
lean_closure_set(v___f_3512_, 4, v___f_3509_);
v___x_3513_ = lean_apply_4(v_toBind_3507_, lean_box(0), lean_box(0), v___x_3511_, v___f_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* v_m_3514_, lean_object* v_00_u03b1_3515_, lean_object* v_inst_3516_, lean_object* v_inst_3517_, lean_object* v_inst_3518_, lean_object* v_f_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_IO_FS_withTempDir___redArg(v_inst_3516_, v_inst_3517_, v_inst_3518_, v_f_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* v_a_00___x40___internal___hyg_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = lean_io_process_get_current_dir();
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* v_path_3526_, lean_object* v_a_00___x40___internal___hyg_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = lean_io_process_set_current_dir(v_path_3526_);
lean_dec_ref(v_path_3526_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* v_a_00___x40___internal___hyg_3530_){
_start:
{
uint32_t v_res_3531_; lean_object* v_r_3532_; 
v_res_3531_ = lean_io_process_get_pid();
v_r_3532_ = lean_box_uint32(v_res_3531_);
return v_r_3532_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t v_x_3533_){
_start:
{
switch(v_x_3533_)
{
case 0:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_unsigned_to_nat(0u);
return v___x_3534_;
}
case 1:
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
return v___x_3535_;
}
default: 
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_unsigned_to_nat(2u);
return v___x_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object* v_x_3537_){
_start:
{
uint8_t v_x_boxed_3538_; lean_object* v_res_3539_; 
v_x_boxed_3538_ = lean_unbox(v_x_3537_);
v_res_3539_ = l_IO_Process_Stdio_ctorIdx(v_x_boxed_3538_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t v_x_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_IO_Process_Stdio_ctorIdx(v_x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object* v_x_3542_){
_start:
{
uint8_t v_x_4__boxed_3543_; lean_object* v_res_3544_; 
v_x_4__boxed_3543_ = lean_unbox(v_x_3542_);
v_res_3544_ = l_IO_Process_Stdio_toCtorIdx(v_x_4__boxed_3543_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* v_k_3545_){
_start:
{
lean_inc(v_k_3545_);
return v_k_3545_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* v_k_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_3546_);
lean_dec(v_k_3546_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object* v_motive_3548_, lean_object* v_ctorIdx_3549_, uint8_t v_t_3550_, lean_object* v_h_3551_, lean_object* v_k_3552_){
_start:
{
lean_inc(v_k_3552_);
return v_k_3552_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* v_motive_3553_, lean_object* v_ctorIdx_3554_, lean_object* v_t_3555_, lean_object* v_h_3556_, lean_object* v_k_3557_){
_start:
{
uint8_t v_t_boxed_3558_; lean_object* v_res_3559_; 
v_t_boxed_3558_ = lean_unbox(v_t_3555_);
v_res_3559_ = l_IO_Process_Stdio_ctorElim(v_motive_3553_, v_ctorIdx_3554_, v_t_boxed_3558_, v_h_3556_, v_k_3557_);
lean_dec(v_k_3557_);
lean_dec(v_ctorIdx_3554_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* v_piped_3560_){
_start:
{
lean_inc(v_piped_3560_);
return v_piped_3560_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* v_piped_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_3561_);
lean_dec(v_piped_3561_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object* v_motive_3563_, uint8_t v_t_3564_, lean_object* v_h_3565_, lean_object* v_piped_3566_){
_start:
{
lean_inc(v_piped_3566_);
return v_piped_3566_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* v_motive_3567_, lean_object* v_t_3568_, lean_object* v_h_3569_, lean_object* v_piped_3570_){
_start:
{
uint8_t v_t_boxed_3571_; lean_object* v_res_3572_; 
v_t_boxed_3571_ = lean_unbox(v_t_3568_);
v_res_3572_ = l_IO_Process_Stdio_piped_elim(v_motive_3567_, v_t_boxed_3571_, v_h_3569_, v_piped_3570_);
lean_dec(v_piped_3570_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* v_inherit_3573_){
_start:
{
lean_inc(v_inherit_3573_);
return v_inherit_3573_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* v_inherit_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_3574_);
lean_dec(v_inherit_3574_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* v_motive_3576_, uint8_t v_t_3577_, lean_object* v_h_3578_, lean_object* v_inherit_3579_){
_start:
{
lean_inc(v_inherit_3579_);
return v_inherit_3579_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* v_motive_3580_, lean_object* v_t_3581_, lean_object* v_h_3582_, lean_object* v_inherit_3583_){
_start:
{
uint8_t v_t_boxed_3584_; lean_object* v_res_3585_; 
v_t_boxed_3584_ = lean_unbox(v_t_3581_);
v_res_3585_ = l_IO_Process_Stdio_inherit_elim(v_motive_3580_, v_t_boxed_3584_, v_h_3582_, v_inherit_3583_);
lean_dec(v_inherit_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* v_null_3586_){
_start:
{
lean_inc(v_null_3586_);
return v_null_3586_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* v_null_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_IO_Process_Stdio_null_elim___redArg(v_null_3587_);
lean_dec(v_null_3587_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object* v_motive_3589_, uint8_t v_t_3590_, lean_object* v_h_3591_, lean_object* v_null_3592_){
_start:
{
lean_inc(v_null_3592_);
return v_null_3592_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* v_motive_3593_, lean_object* v_t_3594_, lean_object* v_h_3595_, lean_object* v_null_3596_){
_start:
{
uint8_t v_t_boxed_3597_; lean_object* v_res_3598_; 
v_t_boxed_3597_ = lean_unbox(v_t_3594_);
v_res_3598_ = l_IO_Process_Stdio_null_elim(v_motive_3593_, v_t_boxed_3597_, v_h_3595_, v_null_3596_);
lean_dec(v_null_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* v_args_3601_, lean_object* v_a_00___x40___internal___hyg_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = lean_io_process_spawn(v_args_3601_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* v_cfg_3607_, lean_object* v_a_00___x40___internal___hyg_3608_, lean_object* v_a_00___x40___internal___hyg_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = lean_io_process_child_wait(v_cfg_3607_, v_a_00___x40___internal___hyg_3608_);
lean_dec_ref(v_a_00___x40___internal___hyg_3608_);
lean_dec_ref(v_cfg_3607_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* v_cfg_3614_, lean_object* v_a_00___x40___internal___hyg_3615_, lean_object* v_a_00___x40___internal___hyg_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = lean_io_process_child_try_wait(v_cfg_3614_, v_a_00___x40___internal___hyg_3615_);
lean_dec_ref(v_a_00___x40___internal___hyg_3615_);
lean_dec_ref(v_cfg_3614_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* v_cfg_3621_, lean_object* v_a_00___x40___internal___hyg_3622_, lean_object* v_a_00___x40___internal___hyg_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = lean_io_process_child_kill(v_cfg_3621_, v_a_00___x40___internal___hyg_3622_);
lean_dec_ref(v_a_00___x40___internal___hyg_3622_);
lean_dec_ref(v_cfg_3621_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* v_cfg_3628_, lean_object* v_a_00___x40___internal___hyg_3629_, lean_object* v_a_00___x40___internal___hyg_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = lean_io_process_child_take_stdin(v_cfg_3628_, v_a_00___x40___internal___hyg_3629_);
lean_dec_ref(v_cfg_3628_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* v_cfg_3634_, lean_object* v_a_00___x40___internal___hyg_3635_){
_start:
{
uint32_t v_res_3636_; lean_object* v_r_3637_; 
v_res_3636_ = lean_io_process_child_pid(v_cfg_3634_, v_a_00___x40___internal___hyg_3635_);
lean_dec_ref(v_cfg_3634_);
v_r_3637_ = lean_box_uint32(v_res_3636_);
return v_r_3637_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* v_e_3638_){
_start:
{
if (lean_obj_tag(v_e_3638_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3649_; 
v_a_3640_ = lean_ctor_get(v_e_3638_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_e_3638_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3642_ = v_e_3638_;
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v_e_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3644_ = lean_io_error_to_string(v_a_3640_);
v___x_3645_ = lean_mk_io_user_error(v___x_3644_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 1);
lean_ctor_set(v___x_3642_, 0, v___x_3645_);
v___x_3647_ = v___x_3642_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
v_a_3650_ = lean_ctor_get(v_e_3638_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_e_3638_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v_e_3638_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v_e_3638_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 0);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* v_e_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_3658_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* v_00_u03b1_3661_, lean_object* v_e_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* v_00_u03b1_3665_, lean_object* v_e_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_3665_, v_e_3666_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* v_stdout_3669_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_IO_FS_Handle_readToEnd(v_stdout_3669_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 1);
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3671_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3671_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 0);
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* v_stdout_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_IO_Process_output___lam__0(v_stdout_3688_);
lean_dec(v_stdout_3688_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* v_args_3696_, lean_object* v_input_x3f_3697_){
_start:
{
lean_object* v_child_3700_; 
if (lean_obj_tag(v_input_x3f_3697_) == 1)
{
lean_object* v_val_3747_; lean_object* v___x_3748_; lean_object* v_cmd_3749_; lean_object* v_args_3750_; lean_object* v_cwd_3751_; lean_object* v_env_3752_; uint8_t v_inheritEnv_3753_; uint8_t v_setsid_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3801_; 
v_val_3747_ = lean_ctor_get(v_input_x3f_3697_, 0);
v___x_3748_ = ((lean_object*)(l_IO_Process_output___closed__1));
v_cmd_3749_ = lean_ctor_get(v_args_3696_, 1);
v_args_3750_ = lean_ctor_get(v_args_3696_, 2);
v_cwd_3751_ = lean_ctor_get(v_args_3696_, 3);
v_env_3752_ = lean_ctor_get(v_args_3696_, 4);
v_inheritEnv_3753_ = lean_ctor_get_uint8(v_args_3696_, sizeof(void*)*5);
v_setsid_3754_ = lean_ctor_get_uint8(v_args_3696_, sizeof(void*)*5 + 1);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_args_3696_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v_args_3696_, 0);
lean_dec(v_unused_3802_);
v___x_3756_ = v_args_3696_;
v_isShared_3757_ = v_isSharedCheck_3801_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_env_3752_);
lean_inc(v_cwd_3751_);
lean_inc(v_args_3750_);
lean_inc(v_cmd_3749_);
lean_dec(v_args_3696_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3801_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v___x_3748_);
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_cmd_3749_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_args_3750_);
lean_ctor_set(v_reuseFailAlloc_3800_, 3, v_cwd_3751_);
lean_ctor_set(v_reuseFailAlloc_3800_, 4, v_env_3752_);
lean_ctor_set_uint8(v_reuseFailAlloc_3800_, sizeof(void*)*5, v_inheritEnv_3753_);
lean_ctor_set_uint8(v_reuseFailAlloc_3800_, sizeof(void*)*5 + 1, v_setsid_3754_);
v___x_3759_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_io_process_spawn(v___x_3759_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = lean_io_process_child_take_stdin(v___x_3748_, v_a_3761_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v_fst_3764_; lean_object* v_snd_3765_; lean_object* v___x_3766_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v_fst_3764_ = lean_ctor_get(v_a_3763_, 0);
lean_inc(v_fst_3764_);
v_snd_3765_ = lean_ctor_get(v_a_3763_, 1);
lean_inc(v_snd_3765_);
lean_dec(v_a_3763_);
v___x_3766_ = lean_io_prim_handle_put_str(v_fst_3764_, v_val_3747_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3767_; 
lean_dec_ref(v___x_3766_);
v___x_3767_ = lean_io_prim_handle_flush(v_fst_3764_);
lean_dec(v_fst_3764_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_dec_ref(v___x_3767_);
v_child_3700_ = v_snd_3765_;
goto v___jp_3699_;
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v_snd_3765_);
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3767_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v_snd_3765_);
lean_dec(v_fst_3764_);
v_a_3776_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3766_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3766_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3762_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3762_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v_a_3792_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3760_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3760_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
else
{
lean_object* v___x_3803_; lean_object* v_cmd_3804_; lean_object* v_args_3805_; lean_object* v_cwd_3806_; lean_object* v_env_3807_; uint8_t v_inheritEnv_3808_; uint8_t v_setsid_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3826_; 
v___x_3803_ = ((lean_object*)(l_IO_Process_output___closed__0));
v_cmd_3804_ = lean_ctor_get(v_args_3696_, 1);
v_args_3805_ = lean_ctor_get(v_args_3696_, 2);
v_cwd_3806_ = lean_ctor_get(v_args_3696_, 3);
v_env_3807_ = lean_ctor_get(v_args_3696_, 4);
v_inheritEnv_3808_ = lean_ctor_get_uint8(v_args_3696_, sizeof(void*)*5);
v_setsid_3809_ = lean_ctor_get_uint8(v_args_3696_, sizeof(void*)*5 + 1);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_args_3696_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; 
v_unused_3827_ = lean_ctor_get(v_args_3696_, 0);
lean_dec(v_unused_3827_);
v___x_3811_ = v_args_3696_;
v_isShared_3812_ = v_isSharedCheck_3826_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_env_3807_);
lean_inc(v_cwd_3806_);
lean_inc(v_args_3805_);
lean_inc(v_cmd_3804_);
lean_dec(v_args_3696_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3826_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3803_);
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_cmd_3804_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_args_3805_);
lean_ctor_set(v_reuseFailAlloc_3825_, 3, v_cwd_3806_);
lean_ctor_set(v_reuseFailAlloc_3825_, 4, v_env_3807_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*5, v_inheritEnv_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*5 + 1, v_setsid_3809_);
v___x_3814_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_io_process_spawn(v___x_3814_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref(v___x_3815_);
v_child_3700_ = v_a_3816_;
goto v___jp_3699_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
v_a_3817_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3815_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3815_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
}
v___jp_3699_:
{
lean_object* v_stdout_3701_; lean_object* v_stderr_3702_; lean_object* v___f_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_stdout_3701_ = lean_ctor_get(v_child_3700_, 1);
v_stderr_3702_ = lean_ctor_get(v_child_3700_, 2);
lean_inc(v_stdout_3701_);
v___f_3703_ = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3703_, 0, v_stdout_3701_);
v___x_3704_ = lean_unsigned_to_nat(9u);
v___x_3705_ = lean_io_as_task(v___f_3703_, v___x_3704_);
v___x_3706_ = l_IO_FS_Handle_readToEnd(v_stderr_3702_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref(v___x_3706_);
v___x_3708_ = ((lean_object*)(l_IO_Process_output___closed__0));
v___x_3709_ = lean_io_process_child_wait(v___x_3708_, v_child_3700_);
lean_dec_ref(v_child_3700_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v___x_3709_);
v___x_3711_ = lean_task_get_own(v___x_3705_);
v___x_3712_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_3711_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3722_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; uint32_t v___x_3718_; lean_object* v___x_3720_; 
v___x_3717_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3717_, 0, v_a_3713_);
lean_ctor_set(v___x_3717_, 1, v_a_3707_);
v___x_3718_ = lean_unbox_uint32(v_a_3710_);
lean_dec(v_a_3710_);
lean_ctor_set_uint32(v___x_3717_, sizeof(void*)*2, v___x_3718_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3717_);
v___x_3720_ = v___x_3715_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3717_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec(v_a_3710_);
lean_dec(v_a_3707_);
v_a_3723_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3712_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3712_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_a_3707_);
lean_dec_ref(v___x_3705_);
v_a_3731_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3709_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3709_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec_ref(v___x_3705_);
lean_dec_ref(v_child_3700_);
v_a_3739_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3706_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3706_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* v_args_3828_, lean_object* v_input_x3f_3829_, lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_IO_Process_output(v_args_3828_, v_input_x3f_3829_);
lean_dec(v_input_x3f_3829_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* v_args_3835_, lean_object* v_input_x3f_3836_){
_start:
{
lean_object* v___x_3838_; 
lean_inc_ref(v_args_3835_);
v___x_3838_ = l_IO_Process_output(v_args_3835_, v_input_x3f_3836_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3866_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3841_ = v___x_3838_;
v_isShared_3842_ = v_isSharedCheck_3866_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3866_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
uint32_t v_exitCode_3843_; lean_object* v_stdout_3844_; lean_object* v_stderr_3845_; uint32_t v___x_3846_; uint8_t v___x_3847_; 
v_exitCode_3843_ = lean_ctor_get_uint32(v_a_3839_, sizeof(void*)*2);
v_stdout_3844_ = lean_ctor_get(v_a_3839_, 0);
lean_inc_ref(v_stdout_3844_);
v_stderr_3845_ = lean_ctor_get(v_a_3839_, 1);
lean_inc_ref(v_stderr_3845_);
lean_dec(v_a_3839_);
v___x_3846_ = 0;
v___x_3847_ = lean_uint32_dec_eq(v_exitCode_3843_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v_cmd_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
lean_dec_ref(v_stdout_3844_);
v_cmd_3848_ = lean_ctor_get(v_args_3835_, 1);
lean_inc_ref(v_cmd_3848_);
lean_dec_ref(v_args_3835_);
v___x_3849_ = ((lean_object*)(l_IO_Process_run___closed__0));
v___x_3850_ = lean_string_append(v___x_3849_, v_cmd_3848_);
lean_dec_ref(v_cmd_3848_);
v___x_3851_ = ((lean_object*)(l_IO_Process_run___closed__1));
v___x_3852_ = lean_string_append(v___x_3850_, v___x_3851_);
v___x_3853_ = lean_uint32_to_nat(v_exitCode_3843_);
v___x_3854_ = l_Nat_reprFast(v___x_3853_);
v___x_3855_ = lean_string_append(v___x_3852_, v___x_3854_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = ((lean_object*)(l_IO_Process_run___closed__2));
v___x_3857_ = lean_string_append(v___x_3855_, v___x_3856_);
v___x_3858_ = lean_string_append(v___x_3857_, v_stderr_3845_);
lean_dec_ref(v_stderr_3845_);
v___x_3859_ = lean_mk_io_user_error(v___x_3858_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set_tag(v___x_3841_, 1);
lean_ctor_set(v___x_3841_, 0, v___x_3859_);
v___x_3861_ = v___x_3841_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
else
{
lean_object* v___x_3864_; 
lean_dec_ref(v_stderr_3845_);
lean_dec_ref(v_args_3835_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v_stdout_3844_);
v___x_3864_ = v___x_3841_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_stdout_3844_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec_ref(v_args_3835_);
v_a_3867_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3838_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3838_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* v_args_3875_, lean_object* v_input_x3f_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_IO_Process_run(v_args_3875_, v_input_x3f_3876_);
lean_dec(v_input_x3f_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* v_00_u03b1_3882_, lean_object* v_a_00___x40___internal___hyg_3883_, lean_object* v_a_00___x40___internal___hyg_3884_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_3885_; lean_object* v_res_3886_; 
v_a_00___x40___internal___hyg_1__boxed_3885_ = lean_unbox(v_a_00___x40___internal___hyg_3883_);
v_res_3886_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_3885_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_a_00___x40___internal___hyg_3891_, lean_object* v_a_00___x40___internal___hyg_3892_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_3893_; lean_object* v_res_3894_; 
v_a_00___x40___internal___hyg_1__boxed_3893_ = lean_unbox(v_a_00___x40___internal___hyg_3891_);
v_res_3894_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_3893_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* v_a_00___x40___internal___hyg_3896_){
_start:
{
uint64_t v_res_3897_; lean_object* v_r_3898_; 
v_res_3897_ = lean_io_get_tid();
v_r_3898_ = lean_box_uint64(v_res_3897_);
return v_r_3898_;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* v_acc_3899_){
_start:
{
uint32_t v___y_3901_; uint32_t v___y_3902_; uint32_t v___y_3903_; uint8_t v_read_3906_; uint8_t v_write_3907_; uint8_t v_execution_3908_; uint32_t v___y_3910_; uint32_t v___y_3911_; uint32_t v___y_3915_; 
v_read_3906_ = lean_ctor_get_uint8(v_acc_3899_, 0);
v_write_3907_ = lean_ctor_get_uint8(v_acc_3899_, 1);
v_execution_3908_ = lean_ctor_get_uint8(v_acc_3899_, 2);
if (v_read_3906_ == 0)
{
uint32_t v___x_3918_; 
v___x_3918_ = 0;
v___y_3915_ = v___x_3918_;
goto v___jp_3914_;
}
else
{
uint32_t v___x_3919_; 
v___x_3919_ = 4;
v___y_3915_ = v___x_3919_;
goto v___jp_3914_;
}
v___jp_3900_:
{
uint32_t v___x_3904_; uint32_t v___x_3905_; 
v___x_3904_ = lean_uint32_lor(v___y_3902_, v___y_3903_);
v___x_3905_ = lean_uint32_lor(v___y_3901_, v___x_3904_);
return v___x_3905_;
}
v___jp_3909_:
{
if (v_execution_3908_ == 0)
{
uint32_t v___x_3912_; 
v___x_3912_ = 0;
v___y_3901_ = v___y_3910_;
v___y_3902_ = v___y_3911_;
v___y_3903_ = v___x_3912_;
goto v___jp_3900_;
}
else
{
uint32_t v___x_3913_; 
v___x_3913_ = 1;
v___y_3901_ = v___y_3910_;
v___y_3902_ = v___y_3911_;
v___y_3903_ = v___x_3913_;
goto v___jp_3900_;
}
}
v___jp_3914_:
{
if (v_write_3907_ == 0)
{
uint32_t v___x_3916_; 
v___x_3916_ = 0;
v___y_3910_ = v___y_3915_;
v___y_3911_ = v___x_3916_;
goto v___jp_3909_;
}
else
{
uint32_t v___x_3917_; 
v___x_3917_ = 2;
v___y_3910_ = v___y_3915_;
v___y_3911_ = v___x_3917_;
goto v___jp_3909_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* v_acc_3920_){
_start:
{
uint32_t v_res_3921_; lean_object* v_r_3922_; 
v_res_3921_ = l_IO_AccessRight_flags(v_acc_3920_);
lean_dec_ref(v_acc_3920_);
v_r_3922_ = lean_box_uint32(v_res_3921_);
return v_r_3922_;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* v_acc_3923_){
_start:
{
lean_object* v_user_3924_; lean_object* v_group_3925_; lean_object* v_other_3926_; uint32_t v___x_3927_; uint32_t v___x_3928_; uint32_t v_u_3929_; uint32_t v___x_3930_; uint32_t v___x_3931_; uint32_t v_g_3932_; uint32_t v_o_3933_; uint32_t v___x_3934_; uint32_t v___x_3935_; 
v_user_3924_ = lean_ctor_get(v_acc_3923_, 0);
v_group_3925_ = lean_ctor_get(v_acc_3923_, 1);
v_other_3926_ = lean_ctor_get(v_acc_3923_, 2);
v___x_3927_ = l_IO_AccessRight_flags(v_user_3924_);
v___x_3928_ = 6;
v_u_3929_ = lean_uint32_shift_left(v___x_3927_, v___x_3928_);
v___x_3930_ = l_IO_AccessRight_flags(v_group_3925_);
v___x_3931_ = 3;
v_g_3932_ = lean_uint32_shift_left(v___x_3930_, v___x_3931_);
v_o_3933_ = l_IO_AccessRight_flags(v_other_3926_);
v___x_3934_ = lean_uint32_lor(v_g_3932_, v_o_3933_);
v___x_3935_ = lean_uint32_lor(v_u_3929_, v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* v_acc_3936_){
_start:
{
uint32_t v_res_3937_; lean_object* v_r_3938_; 
v_res_3937_ = l_IO_FileRight_flags(v_acc_3936_);
lean_dec_ref(v_acc_3936_);
v_r_3938_ = lean_box_uint32(v_res_3937_);
return v_r_3938_;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* v_filename_3942_, lean_object* v_mode_3943_, lean_object* v_a_00___x40___internal___hyg_3944_){
_start:
{
uint32_t v_mode_boxed_3945_; lean_object* v_res_3946_; 
v_mode_boxed_3945_ = lean_unbox_uint32(v_mode_3943_);
lean_dec(v_mode_3943_);
v_res_3946_ = lean_chmod(v_filename_3942_, v_mode_boxed_3945_);
lean_dec_ref(v_filename_3942_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* v_filename_3947_, lean_object* v_mode_3948_){
_start:
{
uint32_t v___x_3950_; lean_object* v___x_3951_; 
v___x_3950_ = l_IO_FileRight_flags(v_mode_3948_);
v___x_3951_ = lean_chmod(v_filename_3947_, v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* v_filename_3952_, lean_object* v_mode_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_IO_setAccessRights(v_filename_3952_, v_mode_3953_);
lean_dec_ref(v_mode_3953_);
lean_dec_ref(v_filename_3952_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* v_00_u03b1_3956_, lean_object* v_mx_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_apply_1(v_mx_3957_, lean_box(0));
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* v_00_u03b1_3960_, lean_object* v_mx_3961_, lean_object* v_s_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_3960_, v_mx_3961_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* v_a_3966_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_st_mk_ref(v_a_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_IO_mkRef___redArg(v_a_3969_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* v_00_u03b1_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_st_mk_ref(v_a_3973_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* v_00_u03b1_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_IO_mkRef(v_00_u03b1_3976_, v_a_3977_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new(){
_start:
{
uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = 0;
v___x_3982_ = lean_box(v___x_3981_);
v___x_3983_ = lean_st_mk_ref(v___x_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_IO_CancelToken_new();
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object* v_tk_3986_){
_start:
{
uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3988_ = 1;
v___x_3989_ = lean_box(v___x_3988_);
v___x_3990_ = lean_st_ref_set(v_tk_3986_, v___x_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object* v_tk_3991_, lean_object* v_a_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_IO_CancelToken_set(v_tk_3991_);
lean_dec(v_tk_3991_);
return v_res_3993_;
}
}
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object* v_tk_3994_){
_start:
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3996_ = lean_st_ref_get(v_tk_3994_);
v___x_3997_ = lean_unbox(v___x_3996_);
lean_dec(v___x_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object* v_tk_3998_, lean_object* v_a_3999_){
_start:
{
uint8_t v_res_4000_; lean_object* v_r_4001_; 
v_res_4000_ = l_IO_CancelToken_isSet(v_tk_3998_);
lean_dec(v_tk_3998_);
v_r_4001_ = lean_box(v_res_4000_);
return v_r_4001_;
}
}
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object* v_tk_4002_){
_start:
{
lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4004_ = lean_st_ref_get(v_tk_4002_);
lean_dec(v_tk_4002_);
v___x_4005_ = lean_unbox(v___x_4004_);
lean_dec(v___x_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_CancelToken_isSetExport___boxed(lean_object* v_tk_4006_, lean_object* v_a_4007_){
_start:
{
uint8_t v_res_4008_; lean_object* v_r_4009_; 
v_res_4008_ = lean_io_cancel_token_is_set(v_tk_4006_);
v_r_4009_ = lean_box(v_res_4008_);
return v_r_4009_;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* v_h_4010_){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_inc(v_h_4010_);
v___x_4011_ = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(v___x_4011_, 0, v_h_4010_);
lean_inc(v_h_4010_);
v___x_4012_ = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(v___x_4012_, 0, v_h_4010_);
lean_inc(v_h_4010_);
v___x_4013_ = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(v___x_4013_, 0, v_h_4010_);
lean_inc(v_h_4010_);
v___x_4014_ = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(v___x_4014_, 0, v_h_4010_);
lean_inc(v_h_4010_);
v___x_4015_ = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(v___x_4015_, 0, v_h_4010_);
v___x_4016_ = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(v___x_4016_, 0, v_h_4010_);
v___x_4017_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4011_);
lean_ctor_set(v___x_4017_, 1, v___x_4012_);
lean_ctor_set(v___x_4017_, 2, v___x_4013_);
lean_ctor_set(v___x_4017_, 3, v___x_4014_);
lean_ctor_set(v___x_4017_, 4, v___x_4015_);
lean_ctor_set(v___x_4017_, 5, v___x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* v_r_4018_, size_t v_n_4019_){
_start:
{
lean_object* v___x_4021_; lean_object* v_data_4022_; lean_object* v_pos_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4037_; 
v___x_4021_ = lean_st_ref_take(v_r_4018_);
v_data_4022_ = lean_ctor_get(v___x_4021_, 0);
v_pos_4023_ = lean_ctor_get(v___x_4021_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4025_ = v___x_4021_;
v_isShared_4026_ = v_isSharedCheck_4037_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_pos_4023_);
lean_inc(v_data_4022_);
lean_dec(v___x_4021_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4037_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v_data_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4027_ = lean_usize_to_nat(v_n_4019_);
v___x_4028_ = lean_nat_add(v_pos_4023_, v___x_4027_);
lean_dec(v___x_4027_);
lean_inc(v_pos_4023_);
v_data_4029_ = l_ByteArray_extract(v_data_4022_, v_pos_4023_, v___x_4028_);
lean_dec(v___x_4028_);
v___x_4030_ = lean_byte_array_size(v_data_4029_);
v___x_4031_ = lean_nat_add(v_pos_4023_, v___x_4030_);
lean_dec(v_pos_4023_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 1, v___x_4031_);
v___x_4033_ = v___x_4025_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_data_4022_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_st_ref_set(v_r_4018_, v___x_4033_);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v_data_4029_);
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* v_r_4038_, lean_object* v_n_4039_, lean_object* v___y_4040_){
_start:
{
size_t v_n_boxed_4041_; lean_object* v_res_4042_; 
v_n_boxed_4041_ = lean_unbox_usize(v_n_4039_);
lean_dec(v_n_4039_);
v_res_4042_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_4038_, v_n_boxed_4041_);
lean_dec(v_r_4038_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* v_r_4043_, lean_object* v_data_4044_){
_start:
{
lean_object* v___x_4046_; lean_object* v_data_4047_; lean_object* v_pos_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4062_; 
v___x_4046_ = lean_st_ref_take(v_r_4043_);
v_data_4047_ = lean_ctor_get(v___x_4046_, 0);
v_pos_4048_ = lean_ctor_get(v___x_4046_, 1);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4050_ = v___x_4046_;
v_isShared_4051_ = v_isSharedCheck_4062_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_pos_4048_);
lean_inc(v_data_4047_);
lean_dec(v___x_4046_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4062_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4052_ = lean_unsigned_to_nat(0u);
v___x_4053_ = lean_byte_array_size(v_data_4044_);
v___x_4054_ = 0;
lean_inc(v_pos_4048_);
v___x_4055_ = lean_byte_array_copy_slice(v_data_4044_, v___x_4052_, v_data_4047_, v_pos_4048_, v___x_4053_, v___x_4054_);
v___x_4056_ = lean_nat_add(v_pos_4048_, v___x_4053_);
lean_dec(v_pos_4048_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 1, v___x_4056_);
lean_ctor_set(v___x_4050_, 0, v___x_4055_);
v___x_4058_ = v___x_4050_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_st_ref_set(v_r_4043_, v___x_4058_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
return v___x_4060_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* v_r_4063_, lean_object* v_data_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_4063_, v_data_4064_);
lean_dec_ref(v_data_4064_);
lean_dec(v_r_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* v_r_4067_, lean_object* v_s_4068_){
_start:
{
lean_object* v___x_4070_; lean_object* v_data_4071_; lean_object* v_pos_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4087_; 
v___x_4070_ = lean_st_ref_take(v_r_4067_);
v_data_4071_ = lean_ctor_get(v___x_4070_, 0);
v_pos_4072_ = lean_ctor_get(v___x_4070_, 1);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4074_ = v___x_4070_;
v_isShared_4075_ = v_isSharedCheck_4087_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_pos_4072_);
lean_inc(v_data_4071_);
lean_dec(v___x_4070_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4087_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v_data_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4083_; 
v_data_4076_ = lean_string_to_utf8(v_s_4068_);
v___x_4077_ = lean_unsigned_to_nat(0u);
v___x_4078_ = lean_byte_array_size(v_data_4076_);
v___x_4079_ = 0;
lean_inc(v_pos_4072_);
v___x_4080_ = lean_byte_array_copy_slice(v_data_4076_, v___x_4077_, v_data_4071_, v_pos_4072_, v___x_4078_, v___x_4079_);
lean_dec_ref(v_data_4076_);
v___x_4081_ = lean_nat_add(v_pos_4072_, v___x_4078_);
lean_dec(v_pos_4072_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 1, v___x_4081_);
lean_ctor_set(v___x_4074_, 0, v___x_4080_);
v___x_4083_ = v___x_4074_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4080_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_st_ref_set(v_r_4067_, v___x_4083_);
v___x_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* v_r_4088_, lean_object* v_s_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_4088_, v_s_4089_);
lean_dec_ref(v_s_4089_);
lean_dec(v_r_4088_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* v_a_4092_, lean_object* v_i_4093_){
_start:
{
uint8_t v___y_4095_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4100_ = lean_byte_array_size(v_a_4092_);
v___x_4101_ = lean_nat_dec_lt(v_i_4093_, v___x_4100_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; 
lean_dec(v_i_4093_);
v___x_4102_ = lean_box(0);
return v___x_4102_;
}
else
{
uint8_t v___x_4103_; uint8_t v___x_4104_; uint8_t v___x_4105_; 
v___x_4103_ = lean_byte_array_fget(v_a_4092_, v_i_4093_);
v___x_4104_ = 0;
v___x_4105_ = lean_uint8_dec_eq(v___x_4103_, v___x_4104_);
if (v___x_4105_ == 0)
{
uint8_t v___x_4106_; uint8_t v___x_4107_; 
v___x_4106_ = 10;
v___x_4107_ = lean_uint8_dec_eq(v___x_4103_, v___x_4106_);
v___y_4095_ = v___x_4107_;
goto v___jp_4094_;
}
else
{
v___y_4095_ = v___x_4105_;
goto v___jp_4094_;
}
}
v___jp_4094_:
{
if (v___y_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_unsigned_to_nat(1u);
v___x_4097_ = lean_nat_add(v_i_4093_, v___x_4096_);
lean_dec(v_i_4093_);
v_i_4093_ = v___x_4097_;
goto _start;
}
else
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_i_4093_);
return v___x_4099_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* v_a_4108_, lean_object* v_i_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_4108_, v_i_4109_);
lean_dec_ref(v_a_4108_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* v_r_4114_){
_start:
{
lean_object* v___x_4116_; lean_object* v_data_4117_; lean_object* v_pos_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4142_; 
v___x_4116_ = lean_st_ref_take(v_r_4114_);
v_data_4117_ = lean_ctor_get(v___x_4116_, 0);
v_pos_4118_ = lean_ctor_get(v___x_4116_, 1);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4120_ = v___x_4116_;
v_isShared_4121_ = v_isSharedCheck_4142_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_pos_4118_);
lean_inc(v_data_4117_);
lean_dec(v___x_4116_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4142_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___y_4123_; lean_object* v___x_4134_; 
lean_inc(v_pos_4118_);
v___x_4134_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_data_4117_, v_pos_4118_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_byte_array_size(v_data_4117_);
v___y_4123_ = v___x_4135_;
goto v___jp_4122_;
}
else
{
lean_object* v_val_4136_; uint8_t v___x_4137_; uint8_t v___x_4138_; uint8_t v___x_4139_; 
v_val_4136_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_val_4136_);
lean_dec_ref(v___x_4134_);
v___x_4137_ = lean_byte_array_get(v_data_4117_, v_val_4136_);
v___x_4138_ = 0;
v___x_4139_ = lean_uint8_dec_eq(v___x_4137_, v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = lean_unsigned_to_nat(1u);
v___x_4141_ = lean_nat_add(v_val_4136_, v___x_4140_);
lean_dec(v_val_4136_);
v___y_4123_ = v___x_4141_;
goto v___jp_4122_;
}
else
{
v___y_4123_ = v_val_4136_;
goto v___jp_4122_;
}
}
v___jp_4122_:
{
lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4124_ = l_ByteArray_extract(v_data_4117_, v_pos_4118_, v___y_4123_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 1, v___y_4123_);
v___x_4126_ = v___x_4120_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_data_4117_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v___y_4123_);
v___x_4126_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = lean_st_ref_set(v_r_4114_, v___x_4126_);
v___x_4128_ = lean_string_validate_utf8(v___x_4124_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec_ref(v___x_4124_);
v___x_4129_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___lam__3___closed__1));
v___x_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_string_from_utf8_unchecked(v___x_4124_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* v_r_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_4143_);
lean_dec(v_r_4143_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* v___x_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* v___x_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_4149_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* v_r_4154_){
_start:
{
lean_object* v___f_4155_; lean_object* v___f_4156_; lean_object* v___f_4157_; lean_object* v___f_4158_; lean_object* v___f_4159_; lean_object* v___f_4160_; lean_object* v___x_4161_; 
lean_inc(v_r_4154_);
v___f_4155_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4155_, 0, v_r_4154_);
lean_inc(v_r_4154_);
v___f_4156_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4156_, 0, v_r_4154_);
lean_inc(v_r_4154_);
v___f_4157_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4157_, 0, v_r_4154_);
v___f_4158_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4158_, 0, v_r_4154_);
v___f_4159_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___closed__0));
v___f_4160_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___closed__5));
v___x_4161_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4161_, 0, v___f_4159_);
lean_ctor_set(v___x_4161_, 1, v___f_4155_);
lean_ctor_set(v___x_4161_, 2, v___f_4156_);
lean_ctor_set(v___x_4161_, 3, v___f_4158_);
lean_ctor_set(v___x_4161_, 4, v___f_4157_);
lean_ctor_set(v___x_4161_, 5, v___f_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* v_s_4164_, lean_object* v_acc_4165_){
_start:
{
lean_object* v_read_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_read_4167_ = lean_ctor_get(v_s_4164_, 1);
v___x_4168_ = ((lean_object*)(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1));
lean_inc_ref(v_read_4167_);
v___x_4169_ = lean_apply_2(v_read_4167_, v___x_4168_, lean_box(0));
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4183_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4183_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4183_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
uint8_t v___x_4174_; 
v___x_4174_ = l_ByteArray_isEmpty(v_a_4170_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_del_object(v___x_4172_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = lean_byte_array_size(v_acc_4165_);
v___x_4177_ = lean_byte_array_size(v_a_4170_);
v___x_4178_ = lean_byte_array_copy_slice(v_a_4170_, v___x_4175_, v_acc_4165_, v___x_4176_, v___x_4177_, v___x_4174_);
lean_dec(v_a_4170_);
v_acc_4165_ = v___x_4178_;
goto _start;
}
else
{
lean_object* v___x_4181_; 
lean_dec(v_a_4170_);
lean_dec_ref(v_s_4164_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v_acc_4165_);
v___x_4181_ = v___x_4172_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_acc_4165_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
else
{
lean_dec_ref(v_acc_4165_);
lean_dec_ref(v_s_4164_);
return v___x_4169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* v_s_4184_, lean_object* v_acc_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4184_, v_acc_4185_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* v_s_4188_, lean_object* v_buf_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4188_, v_buf_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* v_s_4192_, lean_object* v_buf_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_IO_FS_Stream_readBinToEndInto(v_s_4192_, v_buf_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* v_s_4196_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = l_ByteArray_empty;
v___x_4199_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4196_, v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* v_s_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_IO_FS_Stream_readBinToEnd(v_s_4200_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object* v_s_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_IO_FS_Stream_readBinToEnd(v_s_4206_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4222_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4222_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4222_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
uint8_t v___x_4213_; 
v___x_4213_ = lean_string_validate_utf8(v_a_4209_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
lean_dec(v_a_4209_);
v___x_4214_ = ((lean_object*)(l_IO_FS_Stream_readToEnd___closed__1));
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 1);
lean_ctor_set(v___x_4211_, 0, v___x_4214_);
v___x_4216_ = v___x_4211_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
else
{
lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4218_ = lean_string_from_utf8_unchecked(v_a_4209_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4218_);
v___x_4220_ = v___x_4211_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
v_a_4223_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4208_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4208_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* v_s_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_IO_FS_Stream_readToEnd(v_s_4231_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* v_s_4234_, lean_object* v_lines_4235_){
_start:
{
lean_object* v_getLine_4237_; lean_object* v___x_4238_; 
v_getLine_4237_ = lean_ctor_get(v_s_4234_, 3);
lean_inc_ref(v_getLine_4237_);
v___x_4238_ = lean_apply_1(v_getLine_4237_, lean_box(0));
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4294_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4294_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4294_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___y_4244_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; uint32_t v___y_4251_; uint32_t v___y_4259_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4281_ = lean_string_length(v_a_4239_);
v___x_4282_ = lean_unsigned_to_nat(0u);
v___x_4283_ = lean_nat_dec_eq(v___x_4281_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4284_ = lean_string_utf8_byte_size(v_a_4239_);
lean_inc(v_a_4239_);
v___x_4285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4285_, 0, v_a_4239_);
lean_ctor_set(v___x_4285_, 1, v___x_4282_);
lean_ctor_set(v___x_4285_, 2, v___x_4284_);
v___x_4286_ = l_String_Slice_Pos_prev_x3f(v___x_4285_, v___x_4284_);
if (lean_obj_tag(v___x_4286_) == 0)
{
uint32_t v___x_4287_; 
lean_dec_ref(v___x_4285_);
v___x_4287_ = 65;
v___y_4259_ = v___x_4287_;
goto v___jp_4258_;
}
else
{
lean_object* v_val_4288_; lean_object* v___x_4289_; 
v_val_4288_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_val_4288_);
lean_dec_ref(v___x_4286_);
v___x_4289_ = l_String_Slice_Pos_get_x3f(v___x_4285_, v_val_4288_);
lean_dec(v_val_4288_);
lean_dec_ref(v___x_4285_);
if (lean_obj_tag(v___x_4289_) == 0)
{
uint32_t v___x_4290_; 
v___x_4290_ = 65;
v___y_4259_ = v___x_4290_;
goto v___jp_4258_;
}
else
{
lean_object* v_val_4291_; uint32_t v___x_4292_; 
v_val_4291_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_val_4291_);
lean_dec_ref(v___x_4289_);
v___x_4292_ = lean_unbox_uint32(v_val_4291_);
lean_dec(v_val_4291_);
v___y_4259_ = v___x_4292_;
goto v___jp_4258_;
}
}
}
else
{
lean_object* v___x_4293_; 
lean_del_object(v___x_4241_);
lean_dec(v_a_4239_);
lean_dec_ref(v_s_4234_);
v___x_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4293_, 0, v_lines_4235_);
return v___x_4293_;
}
v___jp_4243_:
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_array_push(v_lines_4235_, v___y_4244_);
v_lines_4235_ = v___x_4245_;
goto _start;
}
v___jp_4247_:
{
uint32_t v___x_4252_; uint8_t v___x_4253_; 
v___x_4252_ = 13;
v___x_4253_ = lean_uint32_dec_eq(v___y_4251_, v___x_4252_);
if (v___x_4253_ == 0)
{
lean_dec(v___y_4250_);
lean_dec(v___y_4248_);
v___y_4244_ = v___y_4249_;
goto v___jp_4243_;
}
else
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4254_ = lean_string_utf8_byte_size(v___y_4249_);
lean_inc(v___y_4248_);
lean_inc_ref(v___y_4249_);
v___x_4255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4255_, 0, v___y_4249_);
lean_ctor_set(v___x_4255_, 1, v___y_4248_);
lean_ctor_set(v___x_4255_, 2, v___x_4254_);
v___x_4256_ = l_String_Slice_Pos_prevn(v___x_4255_, v___x_4254_, v___y_4250_);
lean_dec_ref(v___x_4255_);
v___x_4257_ = lean_string_utf8_extract(v___y_4249_, v___y_4248_, v___x_4256_);
lean_dec(v___x_4256_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4249_);
v___y_4244_ = v___x_4257_;
goto v___jp_4243_;
}
}
v___jp_4258_:
{
uint32_t v___x_4260_; uint8_t v___x_4261_; 
v___x_4260_ = 10;
v___x_4261_ = lean_uint32_dec_eq(v___y_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4264_; 
lean_dec_ref(v_s_4234_);
v___x_4262_ = lean_array_push(v_lines_4235_, v_a_4239_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4262_);
v___x_4264_ = v___x_4241_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
else
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_del_object(v___x_4241_);
v___x_4266_ = lean_unsigned_to_nat(1u);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_string_utf8_byte_size(v_a_4239_);
lean_inc(v_a_4239_);
v___x_4269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4269_, 0, v_a_4239_);
lean_ctor_set(v___x_4269_, 1, v___x_4267_);
lean_ctor_set(v___x_4269_, 2, v___x_4268_);
v___x_4270_ = l_String_Slice_Pos_prevn(v___x_4269_, v___x_4268_, v___x_4266_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = lean_string_utf8_extract(v_a_4239_, v___x_4267_, v___x_4270_);
lean_dec(v___x_4270_);
lean_dec(v_a_4239_);
v___x_4272_ = lean_string_utf8_byte_size(v___x_4271_);
lean_inc_ref(v___x_4271_);
v___x_4273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4267_);
lean_ctor_set(v___x_4273_, 2, v___x_4272_);
v___x_4274_ = l_String_Slice_Pos_prev_x3f(v___x_4273_, v___x_4272_);
if (lean_obj_tag(v___x_4274_) == 0)
{
uint32_t v___x_4275_; 
lean_dec_ref(v___x_4273_);
v___x_4275_ = 65;
v___y_4248_ = v___x_4267_;
v___y_4249_ = v___x_4271_;
v___y_4250_ = v___x_4266_;
v___y_4251_ = v___x_4275_;
goto v___jp_4247_;
}
else
{
lean_object* v_val_4276_; lean_object* v___x_4277_; 
v_val_4276_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_val_4276_);
lean_dec_ref(v___x_4274_);
v___x_4277_ = l_String_Slice_Pos_get_x3f(v___x_4273_, v_val_4276_);
lean_dec(v_val_4276_);
lean_dec_ref(v___x_4273_);
if (lean_obj_tag(v___x_4277_) == 0)
{
uint32_t v___x_4278_; 
v___x_4278_ = 65;
v___y_4248_ = v___x_4267_;
v___y_4249_ = v___x_4271_;
v___y_4250_ = v___x_4266_;
v___y_4251_ = v___x_4278_;
goto v___jp_4247_;
}
else
{
lean_object* v_val_4279_; uint32_t v___x_4280_; 
v_val_4279_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_val_4279_);
lean_dec_ref(v___x_4277_);
v___x_4280_ = lean_unbox_uint32(v_val_4279_);
lean_dec(v_val_4279_);
v___y_4248_ = v___x_4267_;
v___y_4249_ = v___x_4271_;
v___y_4250_ = v___x_4266_;
v___y_4251_ = v___x_4280_;
goto v___jp_4247_;
}
}
}
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec_ref(v_lines_4235_);
lean_dec_ref(v_s_4234_);
v_a_4295_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4238_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4238_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* v_s_4303_, lean_object* v_lines_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_4303_, v_lines_4304_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object* v_s_4307_){
_start:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_4310_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_4307_, v___x_4309_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* v_s_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_IO_FS_Stream_lines(v_s_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* v_bOut_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = lean_st_ref_get(v_bOut_4314_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* v_bOut_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_4317_);
lean_dec(v_bOut_4317_);
return v_res_4319_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4324_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3));
v___x_4325_ = lean_unsigned_to_nat(46u);
v___x_4326_ = lean_unsigned_to_nat(193u);
v___x_4327_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2));
v___x_4328_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1));
v___x_4329_ = l_mkPanicMessageWithDecl(v___x_4328_, v___x_4327_, v___x_4326_, v___x_4325_, v___x_4324_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* v_r_4330_, lean_object* v_toPure_4331_, lean_object* v_bOut_4332_){
_start:
{
lean_object* v___y_4334_; lean_object* v_data_4337_; uint8_t v___x_4338_; 
v_data_4337_ = lean_ctor_get(v_bOut_4332_, 0);
lean_inc_ref(v_data_4337_);
lean_dec_ref(v_bOut_4332_);
v___x_4338_ = lean_string_validate_utf8(v_data_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
lean_dec_ref(v_data_4337_);
v___x_4339_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_4340_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4, &l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once, _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
v___x_4341_ = l_panic___redArg(v___x_4339_, v___x_4340_);
v___y_4334_ = v___x_4341_;
goto v___jp_4333_;
}
else
{
lean_object* v___x_4342_; 
v___x_4342_ = lean_string_from_utf8_unchecked(v_data_4337_);
v___y_4334_ = v___x_4342_;
goto v___jp_4333_;
}
v___jp_4333_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___y_4334_);
lean_ctor_set(v___x_4335_, 1, v_r_4330_);
v___x_4336_ = lean_apply_2(v_toPure_4331_, lean_box(0), v___x_4335_);
return v___x_4336_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* v_toPure_4343_, lean_object* v_inst_4344_, lean_object* v___f_4345_, lean_object* v_toBind_4346_, lean_object* v_r_4347_){
_start:
{
lean_object* v___f_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___f_4348_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4348_, 0, v_r_4347_);
lean_closure_set(v___f_4348_, 1, v_toPure_4343_);
v___x_4349_ = lean_apply_2(v_inst_4344_, lean_box(0), v___f_4345_);
v___x_4350_ = lean_apply_4(v_toBind_4346_, lean_box(0), lean_box(0), v___x_4349_, v___f_4348_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* v_toPure_4351_, lean_object* v_inst_4352_, lean_object* v_toBind_4353_, lean_object* v_bIn_4354_, lean_object* v_inst_4355_, lean_object* v_inst_4356_, uint8_t v_isolateStderr_4357_, lean_object* v_x_4358_, lean_object* v_bOut_4359_){
_start:
{
lean_object* v___f_4360_; lean_object* v___f_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___y_4365_; 
lean_inc(v_bOut_4359_);
v___f_4360_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4360_, 0, v_bOut_4359_);
lean_inc(v_toBind_4353_);
lean_inc(v_inst_4352_);
v___f_4361_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(v___f_4361_, 0, v_toPure_4351_);
lean_closure_set(v___f_4361_, 1, v_inst_4352_);
lean_closure_set(v___f_4361_, 2, v___f_4360_);
lean_closure_set(v___f_4361_, 3, v_toBind_4353_);
v___x_4362_ = l_IO_FS_Stream_ofBuffer(v_bIn_4354_);
v___x_4363_ = l_IO_FS_Stream_ofBuffer(v_bOut_4359_);
if (v_isolateStderr_4357_ == 0)
{
v___y_4365_ = v_x_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4369_; 
lean_inc_ref(v___x_4363_);
lean_inc(v_inst_4352_);
lean_inc(v_inst_4356_);
lean_inc_ref(v_inst_4355_);
v___x_4369_ = l_IO_withStderr___redArg(v_inst_4355_, v_inst_4356_, v_inst_4352_, v___x_4363_, v_x_4358_);
v___y_4365_ = v___x_4369_;
goto v___jp_4364_;
}
v___jp_4364_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
lean_inc(v_inst_4352_);
lean_inc(v_inst_4356_);
lean_inc_ref(v_inst_4355_);
v___x_4366_ = l_IO_withStdout___redArg(v_inst_4355_, v_inst_4356_, v_inst_4352_, v___x_4363_, v___y_4365_);
v___x_4367_ = l_IO_withStdin___redArg(v_inst_4355_, v_inst_4356_, v_inst_4352_, v___x_4362_, v___x_4366_);
v___x_4368_ = lean_apply_4(v_toBind_4353_, lean_box(0), lean_box(0), v___x_4367_, v___f_4361_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* v_toPure_4370_, lean_object* v_inst_4371_, lean_object* v_toBind_4372_, lean_object* v_bIn_4373_, lean_object* v_inst_4374_, lean_object* v_inst_4375_, lean_object* v_isolateStderr_4376_, lean_object* v_x_4377_, lean_object* v_bOut_4378_){
_start:
{
uint8_t v_isolateStderr_boxed_4379_; lean_object* v_res_4380_; 
v_isolateStderr_boxed_4379_ = lean_unbox(v_isolateStderr_4376_);
v_res_4380_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_4370_, v_inst_4371_, v_toBind_4372_, v_bIn_4373_, v_inst_4374_, v_inst_4375_, v_isolateStderr_boxed_4379_, v_x_4377_, v_bOut_4378_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* v_toPure_4381_, lean_object* v_inst_4382_, lean_object* v_toBind_4383_, lean_object* v_inst_4384_, lean_object* v_inst_4385_, uint8_t v_isolateStderr_4386_, lean_object* v_x_4387_, lean_object* v___x_4388_, lean_object* v_bIn_4389_){
_start:
{
lean_object* v___x_4390_; lean_object* v___f_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_box(v_isolateStderr_4386_);
lean_inc(v_toBind_4383_);
v___f_4391_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_4391_, 0, v_toPure_4381_);
lean_closure_set(v___f_4391_, 1, v_inst_4382_);
lean_closure_set(v___f_4391_, 2, v_toBind_4383_);
lean_closure_set(v___f_4391_, 3, v_bIn_4389_);
lean_closure_set(v___f_4391_, 4, v_inst_4384_);
lean_closure_set(v___f_4391_, 5, v_inst_4385_);
lean_closure_set(v___f_4391_, 6, v___x_4390_);
lean_closure_set(v___f_4391_, 7, v_x_4387_);
v___x_4392_ = lean_apply_4(v_toBind_4383_, lean_box(0), lean_box(0), v___x_4388_, v___f_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* v_toPure_4393_, lean_object* v_inst_4394_, lean_object* v_toBind_4395_, lean_object* v_inst_4396_, lean_object* v_inst_4397_, lean_object* v_isolateStderr_4398_, lean_object* v_x_4399_, lean_object* v___x_4400_, lean_object* v_bIn_4401_){
_start:
{
uint8_t v_isolateStderr_boxed_4402_; lean_object* v_res_4403_; 
v_isolateStderr_boxed_4402_ = lean_unbox(v_isolateStderr_4398_);
v_res_4403_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_4393_, v_inst_4394_, v_toBind_4395_, v_inst_4396_, v_inst_4397_, v_isolateStderr_boxed_4402_, v_x_4399_, v___x_4400_, v_bIn_4401_);
return v_res_4403_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = lean_unsigned_to_nat(0u);
v___x_4405_ = l_ByteArray_empty;
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
lean_ctor_set(v___x_4406_, 1, v___x_4404_);
return v___x_4406_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__0, &l_IO_FS_withIsolatedStreams___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__0);
v___x_4408_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_4408_, 0, lean_box(0));
lean_closure_set(v___x_4408_, 1, v___x_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* v_inst_4409_, lean_object* v_inst_4410_, lean_object* v_inst_4411_, lean_object* v_x_4412_, uint8_t v_isolateStderr_4413_){
_start:
{
lean_object* v_toApplicative_4414_; lean_object* v_toBind_4415_; lean_object* v_toPure_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___f_4420_; lean_object* v___x_4421_; 
v_toApplicative_4414_ = lean_ctor_get(v_inst_4409_, 0);
v_toBind_4415_ = lean_ctor_get(v_inst_4409_, 1);
lean_inc(v_toBind_4415_);
v_toPure_4416_ = lean_ctor_get(v_toApplicative_4414_, 1);
lean_inc(v_toPure_4416_);
v___x_4417_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__1, &l_IO_FS_withIsolatedStreams___redArg___closed__1_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__1);
lean_inc(v_inst_4411_);
v___x_4418_ = lean_apply_2(v_inst_4411_, lean_box(0), v___x_4417_);
v___x_4419_ = lean_box(v_isolateStderr_4413_);
lean_inc(v___x_4418_);
lean_inc(v_toBind_4415_);
v___f_4420_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_4420_, 0, v_toPure_4416_);
lean_closure_set(v___f_4420_, 1, v_inst_4411_);
lean_closure_set(v___f_4420_, 2, v_toBind_4415_);
lean_closure_set(v___f_4420_, 3, v_inst_4409_);
lean_closure_set(v___f_4420_, 4, v_inst_4410_);
lean_closure_set(v___f_4420_, 5, v___x_4419_);
lean_closure_set(v___f_4420_, 6, v_x_4412_);
lean_closure_set(v___f_4420_, 7, v___x_4418_);
v___x_4421_ = lean_apply_4(v_toBind_4415_, lean_box(0), lean_box(0), v___x_4418_, v___f_4420_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* v_inst_4422_, lean_object* v_inst_4423_, lean_object* v_inst_4424_, lean_object* v_x_4425_, lean_object* v_isolateStderr_4426_){
_start:
{
uint8_t v_isolateStderr_boxed_4427_; lean_object* v_res_4428_; 
v_isolateStderr_boxed_4427_ = lean_unbox(v_isolateStderr_4426_);
v_res_4428_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_4422_, v_inst_4423_, v_inst_4424_, v_x_4425_, v_isolateStderr_boxed_4427_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* v_m_4429_, lean_object* v_00_u03b1_4430_, lean_object* v_inst_4431_, lean_object* v_inst_4432_, lean_object* v_inst_4433_, lean_object* v_x_4434_, uint8_t v_isolateStderr_4435_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_4431_, v_inst_4432_, v_inst_4433_, v_x_4434_, v_isolateStderr_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* v_m_4437_, lean_object* v_00_u03b1_4438_, lean_object* v_inst_4439_, lean_object* v_inst_4440_, lean_object* v_inst_4441_, lean_object* v_x_4442_, lean_object* v_isolateStderr_4443_){
_start:
{
uint8_t v_isolateStderr_boxed_4444_; lean_object* v_res_4445_; 
v_isolateStderr_boxed_4444_ = lean_unbox(v_isolateStderr_4443_);
v_res_4445_ = l_IO_FS_withIsolatedStreams(v_m_4437_, v_00_u03b1_4438_, v_inst_4439_, v_inst_4440_, v_inst_4441_, v_x_4442_, v_isolateStderr_boxed_4444_);
return v_res_4445_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_4503_ = l_String_toRawSubstring_x27(v___x_4502_);
return v___x_4503_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17(void){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16));
v___x_4519_ = l_String_toRawSubstring_x27(v___x_4518_);
return v___x_4519_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18));
v___x_4533_ = l_String_toRawSubstring_x27(v___x_4532_);
return v___x_4533_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31(void){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30));
v___x_4549_ = l_String_toRawSubstring_x27(v___x_4548_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* v_x_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = ((lean_object*)(l_termPrintln_x21_____00__closed__1));
lean_inc(v_x_4574_);
v___x_4578_ = l_Lean_Syntax_isOfKind(v_x_4574_, v___x_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
lean_dec_ref(v_a_4575_);
lean_dec(v_x_4574_);
v___x_4579_ = lean_box(1);
v___x_4580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v_a_4576_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; uint8_t v___x_4584_; 
v___x_4581_ = lean_unsigned_to_nat(1u);
v___x_4582_ = l_Lean_Syntax_getArg(v_x_4574_, v___x_4581_);
lean_dec(v_x_4574_);
v___x_4583_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1));
lean_inc(v___x_4582_);
v___x_4584_ = l_Lean_Syntax_isOfKind(v___x_4582_, v___x_4583_);
if (v___x_4584_ == 0)
{
lean_object* v_quotContext_4585_; lean_object* v_currMacroScope_4586_; lean_object* v_ref_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v_quotContext_4585_ = lean_ctor_get(v_a_4575_, 1);
lean_inc(v_quotContext_4585_);
v_currMacroScope_4586_ = lean_ctor_get(v_a_4575_, 2);
lean_inc(v_currMacroScope_4586_);
v_ref_4587_ = lean_ctor_get(v_a_4575_, 5);
lean_inc(v_ref_4587_);
lean_dec_ref(v_a_4575_);
v___x_4588_ = l_Lean_SourceInfo_fromRef(v_ref_4587_, v___x_4584_);
lean_dec(v_ref_4587_);
v___x_4589_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_4590_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_4591_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc(v___x_4588_);
v___x_4592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4588_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_4594_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_4595_ = lean_box(0);
lean_inc(v_currMacroScope_4586_);
lean_inc(v_quotContext_4585_);
v___x_4596_ = l_Lean_addMacroScope(v_quotContext_4585_, v___x_4595_, v_currMacroScope_4586_);
v___x_4597_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
lean_inc(v___x_4588_);
v___x_4598_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4588_);
lean_ctor_set(v___x_4598_, 1, v___x_4594_);
lean_ctor_set(v___x_4598_, 2, v___x_4596_);
lean_ctor_set(v___x_4598_, 3, v___x_4597_);
lean_inc(v___x_4588_);
v___x_4599_ = l_Lean_Syntax_node1(v___x_4588_, v___x_4593_, v___x_4598_);
lean_inc(v___x_4588_);
v___x_4600_ = l_Lean_Syntax_node2(v___x_4588_, v___x_4590_, v___x_4592_, v___x_4599_);
v___x_4601_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_4602_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_4603_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
lean_inc(v_currMacroScope_4586_);
lean_inc(v_quotContext_4585_);
v___x_4604_ = l_Lean_addMacroScope(v_quotContext_4585_, v___x_4603_, v_currMacroScope_4586_);
v___x_4605_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
lean_inc(v___x_4588_);
v___x_4606_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4588_);
lean_ctor_set(v___x_4606_, 1, v___x_4602_);
lean_ctor_set(v___x_4606_, 2, v___x_4604_);
lean_ctor_set(v___x_4606_, 3, v___x_4605_);
v___x_4607_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
lean_inc(v___x_4588_);
v___x_4608_ = l_Lean_Syntax_node1(v___x_4588_, v___x_4607_, v___x_4582_);
lean_inc(v___x_4588_);
v___x_4609_ = l_Lean_Syntax_node2(v___x_4588_, v___x_4601_, v___x_4606_, v___x_4608_);
v___x_4610_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
lean_inc(v___x_4588_);
v___x_4611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4588_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_4613_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
lean_inc(v_currMacroScope_4586_);
lean_inc(v_quotContext_4585_);
v___x_4614_ = l_Lean_addMacroScope(v_quotContext_4585_, v___x_4613_, v_currMacroScope_4586_);
v___x_4615_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
lean_inc(v___x_4588_);
v___x_4616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4588_);
lean_ctor_set(v___x_4616_, 1, v___x_4612_);
lean_ctor_set(v___x_4616_, 2, v___x_4614_);
lean_ctor_set(v___x_4616_, 3, v___x_4615_);
v___x_4617_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_4618_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_4619_ = l_Lean_addMacroScope(v_quotContext_4585_, v___x_4618_, v_currMacroScope_4586_);
v___x_4620_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
lean_inc(v___x_4588_);
v___x_4621_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4588_);
lean_ctor_set(v___x_4621_, 1, v___x_4617_);
lean_ctor_set(v___x_4621_, 2, v___x_4619_);
lean_ctor_set(v___x_4621_, 3, v___x_4620_);
lean_inc(v___x_4588_);
v___x_4622_ = l_Lean_Syntax_node1(v___x_4588_, v___x_4607_, v___x_4621_);
lean_inc(v___x_4588_);
v___x_4623_ = l_Lean_Syntax_node2(v___x_4588_, v___x_4601_, v___x_4616_, v___x_4622_);
lean_inc(v___x_4588_);
v___x_4624_ = l_Lean_Syntax_node1(v___x_4588_, v___x_4607_, v___x_4623_);
v___x_4625_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
lean_inc(v___x_4588_);
v___x_4626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4588_);
lean_ctor_set(v___x_4626_, 1, v___x_4625_);
v___x_4627_ = l_Lean_Syntax_node5(v___x_4588_, v___x_4589_, v___x_4600_, v___x_4609_, v___x_4611_, v___x_4624_, v___x_4626_);
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
lean_ctor_set(v___x_4628_, 1, v_a_4576_);
return v___x_4628_;
}
else
{
lean_object* v_quotContext_4629_; lean_object* v_currMacroScope_4630_; lean_object* v_ref_4631_; uint8_t v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v_quotContext_4629_ = lean_ctor_get(v_a_4575_, 1);
lean_inc(v_quotContext_4629_);
v_currMacroScope_4630_ = lean_ctor_get(v_a_4575_, 2);
lean_inc(v_currMacroScope_4630_);
v_ref_4631_ = lean_ctor_get(v_a_4575_, 5);
lean_inc(v_ref_4631_);
lean_dec_ref(v_a_4575_);
v___x_4632_ = 0;
v___x_4633_ = l_Lean_SourceInfo_fromRef(v_ref_4631_, v___x_4632_);
lean_dec(v_ref_4631_);
v___x_4634_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_4635_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_4636_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc(v___x_4633_);
v___x_4637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4633_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
v___x_4638_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_4639_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_4640_ = lean_box(0);
lean_inc(v_currMacroScope_4630_);
lean_inc(v_quotContext_4629_);
v___x_4641_ = l_Lean_addMacroScope(v_quotContext_4629_, v___x_4640_, v_currMacroScope_4630_);
v___x_4642_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
lean_inc(v___x_4633_);
v___x_4643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4633_);
lean_ctor_set(v___x_4643_, 1, v___x_4639_);
lean_ctor_set(v___x_4643_, 2, v___x_4641_);
lean_ctor_set(v___x_4643_, 3, v___x_4642_);
lean_inc(v___x_4633_);
v___x_4644_ = l_Lean_Syntax_node1(v___x_4633_, v___x_4638_, v___x_4643_);
lean_inc(v___x_4633_);
v___x_4645_ = l_Lean_Syntax_node2(v___x_4633_, v___x_4635_, v___x_4637_, v___x_4644_);
v___x_4646_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_4647_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_4648_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
lean_inc(v_currMacroScope_4630_);
lean_inc(v_quotContext_4629_);
v___x_4649_ = l_Lean_addMacroScope(v_quotContext_4629_, v___x_4648_, v_currMacroScope_4630_);
v___x_4650_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
lean_inc(v___x_4633_);
v___x_4651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4633_);
lean_ctor_set(v___x_4651_, 1, v___x_4647_);
lean_ctor_set(v___x_4651_, 2, v___x_4649_);
lean_ctor_set(v___x_4651_, 3, v___x_4650_);
v___x_4652_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_4653_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39));
v___x_4654_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41));
v___x_4655_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42));
lean_inc(v___x_4633_);
v___x_4656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4633_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
lean_inc(v___x_4633_);
v___x_4657_ = l_Lean_Syntax_node2(v___x_4633_, v___x_4654_, v___x_4656_, v___x_4582_);
v___x_4658_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
lean_inc(v___x_4633_);
v___x_4659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4633_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
lean_inc_ref(v___x_4659_);
lean_inc(v___x_4645_);
lean_inc(v___x_4633_);
v___x_4660_ = l_Lean_Syntax_node3(v___x_4633_, v___x_4653_, v___x_4645_, v___x_4657_, v___x_4659_);
lean_inc(v___x_4633_);
v___x_4661_ = l_Lean_Syntax_node1(v___x_4633_, v___x_4652_, v___x_4660_);
lean_inc(v___x_4633_);
v___x_4662_ = l_Lean_Syntax_node2(v___x_4633_, v___x_4646_, v___x_4651_, v___x_4661_);
v___x_4663_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
lean_inc(v___x_4633_);
v___x_4664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4633_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
v___x_4665_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_4666_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
lean_inc(v_currMacroScope_4630_);
lean_inc(v_quotContext_4629_);
v___x_4667_ = l_Lean_addMacroScope(v_quotContext_4629_, v___x_4666_, v_currMacroScope_4630_);
v___x_4668_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
lean_inc(v___x_4633_);
v___x_4669_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4633_);
lean_ctor_set(v___x_4669_, 1, v___x_4665_);
lean_ctor_set(v___x_4669_, 2, v___x_4667_);
lean_ctor_set(v___x_4669_, 3, v___x_4668_);
v___x_4670_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_4671_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_4672_ = l_Lean_addMacroScope(v_quotContext_4629_, v___x_4671_, v_currMacroScope_4630_);
v___x_4673_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
lean_inc(v___x_4633_);
v___x_4674_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4633_);
lean_ctor_set(v___x_4674_, 1, v___x_4670_);
lean_ctor_set(v___x_4674_, 2, v___x_4672_);
lean_ctor_set(v___x_4674_, 3, v___x_4673_);
lean_inc(v___x_4633_);
v___x_4675_ = l_Lean_Syntax_node1(v___x_4633_, v___x_4652_, v___x_4674_);
lean_inc(v___x_4633_);
v___x_4676_ = l_Lean_Syntax_node2(v___x_4633_, v___x_4646_, v___x_4669_, v___x_4675_);
lean_inc(v___x_4633_);
v___x_4677_ = l_Lean_Syntax_node1(v___x_4633_, v___x_4652_, v___x_4676_);
v___x_4678_ = l_Lean_Syntax_node5(v___x_4633_, v___x_4634_, v___x_4645_, v___x_4662_, v___x_4664_, v___x_4677_, v___x_4659_);
v___x_4679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
lean_ctor_set(v___x_4679_, 1, v_a_4576_);
return v___x_4679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* v_00_u03b1_4683_, lean_object* v_a_4684_, lean_object* v_a_00___x40___internal___hyg_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = lean_runtime_mark_multi_threaded(v_a_4684_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* v_00_u03b1_4690_, lean_object* v_a_4691_, lean_object* v_a_00___x40___internal___hyg_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = lean_runtime_mark_persistent(v_a_4691_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* v_00_u03b1_4697_, lean_object* v_a_4698_, lean_object* v_a_00___x40___internal___hyg_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = lean_runtime_forget(v_a_4698_);
return v_res_4700_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IOError(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_RealWorld_nonemptyType = _init_l_IO_RealWorld_nonemptyType();
l_instMonadBaseIO = _init_l_instMonadBaseIO();
lean_mark_persistent(l_instMonadBaseIO);
l_IO_instInhabitedTaskState_default = _init_l_IO_instInhabitedTaskState_default();
l_IO_instInhabitedTaskState = _init_l_IO_instInhabitedTaskState();
l_IO_instLTTaskState = _init_l_IO_instLTTaskState();
lean_mark_persistent(l_IO_instLTTaskState);
l_IO_instLETaskState = _init_l_IO_instLETaskState();
lean_mark_persistent(l_IO_instLETaskState);
l_IO_FS_instInhabitedSystemTime_default = _init_l_IO_FS_instInhabitedSystemTime_default();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime_default);
l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
lean_mark_persistent(l_IO_FS_instLTSystemTime);
l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
lean_mark_persistent(l_IO_FS_instLESystemTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_IO_waitAny___auto__1 = _init_l_IO_waitAny___auto__1();
lean_mark_persistent(l_IO_waitAny___auto__1);
l_IO_waitAny_x27___auto__1 = _init_l_IO_waitAny_x27___auto__1();
lean_mark_persistent(l_IO_waitAny_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_System_IOError(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_IO(builtin);
}
#ifdef __cplusplus
}
#endif
