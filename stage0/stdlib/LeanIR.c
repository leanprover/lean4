// Lean compiler output
// Module: LeanIR
// Imports: public import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.IR.CompilerM import all Lean.Compiler.CSimpAttr import Lean.Compiler.IR.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt
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
lean_object* lean_ir_export_entries(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__exportIREntries___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_LeanIR_0__mkIRData___closed__0;
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "invalid trailing argument `"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__0 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__0_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`, expected argument of the form `-Dopt=val`"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__1 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__1_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__2 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__2_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_LeanIR_0__setConfigOption___closed__3;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown option '"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__4 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__4_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__5 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__5_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid -D parameter, argument must contain '='"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__6 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__6_value;
static const lean_ctor_object l___private_LeanIR_0__setConfigOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanIR_0__setConfigOption___closed__6_value)}};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__7 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__7_value;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_String_Slice_toName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_saveState___redArg(lean_object*);
lean_object* l_Lean_compileDeclsImpl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__main_doCompile(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__main_doCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_panic___at___00main_spec__1___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_spec__28(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr();
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__7_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__7_spec__17___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__7___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__6_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27_spec__37___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__7___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__6___closed__0;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1;
extern lean_object* l_Lean_trace_profiler_output;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_impureSigExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00main_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00main_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00main_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_postponedCompileDeclsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "usage: leanir <setup.json> <module> <output.ir> <output.c> <-Dopt=val>..."};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_main___closed__4;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_ctor_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__5_value),LEAN_SCALAR_PTR_LITERAL(157, 0, 67, 166, 172, 92, 38, 85)}};
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
static const lean_string_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
static lean_object* l_main___closed__10;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
static lean_object* l_main___closed__11;
extern lean_object* l_Lean_instInhabitedClassState_default;
static lean_object* l_main___closed__12;
static lean_object* l_main___closed__13;
static const lean_ctor_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_main___closed__15;
static lean_object* l_main___closed__16;
static lean_object* l_main___closed__17;
lean_object* l_Array_instInhabited(lean_object*);
static lean_object* l_main___closed__18;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static lean_object* l_main___closed__20;
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_main___closed__21;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_ctor_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__22_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static lean_object* l_main___closed__25;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "module '"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' not found"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
static uint8_t l_main___closed__28;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_saveModuleData(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* l_Lean_IR_emitC(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* lean_init_search_path();
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_CSimp_ext;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Meta_instanceExtension;
extern lean_object* l_Lean_classExtension;
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27_spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__exportIREntries___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ir_export_entries(x_1);
return x_2;
}
}
static lean_object* _init_l___private_LeanIR_0__mkIRData___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_3 = 2;
lean_inc_ref(x_1);
x_4 = l_Lean_mkModuleData(x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Environment_header(x_1);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_7);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_6, 4);
x_12 = lean_ctor_get(x_6, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = 1;
lean_inc_ref(x_1);
x_17 = lean_get_ir_extra_const_names(x_1, x_3, x_16);
x_18 = l___private_LeanIR_0__mkIRData___closed__0;
x_19 = lean_ir_export_entries(x_1);
x_20 = l_Array_append___redArg(x_19, x_11);
lean_dec_ref(x_11);
lean_ctor_set(x_6, 4, x_20);
lean_ctor_set(x_6, 3, x_17);
lean_ctor_set(x_6, 2, x_18);
lean_ctor_set(x_6, 1, x_18);
lean_ctor_set(x_6, 0, x_9);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_8);
return x_4;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_6, 4);
lean_inc(x_21);
lean_dec(x_6);
x_22 = 1;
lean_inc_ref(x_1);
x_23 = lean_get_ir_extra_const_names(x_1, x_3, x_22);
x_24 = l___private_LeanIR_0__mkIRData___closed__0;
x_25 = lean_ir_export_entries(x_1);
x_26 = l_Array_append___redArg(x_25, x_21);
lean_dec_ref(x_21);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_8);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = l_Lean_Environment_header(x_1);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*7 + 4);
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
x_34 = 1;
lean_inc_ref(x_1);
x_35 = lean_get_ir_extra_const_names(x_1, x_3, x_34);
x_36 = l___private_LeanIR_0__mkIRData___closed__0;
x_37 = lean_ir_export_entries(x_1);
x_38 = l_Array_append___redArg(x_37, x_32);
lean_dec_ref(x_32);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 5, 1);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_30);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_LeanIR_0__mkIRData(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
lean_dec(x_5);
x_10 = 61;
x_11 = lean_nat_add(x_2, x_4);
x_12 = lean_string_utf8_get_fast(x_3, x_11);
x_13 = lean_uint32_dec_eq(x_12, x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_string_utf8_next_fast(x_3, x_11);
lean_dec(x_11);
x_16 = lean_nat_sub(x_15, x_2);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_LeanIR_0__setConfigOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
x_12 = lean_string_utf8_byte_size(x_2);
x_13 = l___private_LeanIR_0__setConfigOption___closed__3;
x_14 = lean_nat_dec_le(x_13, x_12);
if (x_14 == 0)
{
lean_dec_ref(x_1);
goto block_10;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_string_memcmp(x_2, x_11, x_15, x_15, x_13);
if (x_16 == 0)
{
lean_dec_ref(x_1);
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_17 = lean_unsigned_to_nat(2u);
lean_inc_ref(x_2);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_12);
x_19 = l_String_Slice_Pos_nextn(x_18, x_15, x_17);
lean_dec_ref(x_18);
lean_inc(x_19);
lean_inc_ref(x_2);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_19);
lean_ctor_set(x_66, 2, x_12);
x_67 = lean_box(0);
x_68 = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(x_66, x_19, x_2, x_15, x_67);
lean_dec_ref(x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_nat_sub(x_12, x_19);
x_20 = x_69;
goto block_65;
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec_ref(x_68);
x_20 = x_70;
goto block_65;
}
block_65:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_nat_sub(x_12, x_19);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_getOptionDecls();
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_nat_add(x_19, x_20);
lean_dec(x_20);
lean_inc(x_26);
lean_inc(x_19);
lean_inc_ref(x_2);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_String_Slice_toName(x_27);
lean_dec_ref(x_27);
x_29 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_25, x_28);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_string_utf8_next_fast(x_2, x_26);
lean_dec(x_26);
x_32 = lean_nat_sub(x_31, x_19);
x_33 = lean_nat_add(x_19, x_32);
lean_dec(x_32);
lean_dec(x_19);
x_34 = lean_string_utf8_extract(x_2, x_33, x_12);
lean_dec(x_33);
lean_dec_ref(x_2);
x_35 = l_Lean_Language_Lean_setOption(x_1, x_30, x_28, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_36 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
x_37 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_28, x_16);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_41);
return x_23;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_nat_add(x_19, x_20);
lean_dec(x_20);
lean_inc(x_43);
lean_inc(x_19);
lean_inc_ref(x_2);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_19);
lean_ctor_set(x_44, 2, x_43);
x_45 = l_String_Slice_toName(x_44);
lean_dec_ref(x_44);
x_46 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_42, x_45);
lean_dec(x_42);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_string_utf8_next_fast(x_2, x_43);
lean_dec(x_43);
x_49 = lean_nat_sub(x_48, x_19);
x_50 = lean_nat_add(x_19, x_49);
lean_dec(x_49);
lean_dec(x_19);
x_51 = lean_string_utf8_extract(x_2, x_50, x_12);
lean_dec(x_50);
lean_dec_ref(x_2);
x_52 = l_Lean_Language_Lean_setOption(x_1, x_47, x_45, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
x_54 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_45, x_16);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
return x_23;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_23, 0);
lean_inc(x_61);
lean_dec(x_23);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__7));
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
x_5 = lean_string_append(x_4, x_2);
lean_dec_ref(x_2);
x_6 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_LeanIR_0__setConfigOption(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__main_doCompile(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_saveState___redArg(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
lean_inc(x_4);
x_8 = l_Lean_compileDeclsImpl(x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_19; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_19 = l_Lean_Exception_isInterrupt(x_9);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_9);
x_20 = l_Lean_Exception_isRuntime(x_9);
x_10 = x_20;
goto block_18;
}
else
{
x_10 = x_19;
goto block_18;
}
block_18:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_8);
x_11 = l_Lean_Core_SavedState_restore___redArg(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
if (x_1 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
}
else
{
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_8;
}
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__main_doCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_LeanIR_0__main_doCompile(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_panic___at___00main_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instInhabitedError;
x_2 = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_panic___at___00main_spec__1___closed__0;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00main_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00main_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00main_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_mk_io_user_error(x_4);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_mk_io_user_error(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00main_spec__9___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00main_spec__9___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00main_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00main_spec__9(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_name_eq(x_15, x_1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 2;
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_17);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
uint8_t x_18; 
x_18 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_18);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_name_eq(x_24, x_1);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
x_26 = 2;
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_23);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_28);
x_29 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_23);
lean_ctor_set(x_3, 1, x_29);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_6, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_35 = x_6;
} else {
 lean_dec_ref(x_6);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_name_eq(x_36, x_1);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 2;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(0, 3, 2);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_33);
lean_ctor_set_uint8(x_40, sizeof(void*)*3 + 1, x_34);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
if (lean_is_scalar(x_35)) {
 x_43 = lean_alloc_ctor(0, 3, 2);
} else {
 x_43 = x_35;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_33);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_34);
lean_ctor_set(x_3, 1, x_43);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_47 = lean_name_eq(x_44, x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(x_1, x_2, x_46);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_44);
x_50 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_45, sizeof(void*)*3);
x_56 = lean_ctor_get_uint8(x_45, sizeof(void*)*3 + 1);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_57 = x_45;
} else {
 lean_dec_ref(x_45);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_name_eq(x_58, x_1);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = 2;
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 1, 1);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 3, 2);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_54);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_55);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 1, x_56);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_46);
return x_63;
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = 0;
if (lean_is_scalar(x_52)) {
 x_65 = lean_alloc_ctor(0, 1, 1);
} else {
 x_65 = x_52;
}
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(0, 3, 2);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_53);
lean_ctor_set(x_66, 2, x_54);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_55);
lean_ctor_set_uint8(x_66, sizeof(void*)*3 + 1, x_56);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_46);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Name_hash___override(x_3);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(x_3, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = lean_array_uset(x_5, x_18, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(x_1, x_3, x_19);
x_27 = lean_array_uset(x_25, x_18, x_26);
lean_ctor_set(x_2, 1, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_array_uset(x_5, x_18, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3_spec__3(x_1, x_3, x_19);
x_31 = lean_array_uset(x_29, x_18, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_st_mk_ref(x_1);
lean_inc(x_10);
x_11 = l_Lean_importModulesCore(x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec_ref(x_11);
x_12 = lean_st_ref_get(x_10);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_6);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3(x_6, x_14, x_6);
lean_dec(x_6);
lean_ctor_set(x_12, 0, x_15);
x_16 = 0;
x_17 = 0;
x_18 = 0;
x_19 = l_Lean_instDecidableEqOLeanLevel(x_18, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_finalizeImport(x_12, x_2, x_7, x_16, x_8, x_17, x_18, x_8);
lean_dec_ref(x_12);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_finalizeImport(x_12, x_2, x_7, x_16, x_8, x_17, x_18, x_17);
lean_dec_ref(x_12);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
lean_inc(x_6);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__3(x_6, x_22, x_6);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = 0;
x_27 = 0;
x_28 = 0;
x_29 = l_Lean_instDecidableEqOLeanLevel(x_28, x_3);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_finalizeImport(x_25, x_2, x_7, x_26, x_8, x_27, x_28, x_8);
lean_dec_ref(x_25);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_finalizeImport(x_25, x_2, x_7, x_26, x_8, x_27, x_28, x_27);
lean_dec_ref(x_25);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_5);
x_12 = lean_unbox(x_8);
x_13 = l_main___lam__0(x_1, x_2, x_10, x_4, x_11, x_6, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_spec__28(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_7, x_6, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_spec__28(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_7, x_6, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_spec__28(x_1, x_10, x_3, x_8);
return x_11;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l___private_LeanIR_0__setConfigOption(x_2, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00main_spec__2___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_LCNF_setDeclPublic(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__7_spec__17(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stderr();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__7_spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___00IO_eprintln___at___00main_spec__7_spec__17(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__7(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___00IO_eprintln___at___00main_spec__7_spec__17(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___00main_spec__7(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_8 = 0;
x_9 = lean_array_uget(x_1, x_3);
x_10 = l_Lean_Message_toString(x_9, x_8);
x_11 = l_IO_eprintln___at___00main_spec__7(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___closed__0));
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_8 = 0;
x_9 = lean_array_uget(x_1, x_3);
x_10 = l_Lean_Message_toString(x_9, x_8);
x_11 = l_IO_eprintln___at___00main_spec__7(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42___closed__0));
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28_spec__42(x_1, x_2, x_14, x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_array_size(x_6);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27(x_1, x_6, x_9, x_10, x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_16; 
lean_inc_ref(x_14);
lean_dec(x_13);
lean_free_object(x_2);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_18);
lean_dec(x_17);
lean_free_object(x_2);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_free_object(x_2);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_array_size(x_26);
x_30 = 0;
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27(x_1, x_26, x_29, x_30, x_28);
lean_dec_ref(x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_inc_ref(x_34);
lean_dec(x_32);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec_ref(x_34);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_41 = x_31;
} else {
 lean_dec_ref(x_31);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
x_47 = lean_array_size(x_44);
x_48 = 0;
x_49 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28(x_44, x_47, x_48, x_46);
lean_dec_ref(x_44);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_51, 0);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_ctor_set(x_2, 0, x_53);
lean_ctor_set(x_49, 0, x_2);
return x_49;
}
else
{
lean_object* x_54; 
lean_inc_ref(x_52);
lean_dec(x_51);
lean_free_object(x_2);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_55, 0);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_2, 0, x_57);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_2);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_inc_ref(x_56);
lean_dec(x_55);
lean_free_object(x_2);
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec_ref(x_56);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_2);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
return x_49;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec(x_2);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
x_67 = lean_array_size(x_64);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__28(x_64, x_67, x_68, x_66);
lean_dec_ref(x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_70, 0);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_inc_ref(x_72);
lean_dec(x_70);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec_ref(x_72);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_79 = x_69;
} else {
 lean_dec_ref(x_69);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = lean_array_uget(x_2, x_4);
lean_inc(x_10);
x_13 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19(x_1, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_free_object(x_13);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(0);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_18);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_10);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_box(0);
lean_ctor_set(x_5, 1, x_25);
lean_ctor_set(x_5, 0, x_26);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_4 = x_28;
goto _start;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_5);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_array_uget(x_2, x_4);
lean_inc(x_33);
x_35 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19(x_1, x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_37);
lean_dec(x_33);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec_ref(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = 1;
x_45 = lean_usize_add(x_4, x_44);
x_4 = x_45;
x_5 = x_43;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19_spec__27(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_8 = 0;
x_9 = lean_array_uget(x_1, x_3);
x_10 = l_Lean_Message_toString(x_9, x_8);
x_11 = l_IO_eprintln___at___00main_spec__7(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___closed__0));
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_8 = 0;
x_9 = lean_array_uget(x_1, x_3);
x_10 = l_Lean_Message_toString(x_9, x_8);
x_11 = l_IO_eprintln___at___00main_spec__7(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30___closed__0));
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20_spec__30(x_1, x_2, x_14, x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__19(x_2, x_4, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
lean_free_object(x_6);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_array_size(x_5);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20(x_5, x_13, x_14, x_12);
lean_dec_ref(x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_22);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_size(x_5);
x_37 = 0;
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__8_spec__20(x_5, x_36, x_37, x_35);
lean_dec_ref(x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_inc_ref(x_41);
lean_dec(x_39);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec_ref(x_41);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_47 = x_38;
} else {
 lean_dec_ref(x_38);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_5);
x_49 = !lean_is_exclusive(x_6);
if (x_49 == 0)
{
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_6, 0);
lean_inc(x_50);
lean_dec(x_6);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forIn___at___00main_spec__8(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2;
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 4, x_16);
x_17 = lean_st_ref_set(x_1, x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_25);
lean_ctor_set(x_32, 7, x_26);
lean_ctor_set(x_32, 8, x_27);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_nat_dec_lt(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__0));
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__1));
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
return x_1;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__2));
x_14 = lean_string_dec_eq(x_7, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__3));
x_16 = lean_string_dec_eq(x_7, x_15);
if (x_16 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_6, 1);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__4));
x_22 = lean_string_dec_eq(x_20, x_21);
if (x_22 == 0)
{
return x_1;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__5));
x_24 = lean_string_dec_eq(x_19, x_23);
if (x_24 == 0)
{
return x_1;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__6));
x_26 = lean_string_dec_eq(x_18, x_25);
if (x_26 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_string_dec_eq(x_27, x_3);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0(x_5, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_6);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_array_uget(x_2, x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; double x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_box(0);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__0;
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1));
x_27 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_float(x_27, sizeof(void*)*2, x_25);
lean_ctor_set_float(x_27, sizeof(void*)*2 + 8, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 16, x_15);
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_31 = lean_box(0);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2));
x_33 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__3));
x_34 = l_Lean_MessageData_nil;
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_19);
lean_ctor_set_tag(x_18, 8);
lean_ctor_set(x_18, 1, x_35);
lean_ctor_set(x_18, 0, x_33);
x_36 = 0;
lean_inc_ref(x_29);
lean_inc_ref(x_28);
x_37 = l_Lean_Elab_mkMessageCore(x_28, x_29, x_18, x_36, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_30 == 0)
{
lean_inc_ref(x_6);
x_38 = x_6;
x_39 = x_7;
x_40 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_37, 4);
lean_inc(x_93);
x_94 = lean_box(x_1);
x_95 = lean_box(x_30);
x_96 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___boxed), 4, 3);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_95);
lean_closure_set(x_96, 2, x_32);
x_97 = l_Lean_MessageData_hasTag(x_96, x_93);
if (x_97 == 0)
{
lean_dec_ref(x_37);
lean_dec(x_20);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_inc_ref(x_6);
x_38 = x_6;
x_39 = x_7;
x_40 = lean_box(0);
goto block_92;
}
}
block_92:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_take(x_39);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_37, 4);
x_44 = lean_ctor_get(x_38, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 7);
lean_inc(x_45);
lean_dec_ref(x_38);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_41, 6);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_20;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_37, 4, x_49);
x_50 = l_Lean_MessageLog_add(x_37, x_47);
lean_ctor_set(x_41, 6, x_50);
x_51 = lean_st_ref_set(x_39, x_41);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
x_54 = lean_ctor_get(x_41, 2);
x_55 = lean_ctor_get(x_41, 3);
x_56 = lean_ctor_get(x_41, 4);
x_57 = lean_ctor_get(x_41, 5);
x_58 = lean_ctor_get(x_41, 6);
x_59 = lean_ctor_get(x_41, 7);
x_60 = lean_ctor_get(x_41, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
if (lean_is_scalar(x_20)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_20;
}
lean_ctor_set(x_61, 0, x_44);
lean_ctor_set(x_61, 1, x_45);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_43);
lean_ctor_set(x_37, 4, x_62);
x_63 = l_Lean_MessageLog_add(x_37, x_58);
x_64 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_54);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set(x_64, 4, x_56);
lean_ctor_set(x_64, 5, x_57);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_64, 7, x_59);
lean_ctor_set(x_64, 8, x_60);
x_65 = lean_st_ref_set(x_39, x_64);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = lean_ctor_get(x_37, 1);
x_68 = lean_ctor_get(x_37, 2);
x_69 = lean_ctor_get_uint8(x_37, sizeof(void*)*5);
x_70 = lean_ctor_get_uint8(x_37, sizeof(void*)*5 + 1);
x_71 = lean_ctor_get_uint8(x_37, sizeof(void*)*5 + 2);
x_72 = lean_ctor_get(x_37, 3);
x_73 = lean_ctor_get(x_37, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_37);
x_74 = lean_ctor_get(x_38, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 7);
lean_inc(x_75);
lean_dec_ref(x_38);
x_76 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_41, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_41, 3);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_41, 4);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_41, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_41, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_41, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_41, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 lean_ctor_release(x_41, 7);
 lean_ctor_release(x_41, 8);
 x_85 = x_41;
} else {
 lean_dec_ref(x_41);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_20;
}
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_75);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_73);
x_88 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_88, 0, x_66);
lean_ctor_set(x_88, 1, x_67);
lean_ctor_set(x_88, 2, x_68);
lean_ctor_set(x_88, 3, x_72);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*5, x_69);
lean_ctor_set_uint8(x_88, sizeof(void*)*5 + 1, x_70);
lean_ctor_set_uint8(x_88, sizeof(void*)*5 + 2, x_71);
x_89 = l_Lean_MessageLog_add(x_88, x_82);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 9, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_77);
lean_ctor_set(x_90, 2, x_78);
lean_ctor_set(x_90, 3, x_79);
lean_ctor_set(x_90, 4, x_80);
lean_ctor_set(x_90, 5, x_81);
lean_ctor_set(x_90, 6, x_89);
lean_ctor_set(x_90, 7, x_83);
lean_ctor_set(x_90, 8, x_84);
x_91 = lean_st_ref_set(x_39, x_90);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; double x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_98 = lean_ctor_get(x_18, 0);
x_99 = lean_ctor_get(x_18, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_18);
x_100 = lean_box(0);
x_101 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__0;
x_102 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1));
x_103 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_float(x_103, sizeof(void*)*2, x_101);
lean_ctor_set_float(x_103, sizeof(void*)*2 + 8, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 16, x_15);
x_104 = lean_ctor_get(x_6, 0);
x_105 = lean_ctor_get(x_6, 1);
x_106 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_107 = lean_box(0);
x_108 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2));
x_109 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__3));
x_110 = l_Lean_MessageData_nil;
x_111 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_19);
x_112 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = 0;
lean_inc_ref(x_105);
lean_inc_ref(x_104);
x_114 = l_Lean_Elab_mkMessageCore(x_104, x_105, x_112, x_113, x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_106 == 0)
{
lean_inc_ref(x_6);
x_115 = x_6;
x_116 = x_7;
x_117 = lean_box(0);
goto block_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_114, 4);
lean_inc(x_147);
x_148 = lean_box(x_1);
x_149 = lean_box(x_106);
x_150 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___boxed), 4, 3);
lean_closure_set(x_150, 0, x_148);
lean_closure_set(x_150, 1, x_149);
lean_closure_set(x_150, 2, x_108);
x_151 = l_Lean_MessageData_hasTag(x_150, x_147);
if (x_151 == 0)
{
lean_dec_ref(x_114);
lean_dec(x_20);
x_9 = x_107;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_inc_ref(x_6);
x_115 = x_6;
x_116 = x_7;
x_117 = lean_box(0);
goto block_146;
}
}
block_146:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_118 = lean_st_ref_take(x_116);
x_119 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_114, 2);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_114, sizeof(void*)*5);
x_123 = lean_ctor_get_uint8(x_114, sizeof(void*)*5 + 1);
x_124 = lean_ctor_get_uint8(x_114, sizeof(void*)*5 + 2);
x_125 = lean_ctor_get(x_114, 3);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_114, 4);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_115, 6);
lean_inc(x_128);
x_129 = lean_ctor_get(x_115, 7);
lean_inc(x_129);
lean_dec_ref(x_115);
x_130 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_118, 2);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_118, 3);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_118, 4);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_118, 5);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_118, 6);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_118, 7);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_118, 8);
lean_inc_ref(x_138);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 lean_ctor_release(x_118, 8);
 x_139 = x_118;
} else {
 lean_dec_ref(x_118);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_20;
}
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_129);
x_141 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
if (lean_is_scalar(x_127)) {
 x_142 = lean_alloc_ctor(0, 5, 3);
} else {
 x_142 = x_127;
}
lean_ctor_set(x_142, 0, x_119);
lean_ctor_set(x_142, 1, x_120);
lean_ctor_set(x_142, 2, x_121);
lean_ctor_set(x_142, 3, x_125);
lean_ctor_set(x_142, 4, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*5, x_122);
lean_ctor_set_uint8(x_142, sizeof(void*)*5 + 1, x_123);
lean_ctor_set_uint8(x_142, sizeof(void*)*5 + 2, x_124);
x_143 = l_Lean_MessageLog_add(x_142, x_136);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 9, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_131);
lean_ctor_set(x_144, 2, x_132);
lean_ctor_set(x_144, 3, x_133);
lean_ctor_set(x_144, 4, x_134);
lean_ctor_set(x_144, 5, x_135);
lean_ctor_set(x_144, 6, x_143);
lean_ctor_set(x_144, 7, x_137);
lean_ctor_set(x_144, 8, x_138);
x_145 = lean_st_ref_set(x_116, x_144);
x_9 = x_107;
x_10 = lean_box(0);
goto block_14;
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__14___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__14(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__14(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_nat_dec_eq(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_4);
x_8 = lean_uint64_of_nat(x_5);
x_9 = lean_uint64_of_nat(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_4, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg(x_2, x_3, x_22);
lean_dec(x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_nat_dec_eq(x_13, x_15);
if (x_17 == 0)
{
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_14, x_16);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_nat_dec_eq(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27_spec__37___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_6);
x_10 = lean_uint64_of_nat(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_array_get_size(x_1);
x_32 = lean_uint64_of_nat(x_29);
x_33 = lean_uint64_of_nat(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27_spec__37___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_uint64_of_nat(x_7);
x_11 = lean_uint64_of_nat(x_8);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_array_uset(x_6, x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14___redArg(x_29);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_box(0);
x_38 = lean_array_uset(x_6, x_23, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15___redArg(x_2, x_3, x_24);
x_40 = lean_array_uset(x_38, x_23, x_39);
lean_ctor_set(x_1, 1, x_40);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_array_get_size(x_42);
x_46 = lean_uint64_of_nat(x_43);
x_47 = lean_uint64_of_nat(x_44);
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_45);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_42, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_41, x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_array_uset(x_42, x_59, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_63, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14___redArg(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_42, x_59, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15___redArg(x_2, x_3, x_60);
x_78 = lean_array_uset(x_76, x_59, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_11 = x_5;
} else {
 lean_dec_ref(x_5);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_box(0);
x_30 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_14);
x_35 = l_Lean_Syntax_getPos_x3f(x_30, x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_unsigned_to_nat(0u);
x_31 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_31 = x_37;
goto block_34;
}
block_29:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0;
x_22 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(x_10, x_20, x_21);
x_23 = lean_array_push(x_22, x_15);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(x_10, x_20, x_23);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_11;
}
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
goto _start;
}
block_34:
{
lean_object* x_32; 
x_32 = l_Lean_Syntax_getTailPos_x3f(x_30, x_1);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_inc(x_31);
x_18 = x_31;
x_19 = x_31;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_31;
x_19 = x_33;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg(x_8, x_2, x_9, x_10, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_6, 5);
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_box(0);
x_31 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_15);
x_36 = l_Lean_Syntax_getPos_x3f(x_31, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_unsigned_to_nat(0u);
x_32 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_32 = x_38;
goto block_35;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0;
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(x_11, x_21, x_22);
x_24 = lean_array_push(x_23, x_16);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(x_11, x_21, x_24);
if (lean_is_scalar(x_12)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_12;
}
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg(x_1, x_2, x_3, x_28, x_26, x_6);
return x_29;
}
block_35:
{
lean_object* x_33; 
x_33 = l_Lean_Syntax_getTailPos_x3f(x_31, x_1);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_inc(x_32);
x_19 = x_32;
x_20 = x_32;
goto block_30;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_19 = x_32;
x_20 = x_34;
goto block_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_11 = x_5;
} else {
 lean_dec_ref(x_5);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_box(0);
x_30 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_14);
x_35 = l_Lean_Syntax_getPos_x3f(x_30, x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_unsigned_to_nat(0u);
x_31 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_31 = x_37;
goto block_34;
}
block_29:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0;
x_22 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(x_10, x_20, x_21);
x_23 = lean_array_push(x_22, x_15);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(x_10, x_20, x_23);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_11;
}
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
goto _start;
}
block_34:
{
lean_object* x_32; 
x_32 = l_Lean_Syntax_getTailPos_x3f(x_30, x_1);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_inc(x_31);
x_18 = x_31;
x_19 = x_31;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_31;
x_19 = x_33;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg(x_8, x_2, x_9, x_10, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_6, 5);
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_box(0);
x_31 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_15);
x_36 = l_Lean_Syntax_getPos_x3f(x_31, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_unsigned_to_nat(0u);
x_32 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_32 = x_38;
goto block_35;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0;
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(x_11, x_21, x_22);
x_24 = lean_array_push(x_23, x_16);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(x_11, x_21, x_24);
if (lean_is_scalar(x_12)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_12;
}
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg(x_1, x_2, x_3, x_28, x_26, x_6);
return x_29;
}
block_35:
{
lean_object* x_33; 
x_33 = l_Lean_Syntax_getTailPos_x3f(x_31, x_1);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_inc(x_32);
x_19 = x_32;
x_20 = x_32;
goto block_30;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_19 = x_32;
x_20 = x_34;
goto block_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_array_size(x_9);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31(x_1, x_2, x_9, x_12, x_13, x_11, x_5, x_6);
lean_dec_ref(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_18);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_16);
lean_free_object(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_21);
lean_dec(x_20);
lean_free_object(x_3);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_free_object(x_3);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_size(x_29);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31(x_1, x_2, x_29, x_32, x_33, x_31, x_5, x_6);
lean_dec_ref(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_37);
lean_dec(x_35);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec_ref(x_37);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
x_50 = lean_array_size(x_47);
x_51 = 0;
x_52 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32(x_1, x_47, x_50, x_51, x_49, x_5, x_6);
lean_dec_ref(x_47);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_54, 0);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_ctor_set(x_3, 0, x_56);
lean_ctor_set(x_52, 0, x_3);
return x_52;
}
else
{
lean_object* x_57; 
lean_inc_ref(x_55);
lean_dec(x_54);
lean_free_object(x_3);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec_ref(x_55);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_58, 0);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_ctor_set(x_3, 0, x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_3);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_inc_ref(x_59);
lean_dec(x_58);
lean_free_object(x_3);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec_ref(x_59);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_free_object(x_3);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
return x_52;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
x_70 = lean_array_size(x_67);
x_71 = 0;
x_72 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32(x_1, x_67, x_70, x_71, x_69, x_5, x_6);
lean_dec_ref(x_67);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_73, 0);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_inc_ref(x_75);
lean_dec(x_73);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec_ref(x_75);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_array_uget(x_3, x_5);
lean_inc(x_13);
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17(x_1, x_2, x_15, x_13, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
lean_free_object(x_16);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_13);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_box(0);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_29);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_13);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_array_uget(x_3, x_5);
lean_inc(x_36);
x_38 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17(x_1, x_2, x_37, x_36, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_40);
lean_dec(x_36);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec_ref(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_36);
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_51 = x_38;
} else {
 lean_dec_ref(x_38);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__31(x_10, x_2, x_3, x_11, x_12, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_9 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17(x_1, x_3, x_7, x_3, x_4, x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_free_object(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_array_size(x_8);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18(x_1, x_8, x_16, x_17, x_15, x_4, x_5);
lean_dec_ref(x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_21);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_25);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 0);
lean_inc(x_33);
lean_dec(x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_size(x_8);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18(x_1, x_8, x_39, x_40, x_38, x_4, x_5);
lean_dec_ref(x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_44);
lean_dec(x_42);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec_ref(x_44);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_8);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
lean_dec(x_9);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; 
lean_free_object(x_5);
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__7(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTraceAsMessages___at___00main_spec__6___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_trace_profiler_output;
x_6 = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__7(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_PersistentArray_isEmpty___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1;
x_13 = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11(x_10, x_9, x_12, x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_36; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_44);
lean_dec(x_14);
x_45 = lean_mk_empty_array_with_capacity(x_43);
lean_dec(x_43);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_11, x_46);
if (x_47 == 0)
{
lean_dec_ref(x_44);
x_36 = x_45;
goto block_42;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
if (x_47 == 0)
{
lean_dec_ref(x_44);
x_36 = x_45;
goto block_42;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_46);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(x_44, x_49, x_50, x_45);
lean_dec_ref(x_44);
x_36 = x_51;
goto block_42;
}
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(x_44, x_52, x_53, x_45);
lean_dec_ref(x_44);
x_36 = x_54;
goto block_42;
}
}
block_23:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_15);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12(x_10, x_15, x_17, x_18, x_16, x_1, x_2);
lean_dec_ref(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
else
{
return x_19;
}
}
block_29:
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(x_25, x_24, x_27);
lean_dec(x_27);
x_15 = x_28;
goto block_23;
}
block_35:
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_33, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
lean_inc(x_33);
x_24 = x_33;
x_25 = x_30;
x_26 = x_32;
x_27 = x_33;
goto block_29;
}
else
{
x_24 = x_33;
x_25 = x_30;
x_26 = x_32;
x_27 = x_31;
goto block_29;
}
}
block_42:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_eq(x_37, x_11);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_37, x_39);
x_41 = lean_nat_dec_le(x_11, x_40);
if (x_41 == 0)
{
lean_inc(x_40);
x_30 = x_36;
x_31 = x_40;
x_32 = x_37;
x_33 = x_40;
goto block_35;
}
else
{
x_30 = x_36;
x_31 = x_40;
x_32 = x_37;
x_33 = x_11;
goto block_35;
}
}
else
{
x_15 = x_36;
goto block_23;
}
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_9);
lean_dec_ref(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_7, 0, x_58);
return x_7;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
lean_dec(x_7);
x_60 = l_Lean_PersistentArray_isEmpty___redArg(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1;
x_63 = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11(x_60, x_59, x_62, x_1, x_2);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_85; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_92 = lean_ctor_get(x_64, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_93);
lean_dec(x_64);
x_94 = lean_mk_empty_array_with_capacity(x_92);
lean_dec(x_92);
x_95 = lean_array_get_size(x_93);
x_96 = lean_nat_dec_lt(x_61, x_95);
if (x_96 == 0)
{
lean_dec_ref(x_93);
x_85 = x_94;
goto block_91;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_95, x_95);
if (x_97 == 0)
{
if (x_96 == 0)
{
lean_dec_ref(x_93);
x_85 = x_94;
goto block_91;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; 
x_98 = 0;
x_99 = lean_usize_of_nat(x_95);
x_100 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(x_93, x_98, x_99, x_94);
lean_dec_ref(x_93);
x_85 = x_100;
goto block_91;
}
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; 
x_101 = 0;
x_102 = lean_usize_of_nat(x_95);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__15(x_93, x_101, x_102, x_94);
lean_dec_ref(x_93);
x_85 = x_103;
goto block_91;
}
}
block_72:
{
lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_66 = lean_box(0);
x_67 = lean_array_size(x_65);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12(x_60, x_65, x_67, x_68, x_66, x_1, x_2);
lean_dec_ref(x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_70 = x_69;
} else {
 lean_dec_ref(x_69);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_66);
return x_71;
}
else
{
return x_69;
}
}
block_78:
{
lean_object* x_77; 
lean_dec(x_75);
x_77 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(x_74, x_73, x_76);
lean_dec(x_76);
x_65 = x_77;
goto block_72;
}
block_84:
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_82, x_80);
if (x_83 == 0)
{
lean_dec(x_80);
lean_inc(x_82);
x_73 = x_82;
x_74 = x_79;
x_75 = x_81;
x_76 = x_82;
goto block_78;
}
else
{
x_73 = x_82;
x_74 = x_79;
x_75 = x_81;
x_76 = x_80;
goto block_78;
}
}
block_91:
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_eq(x_86, x_61);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_86, x_88);
x_90 = lean_nat_dec_le(x_61, x_89);
if (x_90 == 0)
{
lean_inc(x_89);
x_79 = x_85;
x_80 = x_89;
x_81 = x_86;
x_82 = x_89;
goto block_84;
}
else
{
x_79 = x_85;
x_80 = x_89;
x_81 = x_86;
x_82 = x_61;
goto block_84;
}
}
else
{
x_65 = x_85;
goto block_72;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_63, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_105 = x_63;
} else {
 lean_dec_ref(x_63);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_59);
lean_dec_ref(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_6);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_6, 0);
lean_dec(x_110);
x_111 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_111);
return x_6;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_6);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addTraceAsMessages___at___00main_spec__6(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_inc_ref(x_1);
x_14 = l_Lean_isExtern(x_1, x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = l_Lean_Compiler_LCNF_impureSigExt;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = lean_array_uget(x_1, x_2);
x_11 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_6, x_4, x_10, x_8, x_9);
lean_dec(x_8);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_array_uget(x_2, x_3);
x_15 = l_Lean_IR_Decl_name(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_28);
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec(x_27);
lean_inc_ref(x_15);
x_16 = x_15;
goto block_26;
}
else
{
x_16 = x_27;
goto block_26;
}
}
else
{
lean_inc(x_15);
x_16 = x_15;
goto block_26;
}
block_26:
{
uint8_t x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_isExtern(x_1, x_16);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
x_6 = x_5;
goto block_10;
}
else
{
uint8_t x_18; 
lean_inc(x_13);
lean_inc(x_12);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
lean_inc(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_12);
x_22 = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(x_13, x_15, x_14);
lean_ctor_set(x_5, 1, x_22);
lean_ctor_set(x_5, 0, x_21);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_inc(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_12);
x_24 = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(x_13, x_15, x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_6 = x_25;
goto block_10;
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__2));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_107; uint8_t x_123; 
x_98 = 2;
x_123 = l_Lean_instBEqMessageSeverity_beq(x_3, x_98);
if (x_123 == 0)
{
x_107 = x_123;
goto block_122;
}
else
{
uint8_t x_124; 
lean_inc_ref(x_2);
x_124 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_107 = x_124;
goto block_122;
}
block_47:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_st_ref_take(x_16);
x_19 = lean_ctor_get(x_15, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 7);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_18, 6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
x_25 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_14);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 2, x_4);
x_26 = l_Lean_MessageLog_add(x_25, x_22);
lean_ctor_set(x_18, 6, x_26);
x_27 = lean_st_ref_set(x_16, x_18);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
x_37 = lean_ctor_get(x_18, 7);
x_38 = lean_ctor_get(x_18, 8);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_20);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set(x_41, 2, x_13);
lean_ctor_set(x_41, 3, x_11);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*5, x_14);
lean_ctor_set_uint8(x_41, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_41, sizeof(void*)*5 + 2, x_4);
x_42 = l_Lean_MessageLog_add(x_41, x_36);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_35);
lean_ctor_set(x_43, 6, x_42);
lean_ctor_set(x_43, 7, x_37);
lean_ctor_set(x_43, 8, x_38);
x_44 = lean_st_ref_set(x_16, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
block_74:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_57 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(x_56, x_5, x_6);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_53);
x_60 = l_Lean_FileMap_toPosition(x_53, x_52);
lean_dec(x_52);
x_61 = l_Lean_FileMap_toPosition(x_53, x_55);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1));
if (x_49 == 0)
{
lean_free_object(x_57);
lean_dec_ref(x_48);
x_8 = x_60;
x_9 = x_50;
x_10 = x_59;
x_11 = x_63;
x_12 = x_51;
x_13 = x_62;
x_14 = x_54;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_64; 
lean_inc(x_59);
x_64 = l_Lean_MessageData_hasTag(x_48, x_59);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
x_65 = lean_box(0);
lean_ctor_set(x_57, 0, x_65);
return x_57;
}
else
{
lean_free_object(x_57);
x_8 = x_60;
x_9 = x_50;
x_10 = x_59;
x_11 = x_63;
x_12 = x_51;
x_13 = x_62;
x_14 = x_54;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
lean_inc_ref(x_53);
x_67 = l_Lean_FileMap_toPosition(x_53, x_52);
lean_dec(x_52);
x_68 = l_Lean_FileMap_toPosition(x_53, x_55);
lean_dec(x_55);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__1));
if (x_49 == 0)
{
lean_dec_ref(x_48);
x_8 = x_67;
x_9 = x_50;
x_10 = x_66;
x_11 = x_70;
x_12 = x_51;
x_13 = x_69;
x_14 = x_54;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_71; 
lean_inc(x_66);
x_71 = l_Lean_MessageData_hasTag(x_48, x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_69);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
x_8 = x_67;
x_9 = x_50;
x_10 = x_66;
x_11 = x_70;
x_12 = x_51;
x_13 = x_69;
x_14 = x_54;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
}
}
}
block_85:
{
lean_object* x_83; 
x_83 = l_Lean_Syntax_getTailPos_x3f(x_78, x_81);
lean_dec(x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_inc(x_82);
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_79;
x_52 = x_82;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
goto block_74;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_48 = x_75;
x_49 = x_76;
x_50 = x_77;
x_51 = x_79;
x_52 = x_82;
x_53 = x_80;
x_54 = x_81;
x_55 = x_84;
goto block_74;
}
}
block_97:
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_replaceRef(x_1, x_89);
lean_dec(x_89);
x_94 = l_Lean_Syntax_getPos_x3f(x_93, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_unsigned_to_nat(0u);
x_75 = x_86;
x_76 = x_87;
x_77 = x_88;
x_78 = x_93;
x_79 = x_92;
x_80 = x_90;
x_81 = x_91;
x_82 = x_95;
goto block_85;
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec_ref(x_94);
x_75 = x_86;
x_76 = x_87;
x_77 = x_88;
x_78 = x_93;
x_79 = x_92;
x_80 = x_90;
x_81 = x_91;
x_82 = x_96;
goto block_85;
}
}
block_106:
{
if (x_105 == 0)
{
x_86 = x_102;
x_87 = x_99;
x_88 = x_100;
x_89 = x_101;
x_90 = x_103;
x_91 = x_104;
x_92 = x_3;
goto block_97;
}
else
{
x_86 = x_102;
x_87 = x_99;
x_88 = x_100;
x_89 = x_101;
x_90 = x_103;
x_91 = x_104;
x_92 = x_98;
goto block_97;
}
}
block_122:
{
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_108 = lean_ctor_get(x_5, 0);
x_109 = lean_ctor_get(x_5, 1);
x_110 = lean_ctor_get(x_5, 2);
x_111 = lean_ctor_get(x_5, 5);
x_112 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_113 = lean_box(x_107);
x_114 = lean_box(x_112);
x_115 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___lam__0___boxed), 3, 2);
lean_closure_set(x_115, 0, x_113);
lean_closure_set(x_115, 1, x_114);
x_116 = 1;
x_117 = l_Lean_instBEqMessageSeverity_beq(x_3, x_116);
if (x_117 == 0)
{
lean_inc_ref(x_109);
lean_inc(x_111);
lean_inc_ref(x_108);
x_99 = x_112;
x_100 = x_108;
x_101 = x_111;
x_102 = x_115;
x_103 = x_109;
x_104 = x_107;
x_105 = x_117;
goto block_106;
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = l_Lean_warningAsError;
x_119 = l_Lean_Option_get___at___00main_spec__4(x_110, x_118);
lean_inc_ref(x_109);
lean_inc(x_111);
lean_inc_ref(x_108);
x_99 = x_112;
x_100 = x_108;
x_101 = x_111;
x_102 = x_115;
x_103 = x_109;
x_104 = x_107;
x_105 = x_119;
goto block_106;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26_spec__36(x_7, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 2;
x_6 = 0;
x_7 = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__26(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logError___at___00main_spec__13(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_8) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(x_1, x_5);
x_10 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 4);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_17, x_11);
x_19 = lean_nat_dec_lt(x_18, x_12);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_20 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_21 = lean_nat_add(x_20, x_12);
lean_dec(x_20);
if (lean_is_scalar(x_7)) {
 x_22 = lean_alloc_ctor(0, 5, 0);
} else {
 x_22 = x_7;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_23 = x_6;
} else {
 lean_dec_ref(x_6);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
x_26 = lean_ctor_get(x_15, 2);
x_27 = lean_ctor_get(x_15, 3);
x_28 = lean_ctor_get(x_15, 4);
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_mul(x_30, x_29);
x_32 = lean_nat_dec_lt(x_24, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_43; 
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 x_33 = x_15;
} else {
 lean_dec_ref(x_15);
 x_33 = lean_box(0);
}
x_34 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_35 = lean_nat_add(x_34, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
x_43 = x_50;
goto block_49;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_43 = x_51;
goto block_49;
}
block_42:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_nat_add(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 5, 0);
} else {
 x_40 = x_33;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_13);
lean_ctor_set(x_40, 2, x_14);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_16);
if (lean_is_scalar(x_23)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_23;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_40);
return x_41;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_nat_add(x_34, x_43);
lean_dec(x_43);
lean_dec(x_34);
if (lean_is_scalar(x_7)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_7;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_ctor_set(x_45, 3, x_9);
lean_ctor_set(x_45, 4, x_27);
x_46 = lean_nat_add(x_10, x_29);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
x_36 = x_46;
x_37 = x_45;
x_38 = x_47;
goto block_42;
}
else
{
lean_object* x_48; 
x_48 = lean_unsigned_to_nat(0u);
x_36 = x_46;
x_37 = x_45;
x_38 = x_48;
goto block_42;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_7);
x_52 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_53 = lean_nat_add(x_52, x_12);
lean_dec(x_12);
x_54 = lean_nat_add(x_52, x_24);
lean_dec(x_52);
lean_inc_ref(x_9);
if (lean_is_scalar(x_23)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_23;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set(x_55, 3, x_9);
lean_ctor_set(x_55, 4, x_15);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_9, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_9, 0);
lean_dec(x_61);
lean_ctor_set(x_9, 4, x_16);
lean_ctor_set(x_9, 3, x_55);
lean_ctor_set(x_9, 2, x_14);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_53);
return x_9;
}
else
{
lean_object* x_62; 
lean_dec(x_9);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_13);
lean_ctor_set(x_62, 2, x_14);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_16);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_9, 0);
lean_inc(x_63);
x_64 = lean_nat_add(x_10, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_7)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_7;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set(x_65, 3, x_9);
lean_ctor_set(x_65, 4, x_6);
return x_65;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_6, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_6, 4);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_6);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_6, 0);
x_70 = lean_ctor_get(x_6, 1);
x_71 = lean_ctor_get(x_6, 2);
x_72 = lean_ctor_get(x_6, 4);
lean_dec(x_72);
x_73 = lean_ctor_get(x_6, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_nat_add(x_10, x_69);
lean_dec(x_69);
x_76 = lean_nat_add(x_10, x_74);
lean_ctor_set(x_6, 4, x_66);
lean_ctor_set(x_6, 3, x_9);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_76);
if (lean_is_scalar(x_7)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_7;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_6);
lean_ctor_set(x_77, 4, x_67);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_6, 0);
x_79 = lean_ctor_get(x_6, 1);
x_80 = lean_ctor_get(x_6, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_6);
x_81 = lean_ctor_get(x_66, 0);
x_82 = lean_nat_add(x_10, x_78);
lean_dec(x_78);
x_83 = lean_nat_add(x_10, x_81);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set(x_84, 3, x_9);
lean_ctor_set(x_84, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_7;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_67);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_6, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_6, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_6, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_66);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_66, 1);
x_92 = lean_ctor_get(x_66, 2);
x_93 = lean_ctor_get(x_66, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_66, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_66, 0);
lean_dec(x_95);
x_96 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_66, 4, x_67);
lean_ctor_set(x_66, 3, x_67);
lean_ctor_set(x_66, 2, x_4);
lean_ctor_set(x_66, 1, x_3);
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_6, 3, x_67);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_7;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_92);
lean_ctor_set(x_97, 3, x_66);
lean_ctor_set(x_97, 4, x_6);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_66, 1);
x_99 = lean_ctor_get(x_66, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_66);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_3);
lean_ctor_set(x_101, 2, x_4);
lean_ctor_set(x_101, 3, x_67);
lean_ctor_set(x_101, 4, x_67);
lean_ctor_set(x_6, 3, x_67);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_7;
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_6);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_6);
x_105 = lean_ctor_get(x_66, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_66, 2);
lean_inc(x_106);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_107 = x_66;
} else {
 lean_dec_ref(x_66);
 x_107 = lean_box(0);
}
x_108 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_10);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 2, x_4);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_10);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_104);
lean_ctor_set(x_110, 3, x_67);
lean_ctor_set(x_110, 4, x_67);
if (lean_is_scalar(x_7)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_7;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set(x_111, 2, x_106);
lean_ctor_set(x_111, 3, x_109);
lean_ctor_set(x_111, 4, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_6, 4);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_6);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_6, 1);
x_115 = lean_ctor_get(x_6, 2);
x_116 = lean_ctor_get(x_6, 4);
lean_dec(x_116);
x_117 = lean_ctor_get(x_6, 3);
lean_dec(x_117);
x_118 = lean_ctor_get(x_6, 0);
lean_dec(x_118);
x_119 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_66);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_120 = lean_alloc_ctor(0, 5, 0);
} else {
 x_120 = x_7;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_6);
lean_ctor_set(x_120, 4, x_112);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_6, 1);
x_122 = lean_ctor_get(x_6, 2);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_6);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_10);
lean_ctor_set(x_124, 1, x_3);
lean_ctor_set(x_124, 2, x_4);
lean_ctor_set(x_124, 3, x_66);
lean_ctor_set(x_124, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_125 = lean_alloc_ctor(0, 5, 0);
} else {
 x_125 = x_7;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_122);
lean_ctor_set(x_125, 3, x_124);
lean_ctor_set(x_125, 4, x_112);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_6);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_6, 4);
lean_dec(x_127);
x_128 = lean_ctor_get(x_6, 3);
lean_dec(x_128);
lean_ctor_set(x_6, 3, x_112);
x_129 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_7;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_3);
lean_ctor_set(x_130, 2, x_4);
lean_ctor_set(x_130, 3, x_112);
lean_ctor_set(x_130, 4, x_6);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_6, 0);
x_132 = lean_ctor_get(x_6, 1);
x_133 = lean_ctor_get(x_6, 2);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_6);
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_112);
lean_ctor_set(x_134, 4, x_112);
x_135 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_7;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_4);
lean_ctor_set(x_136, 3, x_112);
lean_ctor_set(x_136, 4, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; 
if (lean_is_scalar(x_7)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_7;
}
lean_ctor_set(x_137, 0, x_10);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_6);
lean_ctor_set(x_137, 4, x_6);
return x_137;
}
}
}
case 1:
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
x_140 = lean_ctor_get(x_5, 2);
x_141 = lean_ctor_get(x_5, 3);
x_142 = lean_ctor_get(x_5, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_6, 0);
x_144 = lean_ctor_get(x_6, 1);
x_145 = lean_ctor_get(x_6, 2);
x_146 = lean_ctor_get(x_6, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_6, 4);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_nat_dec_lt(x_138, x_143);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_150 = x_5;
} else {
 lean_dec_ref(x_5);
 x_150 = lean_box(0);
}
x_151 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_139, x_140, x_141, x_142);
x_152 = lean_ctor_get(x_151, 2);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec_ref(x_151);
x_155 = lean_ctor_get(x_152, 0);
x_156 = lean_unsigned_to_nat(3u);
x_157 = lean_nat_mul(x_156, x_155);
x_158 = lean_nat_dec_lt(x_157, x_143);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_146);
x_159 = lean_nat_add(x_148, x_155);
x_160 = lean_nat_add(x_159, x_143);
lean_dec(x_159);
if (lean_is_scalar(x_150)) {
 x_161 = lean_alloc_ctor(0, 5, 0);
} else {
 x_161 = x_150;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_154);
lean_ctor_set(x_161, 3, x_152);
lean_ctor_set(x_161, 4, x_6);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_162 = x_6;
} else {
 lean_dec_ref(x_6);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_146, 0);
x_164 = lean_ctor_get(x_146, 1);
x_165 = lean_ctor_get(x_146, 2);
x_166 = lean_ctor_get(x_146, 3);
x_167 = lean_ctor_get(x_146, 4);
x_168 = lean_ctor_get(x_147, 0);
x_169 = lean_unsigned_to_nat(2u);
x_170 = lean_nat_mul(x_169, x_168);
x_171 = lean_nat_dec_lt(x_163, x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_182; 
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_172 = x_146;
} else {
 lean_dec_ref(x_146);
 x_172 = lean_box(0);
}
x_173 = lean_nat_add(x_148, x_155);
x_174 = lean_nat_add(x_173, x_143);
lean_dec(x_143);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_166, 0);
lean_inc(x_189);
x_182 = x_189;
goto block_188;
}
else
{
lean_object* x_190; 
x_190 = lean_unsigned_to_nat(0u);
x_182 = x_190;
goto block_188;
}
block_181:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_nat_add(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
if (lean_is_scalar(x_172)) {
 x_179 = lean_alloc_ctor(0, 5, 0);
} else {
 x_179 = x_172;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_144);
lean_ctor_set(x_179, 2, x_145);
lean_ctor_set(x_179, 3, x_167);
lean_ctor_set(x_179, 4, x_147);
if (lean_is_scalar(x_162)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_162;
}
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_164);
lean_ctor_set(x_180, 2, x_165);
lean_ctor_set(x_180, 3, x_175);
lean_ctor_set(x_180, 4, x_179);
return x_180;
}
block_188:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_nat_add(x_173, x_182);
lean_dec(x_182);
lean_dec(x_173);
if (lean_is_scalar(x_150)) {
 x_184 = lean_alloc_ctor(0, 5, 0);
} else {
 x_184 = x_150;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_153);
lean_ctor_set(x_184, 2, x_154);
lean_ctor_set(x_184, 3, x_152);
lean_ctor_set(x_184, 4, x_166);
x_185 = lean_nat_add(x_148, x_168);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
x_175 = x_184;
x_176 = x_185;
x_177 = x_186;
goto block_181;
}
else
{
lean_object* x_187; 
x_187 = lean_unsigned_to_nat(0u);
x_175 = x_184;
x_176 = x_185;
x_177 = x_187;
goto block_181;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_nat_add(x_148, x_155);
x_192 = lean_nat_add(x_191, x_143);
lean_dec(x_143);
x_193 = lean_nat_add(x_191, x_163);
lean_dec(x_191);
if (lean_is_scalar(x_162)) {
 x_194 = lean_alloc_ctor(0, 5, 0);
} else {
 x_194 = x_162;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_153);
lean_ctor_set(x_194, 2, x_154);
lean_ctor_set(x_194, 3, x_152);
lean_ctor_set(x_194, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_150;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_144);
lean_ctor_set(x_195, 2, x_145);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 4, x_147);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
x_196 = !lean_is_exclusive(x_6);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_6, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_6, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_6, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_6, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_6, 0);
lean_dec(x_201);
if (lean_obj_tag(x_146) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_151, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_151, 1);
lean_inc(x_203);
lean_dec_ref(x_151);
x_204 = lean_ctor_get(x_146, 0);
x_205 = lean_nat_add(x_148, x_143);
lean_dec(x_143);
x_206 = lean_nat_add(x_148, x_204);
lean_ctor_set(x_6, 4, x_146);
lean_ctor_set(x_6, 3, x_152);
lean_ctor_set(x_6, 2, x_203);
lean_ctor_set(x_6, 1, x_202);
lean_ctor_set(x_6, 0, x_206);
if (lean_is_scalar(x_150)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_150;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_144);
lean_ctor_set(x_207, 2, x_145);
lean_ctor_set(x_207, 3, x_6);
lean_ctor_set(x_207, 4, x_147);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_143);
x_208 = lean_ctor_get(x_151, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_151, 1);
lean_inc(x_209);
lean_dec_ref(x_151);
x_210 = !lean_is_exclusive(x_146);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_146, 1);
x_212 = lean_ctor_get(x_146, 2);
x_213 = lean_ctor_get(x_146, 4);
lean_dec(x_213);
x_214 = lean_ctor_get(x_146, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_146, 0);
lean_dec(x_215);
x_216 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_146, 4, x_147);
lean_ctor_set(x_146, 3, x_147);
lean_ctor_set(x_146, 2, x_209);
lean_ctor_set(x_146, 1, x_208);
lean_ctor_set(x_146, 0, x_148);
lean_ctor_set(x_6, 3, x_147);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_217 = lean_alloc_ctor(0, 5, 0);
} else {
 x_217 = x_150;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_211);
lean_ctor_set(x_217, 2, x_212);
lean_ctor_set(x_217, 3, x_146);
lean_ctor_set(x_217, 4, x_6);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_146, 1);
x_219 = lean_ctor_get(x_146, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_146);
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_148);
lean_ctor_set(x_221, 1, x_208);
lean_ctor_set(x_221, 2, x_209);
lean_ctor_set(x_221, 3, x_147);
lean_ctor_set(x_221, 4, x_147);
lean_ctor_set(x_6, 3, x_147);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_222 = lean_alloc_ctor(0, 5, 0);
} else {
 x_222 = x_150;
}
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_219);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_6);
return x_222;
}
}
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_143);
x_223 = lean_ctor_get(x_151, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_151, 1);
lean_inc(x_224);
lean_dec_ref(x_151);
x_225 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_146);
lean_ctor_set(x_6, 2, x_224);
lean_ctor_set(x_6, 1, x_223);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_226 = lean_alloc_ctor(0, 5, 0);
} else {
 x_226 = x_150;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_144);
lean_ctor_set(x_226, 2, x_145);
lean_ctor_set(x_226, 3, x_6);
lean_ctor_set(x_226, 4, x_147);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_151, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_151, 1);
lean_inc(x_228);
lean_dec_ref(x_151);
lean_ctor_set(x_6, 3, x_147);
x_229 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_150)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_150;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_147);
lean_ctor_set(x_230, 4, x_6);
return x_230;
}
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_146) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_151, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_151, 1);
lean_inc(x_232);
lean_dec_ref(x_151);
x_233 = lean_ctor_get(x_146, 0);
x_234 = lean_nat_add(x_148, x_143);
lean_dec(x_143);
x_235 = lean_nat_add(x_148, x_233);
x_236 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_231);
lean_ctor_set(x_236, 2, x_232);
lean_ctor_set(x_236, 3, x_152);
lean_ctor_set(x_236, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_237 = lean_alloc_ctor(0, 5, 0);
} else {
 x_237 = x_150;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_144);
lean_ctor_set(x_237, 2, x_145);
lean_ctor_set(x_237, 3, x_236);
lean_ctor_set(x_237, 4, x_147);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_143);
x_238 = lean_ctor_get(x_151, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_151, 1);
lean_inc(x_239);
lean_dec_ref(x_151);
x_240 = lean_ctor_get(x_146, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_146, 2);
lean_inc(x_241);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_242 = x_146;
} else {
 lean_dec_ref(x_146);
 x_242 = lean_box(0);
}
x_243 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_148);
lean_ctor_set(x_244, 1, x_238);
lean_ctor_set(x_244, 2, x_239);
lean_ctor_set(x_244, 3, x_147);
lean_ctor_set(x_244, 4, x_147);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_148);
lean_ctor_set(x_245, 1, x_144);
lean_ctor_set(x_245, 2, x_145);
lean_ctor_set(x_245, 3, x_147);
lean_ctor_set(x_245, 4, x_147);
if (lean_is_scalar(x_150)) {
 x_246 = lean_alloc_ctor(0, 5, 0);
} else {
 x_246 = x_150;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set(x_246, 4, x_245);
return x_246;
}
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_143);
x_247 = lean_ctor_get(x_151, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_151, 1);
lean_inc(x_248);
lean_dec_ref(x_151);
x_249 = lean_unsigned_to_nat(3u);
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_148);
lean_ctor_set(x_250, 1, x_247);
lean_ctor_set(x_250, 2, x_248);
lean_ctor_set(x_250, 3, x_146);
lean_ctor_set(x_250, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_150;
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_144);
lean_ctor_set(x_251, 2, x_145);
lean_ctor_set(x_251, 3, x_250);
lean_ctor_set(x_251, 4, x_147);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_151, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_151, 1);
lean_inc(x_253);
lean_dec_ref(x_151);
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_143);
lean_ctor_set(x_254, 1, x_144);
lean_ctor_set(x_254, 2, x_145);
lean_ctor_set(x_254, 3, x_147);
lean_ctor_set(x_254, 4, x_147);
x_255 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_150)) {
 x_256 = lean_alloc_ctor(0, 5, 0);
} else {
 x_256 = x_150;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_147);
lean_ctor_set(x_256, 4, x_254);
return x_256;
}
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_257 = x_6;
} else {
 lean_dec_ref(x_6);
 x_257 = lean_box(0);
}
x_258 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_144, x_145, x_146, x_147);
x_259 = lean_ctor_get(x_258, 2);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec_ref(x_258);
x_262 = lean_ctor_get(x_259, 0);
x_263 = lean_unsigned_to_nat(3u);
x_264 = lean_nat_mul(x_263, x_262);
x_265 = lean_nat_dec_lt(x_264, x_138);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_142);
x_266 = lean_nat_add(x_148, x_138);
x_267 = lean_nat_add(x_266, x_262);
lean_dec(x_266);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(0, 5, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_260);
lean_ctor_set(x_268, 2, x_261);
lean_ctor_set(x_268, 3, x_5);
lean_ctor_set(x_268, 4, x_259);
return x_268;
}
else
{
uint8_t x_269; 
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
x_269 = !lean_is_exclusive(x_5);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_270 = lean_ctor_get(x_5, 4);
lean_dec(x_270);
x_271 = lean_ctor_get(x_5, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_5, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_5, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_5, 0);
lean_dec(x_274);
x_275 = lean_ctor_get(x_141, 0);
x_276 = lean_ctor_get(x_142, 0);
x_277 = lean_ctor_get(x_142, 1);
x_278 = lean_ctor_get(x_142, 2);
x_279 = lean_ctor_get(x_142, 3);
x_280 = lean_ctor_get(x_142, 4);
x_281 = lean_unsigned_to_nat(2u);
x_282 = lean_nat_mul(x_281, x_275);
x_283 = lean_nat_dec_lt(x_276, x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_300; lean_object* x_301; 
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_free_object(x_5);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_284 = x_142;
} else {
 lean_dec_ref(x_142);
 x_284 = lean_box(0);
}
x_285 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_286 = lean_nat_add(x_285, x_262);
lean_dec(x_285);
x_300 = lean_nat_add(x_148, x_275);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_279, 0);
lean_inc(x_308);
x_301 = x_308;
goto block_307;
}
else
{
lean_object* x_309; 
x_309 = lean_unsigned_to_nat(0u);
x_301 = x_309;
goto block_307;
}
block_299:
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_nat_add(x_287, x_289);
lean_dec(x_289);
lean_dec(x_287);
lean_inc_ref(x_259);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 5, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_260);
lean_ctor_set(x_291, 2, x_261);
lean_ctor_set(x_291, 3, x_280);
lean_ctor_set(x_291, 4, x_259);
x_292 = !lean_is_exclusive(x_259);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_259, 4);
lean_dec(x_293);
x_294 = lean_ctor_get(x_259, 3);
lean_dec(x_294);
x_295 = lean_ctor_get(x_259, 2);
lean_dec(x_295);
x_296 = lean_ctor_get(x_259, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_259, 0);
lean_dec(x_297);
lean_ctor_set(x_259, 4, x_291);
lean_ctor_set(x_259, 3, x_288);
lean_ctor_set(x_259, 2, x_278);
lean_ctor_set(x_259, 1, x_277);
lean_ctor_set(x_259, 0, x_286);
return x_259;
}
else
{
lean_object* x_298; 
lean_dec(x_259);
x_298 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_298, 0, x_286);
lean_ctor_set(x_298, 1, x_277);
lean_ctor_set(x_298, 2, x_278);
lean_ctor_set(x_298, 3, x_288);
lean_ctor_set(x_298, 4, x_291);
return x_298;
}
}
block_307:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_nat_add(x_300, x_301);
lean_dec(x_301);
lean_dec(x_300);
if (lean_is_scalar(x_257)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_257;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_139);
lean_ctor_set(x_303, 2, x_140);
lean_ctor_set(x_303, 3, x_141);
lean_ctor_set(x_303, 4, x_279);
x_304 = lean_nat_add(x_148, x_262);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_280, 0);
lean_inc(x_305);
x_287 = x_304;
x_288 = x_303;
x_289 = x_305;
goto block_299;
}
else
{
lean_object* x_306; 
x_306 = lean_unsigned_to_nat(0u);
x_287 = x_304;
x_288 = x_303;
x_289 = x_306;
goto block_299;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_310 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_311 = lean_nat_add(x_310, x_262);
lean_dec(x_310);
x_312 = lean_nat_add(x_148, x_262);
x_313 = lean_nat_add(x_312, x_276);
lean_dec(x_312);
if (lean_is_scalar(x_257)) {
 x_314 = lean_alloc_ctor(0, 5, 0);
} else {
 x_314 = x_257;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_260);
lean_ctor_set(x_314, 2, x_261);
lean_ctor_set(x_314, 3, x_142);
lean_ctor_set(x_314, 4, x_259);
lean_ctor_set(x_5, 4, x_314);
lean_ctor_set(x_5, 0, x_311);
return x_5;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_5);
x_315 = lean_ctor_get(x_141, 0);
x_316 = lean_ctor_get(x_142, 0);
x_317 = lean_ctor_get(x_142, 1);
x_318 = lean_ctor_get(x_142, 2);
x_319 = lean_ctor_get(x_142, 3);
x_320 = lean_ctor_get(x_142, 4);
x_321 = lean_unsigned_to_nat(2u);
x_322 = lean_nat_mul(x_321, x_315);
x_323 = lean_nat_dec_lt(x_316, x_322);
lean_dec(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_335; lean_object* x_336; 
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_324 = x_142;
} else {
 lean_dec_ref(x_142);
 x_324 = lean_box(0);
}
x_325 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_326 = lean_nat_add(x_325, x_262);
lean_dec(x_325);
x_335 = lean_nat_add(x_148, x_315);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_319, 0);
lean_inc(x_343);
x_336 = x_343;
goto block_342;
}
else
{
lean_object* x_344; 
x_344 = lean_unsigned_to_nat(0u);
x_336 = x_344;
goto block_342;
}
block_334:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_nat_add(x_327, x_329);
lean_dec(x_329);
lean_dec(x_327);
lean_inc_ref(x_259);
if (lean_is_scalar(x_324)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_324;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_260);
lean_ctor_set(x_331, 2, x_261);
lean_ctor_set(x_331, 3, x_320);
lean_ctor_set(x_331, 4, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 x_332 = x_259;
} else {
 lean_dec_ref(x_259);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 5, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_326);
lean_ctor_set(x_333, 1, x_317);
lean_ctor_set(x_333, 2, x_318);
lean_ctor_set(x_333, 3, x_328);
lean_ctor_set(x_333, 4, x_331);
return x_333;
}
block_342:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_nat_add(x_335, x_336);
lean_dec(x_336);
lean_dec(x_335);
if (lean_is_scalar(x_257)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_257;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_139);
lean_ctor_set(x_338, 2, x_140);
lean_ctor_set(x_338, 3, x_141);
lean_ctor_set(x_338, 4, x_319);
x_339 = lean_nat_add(x_148, x_262);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_320, 0);
lean_inc(x_340);
x_327 = x_339;
x_328 = x_338;
x_329 = x_340;
goto block_334;
}
else
{
lean_object* x_341; 
x_341 = lean_unsigned_to_nat(0u);
x_327 = x_339;
x_328 = x_338;
x_329 = x_341;
goto block_334;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_346 = lean_nat_add(x_345, x_262);
lean_dec(x_345);
x_347 = lean_nat_add(x_148, x_262);
x_348 = lean_nat_add(x_347, x_316);
lean_dec(x_347);
if (lean_is_scalar(x_257)) {
 x_349 = lean_alloc_ctor(0, 5, 0);
} else {
 x_349 = x_257;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_260);
lean_ctor_set(x_349, 2, x_261);
lean_ctor_set(x_349, 3, x_142);
lean_ctor_set(x_349, 4, x_259);
x_350 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_139);
lean_ctor_set(x_350, 2, x_140);
lean_ctor_set(x_350, 3, x_141);
lean_ctor_set(x_350, 4, x_349);
return x_350;
}
}
}
}
else
{
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_351; 
lean_inc_ref(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
x_351 = !lean_is_exclusive(x_5);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_5, 4);
lean_dec(x_352);
x_353 = lean_ctor_get(x_5, 3);
lean_dec(x_353);
x_354 = lean_ctor_get(x_5, 2);
lean_dec(x_354);
x_355 = lean_ctor_get(x_5, 1);
lean_dec(x_355);
x_356 = lean_ctor_get(x_5, 0);
lean_dec(x_356);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_258, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_258, 1);
lean_inc(x_358);
lean_dec_ref(x_258);
x_359 = lean_ctor_get(x_142, 0);
x_360 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_361 = lean_nat_add(x_148, x_359);
if (lean_is_scalar(x_257)) {
 x_362 = lean_alloc_ctor(0, 5, 0);
} else {
 x_362 = x_257;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_357);
lean_ctor_set(x_362, 2, x_358);
lean_ctor_set(x_362, 3, x_142);
lean_ctor_set(x_362, 4, x_259);
lean_ctor_set(x_5, 4, x_362);
lean_ctor_set(x_5, 0, x_360);
return x_5;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_138);
x_363 = lean_ctor_get(x_258, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_258, 1);
lean_inc(x_364);
lean_dec_ref(x_258);
x_365 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_257)) {
 x_366 = lean_alloc_ctor(0, 5, 0);
} else {
 x_366 = x_257;
}
lean_ctor_set(x_366, 0, x_148);
lean_ctor_set(x_366, 1, x_363);
lean_ctor_set(x_366, 2, x_364);
lean_ctor_set(x_366, 3, x_142);
lean_ctor_set(x_366, 4, x_142);
lean_ctor_set(x_5, 4, x_366);
lean_ctor_set(x_5, 0, x_365);
return x_5;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_367 = lean_ctor_get(x_258, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_258, 1);
lean_inc(x_368);
lean_dec_ref(x_258);
x_369 = lean_ctor_get(x_142, 0);
x_370 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_371 = lean_nat_add(x_148, x_369);
if (lean_is_scalar(x_257)) {
 x_372 = lean_alloc_ctor(0, 5, 0);
} else {
 x_372 = x_257;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_367);
lean_ctor_set(x_372, 2, x_368);
lean_ctor_set(x_372, 3, x_142);
lean_ctor_set(x_372, 4, x_259);
x_373 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_139);
lean_ctor_set(x_373, 2, x_140);
lean_ctor_set(x_373, 3, x_141);
lean_ctor_set(x_373, 4, x_372);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_138);
x_374 = lean_ctor_get(x_258, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_258, 1);
lean_inc(x_375);
lean_dec_ref(x_258);
x_376 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_257)) {
 x_377 = lean_alloc_ctor(0, 5, 0);
} else {
 x_377 = x_257;
}
lean_ctor_set(x_377, 0, x_148);
lean_ctor_set(x_377, 1, x_374);
lean_ctor_set(x_377, 2, x_375);
lean_ctor_set(x_377, 3, x_142);
lean_ctor_set(x_377, 4, x_142);
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_139);
lean_ctor_set(x_378, 2, x_140);
lean_ctor_set(x_378, 3, x_141);
lean_ctor_set(x_378, 4, x_377);
return x_378;
}
}
}
else
{
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_379; 
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
x_379 = !lean_is_exclusive(x_5);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_380 = lean_ctor_get(x_5, 4);
lean_dec(x_380);
x_381 = lean_ctor_get(x_5, 3);
lean_dec(x_381);
x_382 = lean_ctor_get(x_5, 2);
lean_dec(x_382);
x_383 = lean_ctor_get(x_5, 1);
lean_dec(x_383);
x_384 = lean_ctor_get(x_5, 0);
lean_dec(x_384);
x_385 = lean_ctor_get(x_258, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_258, 1);
lean_inc(x_386);
lean_dec_ref(x_258);
x_387 = !lean_is_exclusive(x_142);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_ctor_get(x_142, 1);
x_389 = lean_ctor_get(x_142, 2);
x_390 = lean_ctor_get(x_142, 4);
lean_dec(x_390);
x_391 = lean_ctor_get(x_142, 3);
lean_dec(x_391);
x_392 = lean_ctor_get(x_142, 0);
lean_dec(x_392);
x_393 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_142, 4, x_141);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 2, x_140);
lean_ctor_set(x_142, 1, x_139);
lean_ctor_set(x_142, 0, x_148);
if (lean_is_scalar(x_257)) {
 x_394 = lean_alloc_ctor(0, 5, 0);
} else {
 x_394 = x_257;
}
lean_ctor_set(x_394, 0, x_148);
lean_ctor_set(x_394, 1, x_385);
lean_ctor_set(x_394, 2, x_386);
lean_ctor_set(x_394, 3, x_141);
lean_ctor_set(x_394, 4, x_141);
lean_ctor_set(x_5, 4, x_394);
lean_ctor_set(x_5, 3, x_142);
lean_ctor_set(x_5, 2, x_389);
lean_ctor_set(x_5, 1, x_388);
lean_ctor_set(x_5, 0, x_393);
return x_5;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_395 = lean_ctor_get(x_142, 1);
x_396 = lean_ctor_get(x_142, 2);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_142);
x_397 = lean_unsigned_to_nat(3u);
x_398 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_398, 0, x_148);
lean_ctor_set(x_398, 1, x_139);
lean_ctor_set(x_398, 2, x_140);
lean_ctor_set(x_398, 3, x_141);
lean_ctor_set(x_398, 4, x_141);
if (lean_is_scalar(x_257)) {
 x_399 = lean_alloc_ctor(0, 5, 0);
} else {
 x_399 = x_257;
}
lean_ctor_set(x_399, 0, x_148);
lean_ctor_set(x_399, 1, x_385);
lean_ctor_set(x_399, 2, x_386);
lean_ctor_set(x_399, 3, x_141);
lean_ctor_set(x_399, 4, x_141);
lean_ctor_set(x_5, 4, x_399);
lean_ctor_set(x_5, 3, x_398);
lean_ctor_set(x_5, 2, x_396);
lean_ctor_set(x_5, 1, x_395);
lean_ctor_set(x_5, 0, x_397);
return x_5;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_5);
x_400 = lean_ctor_get(x_258, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_258, 1);
lean_inc(x_401);
lean_dec_ref(x_258);
x_402 = lean_ctor_get(x_142, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_142, 2);
lean_inc(x_403);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_404 = x_142;
} else {
 lean_dec_ref(x_142);
 x_404 = lean_box(0);
}
x_405 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 5, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_148);
lean_ctor_set(x_406, 1, x_139);
lean_ctor_set(x_406, 2, x_140);
lean_ctor_set(x_406, 3, x_141);
lean_ctor_set(x_406, 4, x_141);
if (lean_is_scalar(x_257)) {
 x_407 = lean_alloc_ctor(0, 5, 0);
} else {
 x_407 = x_257;
}
lean_ctor_set(x_407, 0, x_148);
lean_ctor_set(x_407, 1, x_400);
lean_ctor_set(x_407, 2, x_401);
lean_ctor_set(x_407, 3, x_141);
lean_ctor_set(x_407, 4, x_141);
x_408 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_402);
lean_ctor_set(x_408, 2, x_403);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set(x_408, 4, x_407);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_258, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_258, 1);
lean_inc(x_410);
lean_dec_ref(x_258);
x_411 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_257)) {
 x_412 = lean_alloc_ctor(0, 5, 0);
} else {
 x_412 = x_257;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_409);
lean_ctor_set(x_412, 2, x_410);
lean_ctor_set(x_412, 3, x_5);
lean_ctor_set(x_412, 4, x_142);
return x_412;
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(x_1, x_6);
x_414 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_413) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_5, 0);
x_417 = lean_ctor_get(x_5, 1);
x_418 = lean_ctor_get(x_5, 2);
x_419 = lean_ctor_get(x_5, 3);
x_420 = lean_ctor_get(x_5, 4);
lean_inc(x_420);
x_421 = lean_unsigned_to_nat(3u);
x_422 = lean_nat_mul(x_421, x_415);
x_423 = lean_nat_dec_lt(x_422, x_416);
lean_dec(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_420);
x_424 = lean_nat_add(x_414, x_416);
x_425 = lean_nat_add(x_424, x_415);
lean_dec(x_415);
lean_dec(x_424);
if (lean_is_scalar(x_7)) {
 x_426 = lean_alloc_ctor(0, 5, 0);
} else {
 x_426 = x_7;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_3);
lean_ctor_set(x_426, 2, x_4);
lean_ctor_set(x_426, 3, x_5);
lean_ctor_set(x_426, 4, x_413);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_427 = x_5;
} else {
 lean_dec_ref(x_5);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_419, 0);
x_429 = lean_ctor_get(x_420, 0);
x_430 = lean_ctor_get(x_420, 1);
x_431 = lean_ctor_get(x_420, 2);
x_432 = lean_ctor_get(x_420, 3);
x_433 = lean_ctor_get(x_420, 4);
x_434 = lean_unsigned_to_nat(2u);
x_435 = lean_nat_mul(x_434, x_428);
x_436 = lean_nat_dec_lt(x_429, x_435);
lean_dec(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_447; lean_object* x_448; 
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 lean_ctor_release(x_420, 4);
 x_437 = x_420;
} else {
 lean_dec_ref(x_420);
 x_437 = lean_box(0);
}
x_438 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_439 = lean_nat_add(x_438, x_415);
lean_dec(x_438);
x_447 = lean_nat_add(x_414, x_428);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_432, 0);
lean_inc(x_455);
x_448 = x_455;
goto block_454;
}
else
{
lean_object* x_456; 
x_456 = lean_unsigned_to_nat(0u);
x_448 = x_456;
goto block_454;
}
block_446:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_nat_add(x_441, x_442);
lean_dec(x_442);
lean_dec(x_441);
if (lean_is_scalar(x_437)) {
 x_444 = lean_alloc_ctor(0, 5, 0);
} else {
 x_444 = x_437;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_3);
lean_ctor_set(x_444, 2, x_4);
lean_ctor_set(x_444, 3, x_433);
lean_ctor_set(x_444, 4, x_413);
if (lean_is_scalar(x_427)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_427;
}
lean_ctor_set(x_445, 0, x_439);
lean_ctor_set(x_445, 1, x_430);
lean_ctor_set(x_445, 2, x_431);
lean_ctor_set(x_445, 3, x_440);
lean_ctor_set(x_445, 4, x_444);
return x_445;
}
block_454:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_nat_add(x_447, x_448);
lean_dec(x_448);
lean_dec(x_447);
if (lean_is_scalar(x_7)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_7;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_417);
lean_ctor_set(x_450, 2, x_418);
lean_ctor_set(x_450, 3, x_419);
lean_ctor_set(x_450, 4, x_432);
x_451 = lean_nat_add(x_414, x_415);
lean_dec(x_415);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_433, 0);
lean_inc(x_452);
x_440 = x_450;
x_441 = x_451;
x_442 = x_452;
goto block_446;
}
else
{
lean_object* x_453; 
x_453 = lean_unsigned_to_nat(0u);
x_440 = x_450;
x_441 = x_451;
x_442 = x_453;
goto block_446;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_7);
x_457 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_458 = lean_nat_add(x_457, x_415);
lean_dec(x_457);
x_459 = lean_nat_add(x_414, x_415);
lean_dec(x_415);
x_460 = lean_nat_add(x_459, x_429);
lean_dec(x_459);
lean_inc_ref(x_413);
if (lean_is_scalar(x_427)) {
 x_461 = lean_alloc_ctor(0, 5, 0);
} else {
 x_461 = x_427;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_3);
lean_ctor_set(x_461, 2, x_4);
lean_ctor_set(x_461, 3, x_420);
lean_ctor_set(x_461, 4, x_413);
x_462 = !lean_is_exclusive(x_413);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_463 = lean_ctor_get(x_413, 4);
lean_dec(x_463);
x_464 = lean_ctor_get(x_413, 3);
lean_dec(x_464);
x_465 = lean_ctor_get(x_413, 2);
lean_dec(x_465);
x_466 = lean_ctor_get(x_413, 1);
lean_dec(x_466);
x_467 = lean_ctor_get(x_413, 0);
lean_dec(x_467);
lean_ctor_set(x_413, 4, x_461);
lean_ctor_set(x_413, 3, x_419);
lean_ctor_set(x_413, 2, x_418);
lean_ctor_set(x_413, 1, x_417);
lean_ctor_set(x_413, 0, x_458);
return x_413;
}
else
{
lean_object* x_468; 
lean_dec(x_413);
x_468 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_468, 0, x_458);
lean_ctor_set(x_468, 1, x_417);
lean_ctor_set(x_468, 2, x_418);
lean_ctor_set(x_468, 3, x_419);
lean_ctor_set(x_468, 4, x_461);
return x_468;
}
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_413, 0);
lean_inc(x_469);
x_470 = lean_nat_add(x_414, x_469);
lean_dec(x_469);
if (lean_is_scalar(x_7)) {
 x_471 = lean_alloc_ctor(0, 5, 0);
} else {
 x_471 = x_7;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_3);
lean_ctor_set(x_471, 2, x_4);
lean_ctor_set(x_471, 3, x_5);
lean_ctor_set(x_471, 4, x_413);
return x_471;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; 
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_5, 4);
lean_inc(x_473);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
x_474 = !lean_is_exclusive(x_5);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_475 = lean_ctor_get(x_5, 0);
x_476 = lean_ctor_get(x_5, 1);
x_477 = lean_ctor_get(x_5, 2);
x_478 = lean_ctor_get(x_5, 4);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 3);
lean_dec(x_479);
x_480 = lean_ctor_get(x_473, 0);
x_481 = lean_nat_add(x_414, x_475);
lean_dec(x_475);
x_482 = lean_nat_add(x_414, x_480);
lean_ctor_set(x_5, 4, x_413);
lean_ctor_set(x_5, 3, x_473);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_482);
if (lean_is_scalar(x_7)) {
 x_483 = lean_alloc_ctor(0, 5, 0);
} else {
 x_483 = x_7;
}
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_472);
lean_ctor_set(x_483, 4, x_5);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_484 = lean_ctor_get(x_5, 0);
x_485 = lean_ctor_get(x_5, 1);
x_486 = lean_ctor_get(x_5, 2);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_5);
x_487 = lean_ctor_get(x_473, 0);
x_488 = lean_nat_add(x_414, x_484);
lean_dec(x_484);
x_489 = lean_nat_add(x_414, x_487);
x_490 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_3);
lean_ctor_set(x_490, 2, x_4);
lean_ctor_set(x_490, 3, x_473);
lean_ctor_set(x_490, 4, x_413);
if (lean_is_scalar(x_7)) {
 x_491 = lean_alloc_ctor(0, 5, 0);
} else {
 x_491 = x_7;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_485);
lean_ctor_set(x_491, 2, x_486);
lean_ctor_set(x_491, 3, x_472);
lean_ctor_set(x_491, 4, x_490);
return x_491;
}
}
else
{
uint8_t x_492; 
x_492 = !lean_is_exclusive(x_5);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = lean_ctor_get(x_5, 1);
x_494 = lean_ctor_get(x_5, 2);
x_495 = lean_ctor_get(x_5, 4);
lean_dec(x_495);
x_496 = lean_ctor_get(x_5, 3);
lean_dec(x_496);
x_497 = lean_ctor_get(x_5, 0);
lean_dec(x_497);
x_498 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_5, 3, x_473);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_499 = lean_alloc_ctor(0, 5, 0);
} else {
 x_499 = x_7;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_493);
lean_ctor_set(x_499, 2, x_494);
lean_ctor_set(x_499, 3, x_472);
lean_ctor_set(x_499, 4, x_5);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_500 = lean_ctor_get(x_5, 1);
x_501 = lean_ctor_get(x_5, 2);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_5);
x_502 = lean_unsigned_to_nat(3u);
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_414);
lean_ctor_set(x_503, 1, x_3);
lean_ctor_set(x_503, 2, x_4);
lean_ctor_set(x_503, 3, x_473);
lean_ctor_set(x_503, 4, x_473);
if (lean_is_scalar(x_7)) {
 x_504 = lean_alloc_ctor(0, 5, 0);
} else {
 x_504 = x_7;
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_500);
lean_ctor_set(x_504, 2, x_501);
lean_ctor_set(x_504, 3, x_472);
lean_ctor_set(x_504, 4, x_503);
return x_504;
}
}
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_5, 4);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
uint8_t x_506; 
lean_inc(x_472);
x_506 = !lean_is_exclusive(x_5);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_507 = lean_ctor_get(x_5, 1);
x_508 = lean_ctor_get(x_5, 2);
x_509 = lean_ctor_get(x_5, 4);
lean_dec(x_509);
x_510 = lean_ctor_get(x_5, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_5, 0);
lean_dec(x_511);
x_512 = !lean_is_exclusive(x_505);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_513 = lean_ctor_get(x_505, 1);
x_514 = lean_ctor_get(x_505, 2);
x_515 = lean_ctor_get(x_505, 4);
lean_dec(x_515);
x_516 = lean_ctor_get(x_505, 3);
lean_dec(x_516);
x_517 = lean_ctor_get(x_505, 0);
lean_dec(x_517);
x_518 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_505, 4, x_472);
lean_ctor_set(x_505, 3, x_472);
lean_ctor_set(x_505, 2, x_508);
lean_ctor_set(x_505, 1, x_507);
lean_ctor_set(x_505, 0, x_414);
lean_ctor_set(x_5, 4, x_472);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_519 = lean_alloc_ctor(0, 5, 0);
} else {
 x_519 = x_7;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_513);
lean_ctor_set(x_519, 2, x_514);
lean_ctor_set(x_519, 3, x_505);
lean_ctor_set(x_519, 4, x_5);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_520 = lean_ctor_get(x_505, 1);
x_521 = lean_ctor_get(x_505, 2);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_505);
x_522 = lean_unsigned_to_nat(3u);
x_523 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_523, 0, x_414);
lean_ctor_set(x_523, 1, x_507);
lean_ctor_set(x_523, 2, x_508);
lean_ctor_set(x_523, 3, x_472);
lean_ctor_set(x_523, 4, x_472);
lean_ctor_set(x_5, 4, x_472);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_7;
}
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_520);
lean_ctor_set(x_524, 2, x_521);
lean_ctor_set(x_524, 3, x_523);
lean_ctor_set(x_524, 4, x_5);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_525 = lean_ctor_get(x_5, 1);
x_526 = lean_ctor_get(x_5, 2);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_5);
x_527 = lean_ctor_get(x_505, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_505, 2);
lean_inc(x_528);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 lean_ctor_release(x_505, 4);
 x_529 = x_505;
} else {
 lean_dec_ref(x_505);
 x_529 = lean_box(0);
}
x_530 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_529)) {
 x_531 = lean_alloc_ctor(0, 5, 0);
} else {
 x_531 = x_529;
}
lean_ctor_set(x_531, 0, x_414);
lean_ctor_set(x_531, 1, x_525);
lean_ctor_set(x_531, 2, x_526);
lean_ctor_set(x_531, 3, x_472);
lean_ctor_set(x_531, 4, x_472);
x_532 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_532, 0, x_414);
lean_ctor_set(x_532, 1, x_3);
lean_ctor_set(x_532, 2, x_4);
lean_ctor_set(x_532, 3, x_472);
lean_ctor_set(x_532, 4, x_472);
if (lean_is_scalar(x_7)) {
 x_533 = lean_alloc_ctor(0, 5, 0);
} else {
 x_533 = x_7;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_527);
lean_ctor_set(x_533, 2, x_528);
lean_ctor_set(x_533, 3, x_531);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_535 = lean_alloc_ctor(0, 5, 0);
} else {
 x_535 = x_7;
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_5);
lean_ctor_set(x_535, 4, x_505);
return x_535;
}
}
}
else
{
lean_object* x_536; 
if (lean_is_scalar(x_7)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_7;
}
lean_ctor_set(x_536, 0, x_414);
lean_ctor_set(x_536, 1, x_3);
lean_ctor_set(x_536, 2, x_4);
lean_ctor_set(x_536, 3, x_5);
lean_ctor_set(x_536, 4, x_5);
return x_536;
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00main_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_find_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_ctor_set_tag(x_8, 0);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00main_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___00main_spec__10(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00main_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(x_3, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00main_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00main_spec__11(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_List_foldl___at___00main_spec__11(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_16 = lean_st_ref_get(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = l_Lean_postponedCompileDeclsExt;
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_dec(x_21);
x_24 = lean_box(1);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_24, x_18, x_17, x_20, x_25);
lean_dec(x_20);
x_28 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_22, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_22);
x_8 = x_26;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_29; 
lean_inc_ref(x_5);
lean_inc(x_22);
x_29 = l_Lean_getConstInfo___at___00main_spec__10(x_22, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_22);
x_31 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_30);
x_32 = lean_st_ref_take(x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 5);
lean_dec(x_35);
lean_inc_ref(x_31);
x_36 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0___boxed), 2, 1);
lean_closure_set(x_36, 0, x_31);
x_37 = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(x_18, x_34, x_36);
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
lean_ctor_set(x_32, 5, x_38);
lean_ctor_set(x_32, 0, x_37);
x_39 = lean_st_ref_set(x_6, x_32);
x_40 = lean_ctor_get(x_31, 3);
lean_inc(x_40);
lean_dec_ref(x_31);
x_41 = lean_array_mk(x_40);
lean_inc(x_6);
lean_inc_ref(x_5);
x_42 = l___private_LeanIR_0__main_doCompile(x_23, x_41, x_5, x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_8 = x_26;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
x_45 = lean_ctor_get(x_32, 2);
x_46 = lean_ctor_get(x_32, 3);
x_47 = lean_ctor_get(x_32, 4);
x_48 = lean_ctor_get(x_32, 6);
x_49 = lean_ctor_get(x_32, 7);
x_50 = lean_ctor_get(x_32, 8);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
lean_inc_ref(x_31);
x_51 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__0___boxed), 2, 1);
lean_closure_set(x_51, 0, x_31);
x_52 = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(x_18, x_43, x_51);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_54 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_46);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_48);
lean_ctor_set(x_54, 7, x_49);
lean_ctor_set(x_54, 8, x_50);
x_55 = lean_st_ref_set(x_6, x_54);
x_56 = lean_ctor_get(x_31, 3);
lean_inc(x_56);
lean_dec_ref(x_31);
x_57 = lean_array_mk(x_56);
lean_inc(x_6);
lean_inc_ref(x_5);
x_58 = l___private_LeanIR_0__main_doCompile(x_23, x_57, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_8 = x_26;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_30);
x_59 = lean_st_ref_take(x_6);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 5);
lean_dec(x_62);
lean_inc(x_22);
x_63 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1___boxed), 2, 1);
lean_closure_set(x_63, 0, x_22);
x_64 = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(x_18, x_61, x_63);
x_65 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
lean_ctor_set(x_59, 5, x_65);
lean_ctor_set(x_59, 0, x_64);
x_66 = lean_st_ref_set(x_6, x_59);
x_67 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3;
x_68 = lean_array_push(x_67, x_22);
lean_inc(x_6);
lean_inc_ref(x_5);
x_69 = l___private_LeanIR_0__main_doCompile(x_23, x_68, x_5, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_8 = x_26;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_59, 0);
x_71 = lean_ctor_get(x_59, 1);
x_72 = lean_ctor_get(x_59, 2);
x_73 = lean_ctor_get(x_59, 3);
x_74 = lean_ctor_get(x_59, 4);
x_75 = lean_ctor_get(x_59, 6);
x_76 = lean_ctor_get(x_59, 7);
x_77 = lean_ctor_get(x_59, 8);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_59);
lean_inc(x_22);
x_78 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___lam__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_22);
x_79 = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(x_18, x_70, x_78);
x_80 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_81 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_71);
lean_ctor_set(x_81, 2, x_72);
lean_ctor_set(x_81, 3, x_73);
lean_ctor_set(x_81, 4, x_74);
lean_ctor_set(x_81, 5, x_80);
lean_ctor_set(x_81, 6, x_75);
lean_ctor_set(x_81, 7, x_76);
lean_ctor_set(x_81, 8, x_77);
x_82 = lean_st_ref_set(x_6, x_81);
x_83 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3;
x_84 = lean_array_push(x_83, x_22);
lean_inc(x_6);
lean_inc_ref(x_5);
x_85 = l___private_LeanIR_0__main_doCompile(x_23, x_84, x_5, x_6);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
x_8 = x_26;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec_ref(x_5);
x_86 = !lean_is_exclusive(x_29);
if (x_86 == 0)
{
return x_29;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_29, 0);
lean_inc(x_87);
lean_dec(x_29);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_main___closed__3));
x_2 = lean_unsigned_to_nat(27u);
x_3 = lean_unsigned_to_nat(131u);
x_4 = ((lean_object*)(l_main___closed__2));
x_5 = ((lean_object*)(l_main___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_main___closed__10;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedClassState_default;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_main___closed__12;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_main___closed__9));
x_2 = ((lean_object*)(l_main___closed__8));
x_3 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_main___closed__15;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_main___closed__16;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_main___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_main___closed__3));
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_unsigned_to_nat(107u);
x_4 = ((lean_object*)(l_main___closed__2));
x_5 = ((lean_object*)(l_main___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_main___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_firstFrontendMacroScope;
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_main___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint8_t _init_l_main___closed__28() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 2;
x_2 = l_Lean_instOrdOLeanLevel_ord(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_main___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_main___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_169; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_31 = x_25;
} else {
 lean_dec_ref(x_25);
 x_31 = lean_box(0);
}
x_169 = l_Lean_ModuleSetup_load(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 6);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_LeanOptions_toOptions(x_172);
x_174 = l_List_forIn_x27_loop___at___00main_spec__2___redArg(x_30, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
x_176 = lean_init_search_path();
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_603; lean_object* x_604; uint8_t x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_667; lean_object* x_668; uint8_t x_669; uint8_t x_670; uint8_t x_1053; 
lean_dec_ref(x_176);
x_177 = l_main___closed__11;
x_178 = lean_box(0);
x_179 = l_main___closed__13;
x_180 = lean_box(1);
x_181 = ((lean_object*)(l_main___closed__14));
x_292 = l_main___closed__15;
x_293 = l_main___closed__17;
x_294 = l_main___closed__18;
x_295 = ((lean_object*)(l_main___closed__19));
x_296 = 1;
lean_inc(x_171);
x_297 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_297, 0, x_171);
lean_ctor_set_uint8(x_297, sizeof(void*)*1, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*1 + 1, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*1 + 2, x_296);
x_298 = lean_unsigned_to_nat(1u);
x_667 = l_main___closed__25;
x_668 = lean_array_push(x_667, x_297);
x_669 = 2;
x_1053 = l_main___closed__28;
if (x_1053 == 0)
{
x_670 = x_296;
goto block_1052;
}
else
{
uint8_t x_1054; 
x_1054 = 0;
x_670 = x_1054;
goto block_1052;
}
block_262:
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = lean_st_ref_get(x_191);
x_194 = lean_st_ref_take(x_191);
x_195 = !lean_is_exclusive(x_190);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_196 = lean_ctor_get(x_190, 4);
lean_dec(x_196);
x_197 = lean_ctor_get(x_190, 2);
lean_dec(x_197);
x_198 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_198);
lean_dec(x_193);
x_199 = lean_ctor_get(x_194, 0);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_194, 2);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_194, 3);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_194, 4);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_194, 6);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_194, 7);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_194, 8);
lean_inc_ref(x_206);
lean_dec(x_194);
x_207 = l_Lean_maxRecDepth;
x_208 = l_Lean_Option_get___at___00main_spec__5(x_175, x_207);
lean_ctor_set(x_190, 4, x_208);
lean_ctor_set(x_190, 2, x_175);
lean_ctor_set_uint8(x_190, sizeof(void*)*14, x_186);
x_209 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_188, x_198, x_185, x_184);
lean_dec(x_185);
lean_dec_ref(x_198);
x_210 = lean_array_get_size(x_209);
x_211 = lean_nat_dec_lt(x_187, x_210);
lean_dec(x_187);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_199, x_182);
x_145 = x_183;
x_146 = x_190;
x_147 = x_191;
x_148 = x_209;
x_149 = x_189;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
x_157 = lean_box(0);
x_158 = x_212;
goto block_168;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_210, x_210);
if (x_213 == 0)
{
if (x_211 == 0)
{
lean_object* x_214; 
x_214 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_199, x_182);
x_145 = x_183;
x_146 = x_190;
x_147 = x_191;
x_148 = x_209;
x_149 = x_189;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
x_157 = lean_box(0);
x_158 = x_214;
goto block_168;
}
else
{
size_t x_215; size_t x_216; lean_object* x_217; lean_object* x_218; 
x_215 = 0;
x_216 = lean_usize_of_nat(x_210);
x_217 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_209, x_215, x_216, x_182);
x_218 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_199, x_217);
x_145 = x_183;
x_146 = x_190;
x_147 = x_191;
x_148 = x_209;
x_149 = x_189;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
x_157 = lean_box(0);
x_158 = x_218;
goto block_168;
}
}
else
{
size_t x_219; size_t x_220; lean_object* x_221; lean_object* x_222; 
x_219 = 0;
x_220 = lean_usize_of_nat(x_210);
x_221 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_209, x_219, x_220, x_182);
x_222 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_199, x_221);
x_145 = x_183;
x_146 = x_190;
x_147 = x_191;
x_148 = x_209;
x_149 = x_189;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
x_157 = lean_box(0);
x_158 = x_222;
goto block_168;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_223 = lean_ctor_get(x_190, 0);
x_224 = lean_ctor_get(x_190, 1);
x_225 = lean_ctor_get(x_190, 3);
x_226 = lean_ctor_get(x_190, 5);
x_227 = lean_ctor_get(x_190, 6);
x_228 = lean_ctor_get(x_190, 7);
x_229 = lean_ctor_get(x_190, 8);
x_230 = lean_ctor_get(x_190, 9);
x_231 = lean_ctor_get(x_190, 10);
x_232 = lean_ctor_get(x_190, 11);
x_233 = lean_ctor_get(x_190, 12);
x_234 = lean_ctor_get_uint8(x_190, sizeof(void*)*14 + 1);
x_235 = lean_ctor_get(x_190, 13);
lean_inc(x_235);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_190);
x_236 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_236);
lean_dec(x_193);
x_237 = lean_ctor_get(x_194, 0);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_194, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_194, 2);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_194, 3);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_194, 4);
lean_inc_ref(x_241);
x_242 = lean_ctor_get(x_194, 6);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_194, 7);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_194, 8);
lean_inc_ref(x_244);
lean_dec(x_194);
x_245 = l_Lean_maxRecDepth;
x_246 = l_Lean_Option_get___at___00main_spec__5(x_175, x_245);
x_247 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_247, 0, x_223);
lean_ctor_set(x_247, 1, x_224);
lean_ctor_set(x_247, 2, x_175);
lean_ctor_set(x_247, 3, x_225);
lean_ctor_set(x_247, 4, x_246);
lean_ctor_set(x_247, 5, x_226);
lean_ctor_set(x_247, 6, x_227);
lean_ctor_set(x_247, 7, x_228);
lean_ctor_set(x_247, 8, x_229);
lean_ctor_set(x_247, 9, x_230);
lean_ctor_set(x_247, 10, x_231);
lean_ctor_set(x_247, 11, x_232);
lean_ctor_set(x_247, 12, x_233);
lean_ctor_set(x_247, 13, x_235);
lean_ctor_set_uint8(x_247, sizeof(void*)*14, x_186);
lean_ctor_set_uint8(x_247, sizeof(void*)*14 + 1, x_234);
x_248 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_188, x_236, x_185, x_184);
lean_dec(x_185);
lean_dec_ref(x_236);
x_249 = lean_array_get_size(x_248);
x_250 = lean_nat_dec_lt(x_187, x_249);
lean_dec(x_187);
if (x_250 == 0)
{
lean_object* x_251; 
x_251 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_237, x_182);
x_145 = x_183;
x_146 = x_247;
x_147 = x_191;
x_148 = x_248;
x_149 = x_189;
x_150 = x_238;
x_151 = x_239;
x_152 = x_240;
x_153 = x_241;
x_154 = x_242;
x_155 = x_243;
x_156 = x_244;
x_157 = lean_box(0);
x_158 = x_251;
goto block_168;
}
else
{
uint8_t x_252; 
x_252 = lean_nat_dec_le(x_249, x_249);
if (x_252 == 0)
{
if (x_250 == 0)
{
lean_object* x_253; 
x_253 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_237, x_182);
x_145 = x_183;
x_146 = x_247;
x_147 = x_191;
x_148 = x_248;
x_149 = x_189;
x_150 = x_238;
x_151 = x_239;
x_152 = x_240;
x_153 = x_241;
x_154 = x_242;
x_155 = x_243;
x_156 = x_244;
x_157 = lean_box(0);
x_158 = x_253;
goto block_168;
}
else
{
size_t x_254; size_t x_255; lean_object* x_256; lean_object* x_257; 
x_254 = 0;
x_255 = lean_usize_of_nat(x_249);
x_256 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_248, x_254, x_255, x_182);
x_257 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_237, x_256);
x_145 = x_183;
x_146 = x_247;
x_147 = x_191;
x_148 = x_248;
x_149 = x_189;
x_150 = x_238;
x_151 = x_239;
x_152 = x_240;
x_153 = x_241;
x_154 = x_242;
x_155 = x_243;
x_156 = x_244;
x_157 = lean_box(0);
x_158 = x_257;
goto block_168;
}
}
else
{
size_t x_258; size_t x_259; lean_object* x_260; lean_object* x_261; 
x_258 = 0;
x_259 = lean_usize_of_nat(x_249);
x_260 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_248, x_258, x_259, x_182);
x_261 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_188, x_237, x_260);
x_145 = x_183;
x_146 = x_247;
x_147 = x_191;
x_148 = x_248;
x_149 = x_189;
x_150 = x_238;
x_151 = x_239;
x_152 = x_240;
x_153 = x_241;
x_154 = x_242;
x_155 = x_243;
x_156 = x_244;
x_157 = lean_box(0);
x_158 = x_261;
goto block_168;
}
}
}
}
block_291:
{
if (x_273 == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_st_ref_take(x_272);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_274, 0);
x_277 = lean_ctor_get(x_274, 5);
lean_dec(x_277);
x_278 = l_Lean_Kernel_enableDiag(x_276, x_268);
lean_inc_ref(x_267);
lean_ctor_set(x_274, 5, x_267);
lean_ctor_set(x_274, 0, x_278);
x_279 = lean_st_ref_set(x_272, x_274);
lean_inc(x_272);
x_182 = x_263;
x_183 = x_267;
x_184 = x_266;
x_185 = x_265;
x_186 = x_268;
x_187 = x_269;
x_188 = x_270;
x_189 = x_272;
x_190 = x_264;
x_191 = x_272;
x_192 = lean_box(0);
goto block_262;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_280 = lean_ctor_get(x_274, 0);
x_281 = lean_ctor_get(x_274, 1);
x_282 = lean_ctor_get(x_274, 2);
x_283 = lean_ctor_get(x_274, 3);
x_284 = lean_ctor_get(x_274, 4);
x_285 = lean_ctor_get(x_274, 6);
x_286 = lean_ctor_get(x_274, 7);
x_287 = lean_ctor_get(x_274, 8);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_274);
x_288 = l_Lean_Kernel_enableDiag(x_280, x_268);
lean_inc_ref(x_267);
x_289 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_281);
lean_ctor_set(x_289, 2, x_282);
lean_ctor_set(x_289, 3, x_283);
lean_ctor_set(x_289, 4, x_284);
lean_ctor_set(x_289, 5, x_267);
lean_ctor_set(x_289, 6, x_285);
lean_ctor_set(x_289, 7, x_286);
lean_ctor_set(x_289, 8, x_287);
x_290 = lean_st_ref_set(x_272, x_289);
lean_inc(x_272);
x_182 = x_263;
x_183 = x_267;
x_184 = x_266;
x_185 = x_265;
x_186 = x_268;
x_187 = x_269;
x_188 = x_270;
x_189 = x_272;
x_190 = x_264;
x_191 = x_272;
x_192 = lean_box(0);
goto block_262;
}
}
else
{
lean_inc(x_272);
x_182 = x_263;
x_183 = x_267;
x_184 = x_266;
x_185 = x_265;
x_186 = x_268;
x_187 = x_269;
x_188 = x_270;
x_189 = x_272;
x_190 = x_264;
x_191 = x_272;
x_192 = lean_box(0);
goto block_262;
}
}
block_576:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
if (lean_is_scalar(x_31)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_31;
 lean_ctor_set_tag(x_311, 0);
}
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_EnvExtension_setState___redArg(x_303, x_305, x_311, x_304);
lean_dec(x_304);
x_313 = l_Lean_Environment_header(x_312);
x_314 = lean_ctor_get(x_313, 6);
lean_inc_ref(x_314);
lean_dec_ref(x_313);
x_315 = lean_array_get_size(x_314);
x_316 = lean_nat_dec_lt(x_302, x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
lean_dec_ref(x_314);
lean_dec_ref(x_312);
lean_dec_ref(x_307);
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_175);
lean_dec(x_29);
lean_dec(x_27);
x_317 = l_main___closed__20;
x_318 = l_panic___at___00main_spec__1(x_317);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_319 = lean_ctor_get(x_312, 0);
lean_inc_ref(x_319);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_320, 5);
lean_inc_ref(x_321);
x_322 = !lean_is_exclusive(x_312);
if (x_322 == 0)
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_ctor_get(x_312, 0);
lean_dec(x_323);
x_324 = !lean_is_exclusive(x_319);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; 
x_325 = lean_ctor_get(x_319, 0);
lean_dec(x_325);
x_326 = !lean_is_exclusive(x_320);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_320, 5);
lean_dec(x_327);
x_328 = !lean_is_exclusive(x_321);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint64_t x_336; lean_object* x_337; lean_object* x_338; size_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_363; 
x_329 = lean_ctor_get(x_321, 1);
lean_dec(x_329);
x_330 = lean_array_fget(x_314, x_302);
lean_dec_ref(x_314);
x_331 = lean_ctor_get(x_330, 0);
lean_inc_ref(x_331);
lean_dec(x_330);
lean_ctor_set(x_321, 1, x_331);
x_332 = l_Lean_firstFrontendMacroScope;
x_333 = l_main___closed__21;
x_334 = ((lean_object*)(l_main___closed__24));
lean_inc(x_300);
x_335 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_335, 0, x_300);
lean_ctor_set(x_335, 1, x_298);
lean_ctor_set(x_335, 2, x_178);
x_336 = 0;
x_337 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_338 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
x_339 = 5;
lean_inc_n(x_306, 2);
x_340 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_337);
lean_ctor_set(x_340, 2, x_306);
lean_ctor_set(x_340, 3, x_306);
lean_ctor_set_usize(x_340, 4, x_339);
lean_inc_ref(x_340);
x_341 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set_uint64(x_341, sizeof(void*)*1, x_336);
x_342 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
x_343 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_344 = l_Lean_NameSet_empty;
lean_inc_ref_n(x_340, 2);
x_345 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_340);
lean_ctor_set(x_345, 2, x_344);
x_346 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_346, 0, x_342);
lean_ctor_set(x_346, 1, x_342);
lean_ctor_set(x_346, 2, x_340);
lean_ctor_set_uint8(x_346, sizeof(void*)*3, x_296);
x_347 = lean_mk_empty_array_with_capacity(x_306);
x_348 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_348, 0, x_312);
lean_ctor_set(x_348, 1, x_333);
lean_ctor_set(x_348, 2, x_334);
lean_ctor_set(x_348, 3, x_335);
lean_ctor_set(x_348, 4, x_341);
lean_ctor_set(x_348, 5, x_343);
lean_ctor_set(x_348, 6, x_345);
lean_ctor_set(x_348, 7, x_346);
lean_ctor_set(x_348, 8, x_347);
x_349 = lean_st_mk_ref(x_348);
x_350 = l_Lean_inheritedTraceOptions;
x_351 = lean_st_ref_get(x_350);
x_352 = lean_st_ref_get(x_349);
x_353 = l_Lean_instInhabitedFileMap_default;
x_354 = lean_unsigned_to_nat(1000u);
x_355 = lean_box(0);
x_356 = l_Lean_Core_getMaxHeartbeats(x_175);
x_357 = 0;
x_358 = lean_box(0);
lean_inc(x_300);
lean_inc_n(x_306, 2);
lean_inc(x_175);
lean_inc(x_27);
x_359 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_359, 0, x_27);
lean_ctor_set(x_359, 1, x_353);
lean_ctor_set(x_359, 2, x_175);
lean_ctor_set(x_359, 3, x_306);
lean_ctor_set(x_359, 4, x_354);
lean_ctor_set(x_359, 5, x_355);
lean_ctor_set(x_359, 6, x_300);
lean_ctor_set(x_359, 7, x_178);
lean_ctor_set(x_359, 8, x_306);
lean_ctor_set(x_359, 9, x_356);
lean_ctor_set(x_359, 10, x_300);
lean_ctor_set(x_359, 11, x_332);
lean_ctor_set(x_359, 12, x_358);
lean_ctor_set(x_359, 13, x_351);
lean_ctor_set_uint8(x_359, sizeof(void*)*14, x_357);
lean_ctor_set_uint8(x_359, sizeof(void*)*14 + 1, x_357);
x_360 = lean_ctor_get(x_352, 0);
lean_inc_ref(x_360);
lean_dec(x_352);
x_361 = l_Lean_diagnostics;
x_362 = l_Lean_Option_get___at___00main_spec__4(x_175, x_361);
x_363 = l_Lean_Kernel_isDiagnosticsEnabled(x_360);
lean_dec_ref(x_360);
if (x_363 == 0)
{
if (x_362 == 0)
{
x_263 = x_299;
x_264 = x_359;
x_265 = x_302;
x_266 = x_301;
x_267 = x_343;
x_268 = x_362;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_349;
x_273 = x_316;
goto block_291;
}
else
{
x_263 = x_299;
x_264 = x_359;
x_265 = x_302;
x_266 = x_301;
x_267 = x_343;
x_268 = x_362;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_349;
x_273 = x_363;
goto block_291;
}
}
else
{
x_263 = x_299;
x_264 = x_359;
x_265 = x_302;
x_266 = x_301;
x_267 = x_343;
x_268 = x_362;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_349;
x_273 = x_362;
goto block_291;
}
}
else
{
uint32_t x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint64_t x_379; lean_object* x_380; lean_object* x_381; size_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; uint8_t x_406; 
x_364 = lean_ctor_get_uint32(x_321, sizeof(void*)*7);
x_365 = lean_ctor_get(x_321, 0);
x_366 = lean_ctor_get_uint8(x_321, sizeof(void*)*7 + 4);
x_367 = lean_ctor_get(x_321, 2);
x_368 = lean_ctor_get(x_321, 3);
x_369 = lean_ctor_get(x_321, 4);
x_370 = lean_ctor_get(x_321, 5);
x_371 = lean_ctor_get(x_321, 6);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_365);
lean_dec(x_321);
x_372 = lean_array_fget(x_314, x_302);
lean_dec_ref(x_314);
x_373 = lean_ctor_get(x_372, 0);
lean_inc_ref(x_373);
lean_dec(x_372);
x_374 = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(x_374, 0, x_365);
lean_ctor_set(x_374, 1, x_373);
lean_ctor_set(x_374, 2, x_367);
lean_ctor_set(x_374, 3, x_368);
lean_ctor_set(x_374, 4, x_369);
lean_ctor_set(x_374, 5, x_370);
lean_ctor_set(x_374, 6, x_371);
lean_ctor_set_uint32(x_374, sizeof(void*)*7, x_364);
lean_ctor_set_uint8(x_374, sizeof(void*)*7 + 4, x_366);
lean_ctor_set(x_320, 5, x_374);
x_375 = l_Lean_firstFrontendMacroScope;
x_376 = l_main___closed__21;
x_377 = ((lean_object*)(l_main___closed__24));
lean_inc(x_300);
x_378 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_378, 0, x_300);
lean_ctor_set(x_378, 1, x_298);
lean_ctor_set(x_378, 2, x_178);
x_379 = 0;
x_380 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_381 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
x_382 = 5;
lean_inc_n(x_306, 2);
x_383 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_380);
lean_ctor_set(x_383, 2, x_306);
lean_ctor_set(x_383, 3, x_306);
lean_ctor_set_usize(x_383, 4, x_382);
lean_inc_ref(x_383);
x_384 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set_uint64(x_384, sizeof(void*)*1, x_379);
x_385 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
x_386 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_387 = l_Lean_NameSet_empty;
lean_inc_ref_n(x_383, 2);
x_388 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_388, 0, x_383);
lean_ctor_set(x_388, 1, x_383);
lean_ctor_set(x_388, 2, x_387);
x_389 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_385);
lean_ctor_set(x_389, 2, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*3, x_296);
x_390 = lean_mk_empty_array_with_capacity(x_306);
x_391 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_391, 0, x_312);
lean_ctor_set(x_391, 1, x_376);
lean_ctor_set(x_391, 2, x_377);
lean_ctor_set(x_391, 3, x_378);
lean_ctor_set(x_391, 4, x_384);
lean_ctor_set(x_391, 5, x_386);
lean_ctor_set(x_391, 6, x_388);
lean_ctor_set(x_391, 7, x_389);
lean_ctor_set(x_391, 8, x_390);
x_392 = lean_st_mk_ref(x_391);
x_393 = l_Lean_inheritedTraceOptions;
x_394 = lean_st_ref_get(x_393);
x_395 = lean_st_ref_get(x_392);
x_396 = l_Lean_instInhabitedFileMap_default;
x_397 = lean_unsigned_to_nat(1000u);
x_398 = lean_box(0);
x_399 = l_Lean_Core_getMaxHeartbeats(x_175);
x_400 = 0;
x_401 = lean_box(0);
lean_inc(x_300);
lean_inc_n(x_306, 2);
lean_inc(x_175);
lean_inc(x_27);
x_402 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_402, 0, x_27);
lean_ctor_set(x_402, 1, x_396);
lean_ctor_set(x_402, 2, x_175);
lean_ctor_set(x_402, 3, x_306);
lean_ctor_set(x_402, 4, x_397);
lean_ctor_set(x_402, 5, x_398);
lean_ctor_set(x_402, 6, x_300);
lean_ctor_set(x_402, 7, x_178);
lean_ctor_set(x_402, 8, x_306);
lean_ctor_set(x_402, 9, x_399);
lean_ctor_set(x_402, 10, x_300);
lean_ctor_set(x_402, 11, x_375);
lean_ctor_set(x_402, 12, x_401);
lean_ctor_set(x_402, 13, x_394);
lean_ctor_set_uint8(x_402, sizeof(void*)*14, x_400);
lean_ctor_set_uint8(x_402, sizeof(void*)*14 + 1, x_400);
x_403 = lean_ctor_get(x_395, 0);
lean_inc_ref(x_403);
lean_dec(x_395);
x_404 = l_Lean_diagnostics;
x_405 = l_Lean_Option_get___at___00main_spec__4(x_175, x_404);
x_406 = l_Lean_Kernel_isDiagnosticsEnabled(x_403);
lean_dec_ref(x_403);
if (x_406 == 0)
{
if (x_405 == 0)
{
x_263 = x_299;
x_264 = x_402;
x_265 = x_302;
x_266 = x_301;
x_267 = x_386;
x_268 = x_405;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_392;
x_273 = x_316;
goto block_291;
}
else
{
x_263 = x_299;
x_264 = x_402;
x_265 = x_302;
x_266 = x_301;
x_267 = x_386;
x_268 = x_405;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_392;
x_273 = x_406;
goto block_291;
}
}
else
{
x_263 = x_299;
x_264 = x_402;
x_265 = x_302;
x_266 = x_301;
x_267 = x_386;
x_268 = x_405;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_392;
x_273 = x_405;
goto block_291;
}
}
}
else
{
lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint32_t x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint64_t x_430; lean_object* x_431; lean_object* x_432; size_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; uint8_t x_457; 
x_407 = lean_ctor_get(x_320, 0);
x_408 = lean_ctor_get_uint8(x_320, sizeof(void*)*6);
x_409 = lean_ctor_get(x_320, 1);
x_410 = lean_ctor_get(x_320, 2);
x_411 = lean_ctor_get(x_320, 3);
x_412 = lean_ctor_get(x_320, 4);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_407);
lean_dec(x_320);
x_413 = lean_ctor_get_uint32(x_321, sizeof(void*)*7);
x_414 = lean_ctor_get(x_321, 0);
lean_inc(x_414);
x_415 = lean_ctor_get_uint8(x_321, sizeof(void*)*7 + 4);
x_416 = lean_ctor_get(x_321, 2);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_321, 3);
lean_inc_ref(x_417);
x_418 = lean_ctor_get(x_321, 4);
lean_inc_ref(x_418);
x_419 = lean_ctor_get(x_321, 5);
lean_inc_ref(x_419);
x_420 = lean_ctor_get(x_321, 6);
lean_inc_ref(x_420);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 lean_ctor_release(x_321, 6);
 x_421 = x_321;
} else {
 lean_dec_ref(x_321);
 x_421 = lean_box(0);
}
x_422 = lean_array_fget(x_314, x_302);
lean_dec_ref(x_314);
x_423 = lean_ctor_get(x_422, 0);
lean_inc_ref(x_423);
lean_dec(x_422);
if (lean_is_scalar(x_421)) {
 x_424 = lean_alloc_ctor(0, 7, 5);
} else {
 x_424 = x_421;
}
lean_ctor_set(x_424, 0, x_414);
lean_ctor_set(x_424, 1, x_423);
lean_ctor_set(x_424, 2, x_416);
lean_ctor_set(x_424, 3, x_417);
lean_ctor_set(x_424, 4, x_418);
lean_ctor_set(x_424, 5, x_419);
lean_ctor_set(x_424, 6, x_420);
lean_ctor_set_uint32(x_424, sizeof(void*)*7, x_413);
lean_ctor_set_uint8(x_424, sizeof(void*)*7 + 4, x_415);
x_425 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_425, 0, x_407);
lean_ctor_set(x_425, 1, x_409);
lean_ctor_set(x_425, 2, x_410);
lean_ctor_set(x_425, 3, x_411);
lean_ctor_set(x_425, 4, x_412);
lean_ctor_set(x_425, 5, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*6, x_408);
lean_ctor_set(x_319, 0, x_425);
x_426 = l_Lean_firstFrontendMacroScope;
x_427 = l_main___closed__21;
x_428 = ((lean_object*)(l_main___closed__24));
lean_inc(x_300);
x_429 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_429, 0, x_300);
lean_ctor_set(x_429, 1, x_298);
lean_ctor_set(x_429, 2, x_178);
x_430 = 0;
x_431 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_432 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
x_433 = 5;
lean_inc_n(x_306, 2);
x_434 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_431);
lean_ctor_set(x_434, 2, x_306);
lean_ctor_set(x_434, 3, x_306);
lean_ctor_set_usize(x_434, 4, x_433);
lean_inc_ref(x_434);
x_435 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set_uint64(x_435, sizeof(void*)*1, x_430);
x_436 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
x_437 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_438 = l_Lean_NameSet_empty;
lean_inc_ref_n(x_434, 2);
x_439 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_439, 0, x_434);
lean_ctor_set(x_439, 1, x_434);
lean_ctor_set(x_439, 2, x_438);
x_440 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_436);
lean_ctor_set(x_440, 2, x_434);
lean_ctor_set_uint8(x_440, sizeof(void*)*3, x_296);
x_441 = lean_mk_empty_array_with_capacity(x_306);
x_442 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_442, 0, x_312);
lean_ctor_set(x_442, 1, x_427);
lean_ctor_set(x_442, 2, x_428);
lean_ctor_set(x_442, 3, x_429);
lean_ctor_set(x_442, 4, x_435);
lean_ctor_set(x_442, 5, x_437);
lean_ctor_set(x_442, 6, x_439);
lean_ctor_set(x_442, 7, x_440);
lean_ctor_set(x_442, 8, x_441);
x_443 = lean_st_mk_ref(x_442);
x_444 = l_Lean_inheritedTraceOptions;
x_445 = lean_st_ref_get(x_444);
x_446 = lean_st_ref_get(x_443);
x_447 = l_Lean_instInhabitedFileMap_default;
x_448 = lean_unsigned_to_nat(1000u);
x_449 = lean_box(0);
x_450 = l_Lean_Core_getMaxHeartbeats(x_175);
x_451 = 0;
x_452 = lean_box(0);
lean_inc(x_300);
lean_inc_n(x_306, 2);
lean_inc(x_175);
lean_inc(x_27);
x_453 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_453, 0, x_27);
lean_ctor_set(x_453, 1, x_447);
lean_ctor_set(x_453, 2, x_175);
lean_ctor_set(x_453, 3, x_306);
lean_ctor_set(x_453, 4, x_448);
lean_ctor_set(x_453, 5, x_449);
lean_ctor_set(x_453, 6, x_300);
lean_ctor_set(x_453, 7, x_178);
lean_ctor_set(x_453, 8, x_306);
lean_ctor_set(x_453, 9, x_450);
lean_ctor_set(x_453, 10, x_300);
lean_ctor_set(x_453, 11, x_426);
lean_ctor_set(x_453, 12, x_452);
lean_ctor_set(x_453, 13, x_445);
lean_ctor_set_uint8(x_453, sizeof(void*)*14, x_451);
lean_ctor_set_uint8(x_453, sizeof(void*)*14 + 1, x_451);
x_454 = lean_ctor_get(x_446, 0);
lean_inc_ref(x_454);
lean_dec(x_446);
x_455 = l_Lean_diagnostics;
x_456 = l_Lean_Option_get___at___00main_spec__4(x_175, x_455);
x_457 = l_Lean_Kernel_isDiagnosticsEnabled(x_454);
lean_dec_ref(x_454);
if (x_457 == 0)
{
if (x_456 == 0)
{
x_263 = x_299;
x_264 = x_453;
x_265 = x_302;
x_266 = x_301;
x_267 = x_437;
x_268 = x_456;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_443;
x_273 = x_316;
goto block_291;
}
else
{
x_263 = x_299;
x_264 = x_453;
x_265 = x_302;
x_266 = x_301;
x_267 = x_437;
x_268 = x_456;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_443;
x_273 = x_457;
goto block_291;
}
}
else
{
x_263 = x_299;
x_264 = x_453;
x_265 = x_302;
x_266 = x_301;
x_267 = x_437;
x_268 = x_456;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_443;
x_273 = x_456;
goto block_291;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint32_t x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint64_t x_484; lean_object* x_485; lean_object* x_486; size_t x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; uint8_t x_511; 
x_458 = lean_ctor_get(x_319, 1);
lean_inc(x_458);
lean_dec(x_319);
x_459 = lean_ctor_get(x_320, 0);
lean_inc_ref(x_459);
x_460 = lean_ctor_get_uint8(x_320, sizeof(void*)*6);
x_461 = lean_ctor_get(x_320, 1);
lean_inc_ref(x_461);
x_462 = lean_ctor_get(x_320, 2);
lean_inc_ref(x_462);
x_463 = lean_ctor_get(x_320, 3);
lean_inc_ref(x_463);
x_464 = lean_ctor_get(x_320, 4);
lean_inc_ref(x_464);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 lean_ctor_release(x_320, 2);
 lean_ctor_release(x_320, 3);
 lean_ctor_release(x_320, 4);
 lean_ctor_release(x_320, 5);
 x_465 = x_320;
} else {
 lean_dec_ref(x_320);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get_uint32(x_321, sizeof(void*)*7);
x_467 = lean_ctor_get(x_321, 0);
lean_inc(x_467);
x_468 = lean_ctor_get_uint8(x_321, sizeof(void*)*7 + 4);
x_469 = lean_ctor_get(x_321, 2);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_321, 3);
lean_inc_ref(x_470);
x_471 = lean_ctor_get(x_321, 4);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_321, 5);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_321, 6);
lean_inc_ref(x_473);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 lean_ctor_release(x_321, 6);
 x_474 = x_321;
} else {
 lean_dec_ref(x_321);
 x_474 = lean_box(0);
}
x_475 = lean_array_fget(x_314, x_302);
lean_dec_ref(x_314);
x_476 = lean_ctor_get(x_475, 0);
lean_inc_ref(x_476);
lean_dec(x_475);
if (lean_is_scalar(x_474)) {
 x_477 = lean_alloc_ctor(0, 7, 5);
} else {
 x_477 = x_474;
}
lean_ctor_set(x_477, 0, x_467);
lean_ctor_set(x_477, 1, x_476);
lean_ctor_set(x_477, 2, x_469);
lean_ctor_set(x_477, 3, x_470);
lean_ctor_set(x_477, 4, x_471);
lean_ctor_set(x_477, 5, x_472);
lean_ctor_set(x_477, 6, x_473);
lean_ctor_set_uint32(x_477, sizeof(void*)*7, x_466);
lean_ctor_set_uint8(x_477, sizeof(void*)*7 + 4, x_468);
if (lean_is_scalar(x_465)) {
 x_478 = lean_alloc_ctor(0, 6, 1);
} else {
 x_478 = x_465;
}
lean_ctor_set(x_478, 0, x_459);
lean_ctor_set(x_478, 1, x_461);
lean_ctor_set(x_478, 2, x_462);
lean_ctor_set(x_478, 3, x_463);
lean_ctor_set(x_478, 4, x_464);
lean_ctor_set(x_478, 5, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*6, x_460);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_458);
lean_ctor_set(x_312, 0, x_479);
x_480 = l_Lean_firstFrontendMacroScope;
x_481 = l_main___closed__21;
x_482 = ((lean_object*)(l_main___closed__24));
lean_inc(x_300);
x_483 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_483, 0, x_300);
lean_ctor_set(x_483, 1, x_298);
lean_ctor_set(x_483, 2, x_178);
x_484 = 0;
x_485 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_486 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
x_487 = 5;
lean_inc_n(x_306, 2);
x_488 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_485);
lean_ctor_set(x_488, 2, x_306);
lean_ctor_set(x_488, 3, x_306);
lean_ctor_set_usize(x_488, 4, x_487);
lean_inc_ref(x_488);
x_489 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set_uint64(x_489, sizeof(void*)*1, x_484);
x_490 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
x_491 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_492 = l_Lean_NameSet_empty;
lean_inc_ref_n(x_488, 2);
x_493 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_488);
lean_ctor_set(x_493, 2, x_492);
x_494 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_494, 0, x_490);
lean_ctor_set(x_494, 1, x_490);
lean_ctor_set(x_494, 2, x_488);
lean_ctor_set_uint8(x_494, sizeof(void*)*3, x_296);
x_495 = lean_mk_empty_array_with_capacity(x_306);
x_496 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_496, 0, x_312);
lean_ctor_set(x_496, 1, x_481);
lean_ctor_set(x_496, 2, x_482);
lean_ctor_set(x_496, 3, x_483);
lean_ctor_set(x_496, 4, x_489);
lean_ctor_set(x_496, 5, x_491);
lean_ctor_set(x_496, 6, x_493);
lean_ctor_set(x_496, 7, x_494);
lean_ctor_set(x_496, 8, x_495);
x_497 = lean_st_mk_ref(x_496);
x_498 = l_Lean_inheritedTraceOptions;
x_499 = lean_st_ref_get(x_498);
x_500 = lean_st_ref_get(x_497);
x_501 = l_Lean_instInhabitedFileMap_default;
x_502 = lean_unsigned_to_nat(1000u);
x_503 = lean_box(0);
x_504 = l_Lean_Core_getMaxHeartbeats(x_175);
x_505 = 0;
x_506 = lean_box(0);
lean_inc(x_300);
lean_inc_n(x_306, 2);
lean_inc(x_175);
lean_inc(x_27);
x_507 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_507, 0, x_27);
lean_ctor_set(x_507, 1, x_501);
lean_ctor_set(x_507, 2, x_175);
lean_ctor_set(x_507, 3, x_306);
lean_ctor_set(x_507, 4, x_502);
lean_ctor_set(x_507, 5, x_503);
lean_ctor_set(x_507, 6, x_300);
lean_ctor_set(x_507, 7, x_178);
lean_ctor_set(x_507, 8, x_306);
lean_ctor_set(x_507, 9, x_504);
lean_ctor_set(x_507, 10, x_300);
lean_ctor_set(x_507, 11, x_480);
lean_ctor_set(x_507, 12, x_506);
lean_ctor_set(x_507, 13, x_499);
lean_ctor_set_uint8(x_507, sizeof(void*)*14, x_505);
lean_ctor_set_uint8(x_507, sizeof(void*)*14 + 1, x_505);
x_508 = lean_ctor_get(x_500, 0);
lean_inc_ref(x_508);
lean_dec(x_500);
x_509 = l_Lean_diagnostics;
x_510 = l_Lean_Option_get___at___00main_spec__4(x_175, x_509);
x_511 = l_Lean_Kernel_isDiagnosticsEnabled(x_508);
lean_dec_ref(x_508);
if (x_511 == 0)
{
if (x_510 == 0)
{
x_263 = x_299;
x_264 = x_507;
x_265 = x_302;
x_266 = x_301;
x_267 = x_491;
x_268 = x_510;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_497;
x_273 = x_316;
goto block_291;
}
else
{
x_263 = x_299;
x_264 = x_507;
x_265 = x_302;
x_266 = x_301;
x_267 = x_491;
x_268 = x_510;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_497;
x_273 = x_511;
goto block_291;
}
}
else
{
x_263 = x_299;
x_264 = x_507;
x_265 = x_302;
x_266 = x_301;
x_267 = x_491;
x_268 = x_510;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_497;
x_273 = x_510;
goto block_291;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint32_t x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint64_t x_548; lean_object* x_549; lean_object* x_550; size_t x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; uint8_t x_575; 
x_512 = lean_ctor_get(x_312, 1);
x_513 = lean_ctor_get(x_312, 2);
x_514 = lean_ctor_get(x_312, 3);
x_515 = lean_ctor_get(x_312, 4);
x_516 = lean_ctor_get(x_312, 5);
x_517 = lean_ctor_get(x_312, 6);
x_518 = lean_ctor_get(x_312, 7);
x_519 = lean_ctor_get_uint8(x_312, sizeof(void*)*8);
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_312);
x_520 = lean_ctor_get(x_319, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_521 = x_319;
} else {
 lean_dec_ref(x_319);
 x_521 = lean_box(0);
}
x_522 = lean_ctor_get(x_320, 0);
lean_inc_ref(x_522);
x_523 = lean_ctor_get_uint8(x_320, sizeof(void*)*6);
x_524 = lean_ctor_get(x_320, 1);
lean_inc_ref(x_524);
x_525 = lean_ctor_get(x_320, 2);
lean_inc_ref(x_525);
x_526 = lean_ctor_get(x_320, 3);
lean_inc_ref(x_526);
x_527 = lean_ctor_get(x_320, 4);
lean_inc_ref(x_527);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 lean_ctor_release(x_320, 2);
 lean_ctor_release(x_320, 3);
 lean_ctor_release(x_320, 4);
 lean_ctor_release(x_320, 5);
 x_528 = x_320;
} else {
 lean_dec_ref(x_320);
 x_528 = lean_box(0);
}
x_529 = lean_ctor_get_uint32(x_321, sizeof(void*)*7);
x_530 = lean_ctor_get(x_321, 0);
lean_inc(x_530);
x_531 = lean_ctor_get_uint8(x_321, sizeof(void*)*7 + 4);
x_532 = lean_ctor_get(x_321, 2);
lean_inc_ref(x_532);
x_533 = lean_ctor_get(x_321, 3);
lean_inc_ref(x_533);
x_534 = lean_ctor_get(x_321, 4);
lean_inc_ref(x_534);
x_535 = lean_ctor_get(x_321, 5);
lean_inc_ref(x_535);
x_536 = lean_ctor_get(x_321, 6);
lean_inc_ref(x_536);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 lean_ctor_release(x_321, 6);
 x_537 = x_321;
} else {
 lean_dec_ref(x_321);
 x_537 = lean_box(0);
}
x_538 = lean_array_fget(x_314, x_302);
lean_dec_ref(x_314);
x_539 = lean_ctor_get(x_538, 0);
lean_inc_ref(x_539);
lean_dec(x_538);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 7, 5);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_530);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set(x_540, 2, x_532);
lean_ctor_set(x_540, 3, x_533);
lean_ctor_set(x_540, 4, x_534);
lean_ctor_set(x_540, 5, x_535);
lean_ctor_set(x_540, 6, x_536);
lean_ctor_set_uint32(x_540, sizeof(void*)*7, x_529);
lean_ctor_set_uint8(x_540, sizeof(void*)*7 + 4, x_531);
if (lean_is_scalar(x_528)) {
 x_541 = lean_alloc_ctor(0, 6, 1);
} else {
 x_541 = x_528;
}
lean_ctor_set(x_541, 0, x_522);
lean_ctor_set(x_541, 1, x_524);
lean_ctor_set(x_541, 2, x_525);
lean_ctor_set(x_541, 3, x_526);
lean_ctor_set(x_541, 4, x_527);
lean_ctor_set(x_541, 5, x_540);
lean_ctor_set_uint8(x_541, sizeof(void*)*6, x_523);
if (lean_is_scalar(x_521)) {
 x_542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_542 = x_521;
}
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_520);
x_543 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_512);
lean_ctor_set(x_543, 2, x_513);
lean_ctor_set(x_543, 3, x_514);
lean_ctor_set(x_543, 4, x_515);
lean_ctor_set(x_543, 5, x_516);
lean_ctor_set(x_543, 6, x_517);
lean_ctor_set(x_543, 7, x_518);
lean_ctor_set_uint8(x_543, sizeof(void*)*8, x_519);
x_544 = l_Lean_firstFrontendMacroScope;
x_545 = l_main___closed__21;
x_546 = ((lean_object*)(l_main___closed__24));
lean_inc(x_300);
x_547 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_547, 0, x_300);
lean_ctor_set(x_547, 1, x_298);
lean_ctor_set(x_547, 2, x_178);
x_548 = 0;
x_549 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0;
x_550 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1;
x_551 = 5;
lean_inc_n(x_306, 2);
x_552 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_549);
lean_ctor_set(x_552, 2, x_306);
lean_ctor_set(x_552, 3, x_306);
lean_ctor_set_usize(x_552, 4, x_551);
lean_inc_ref(x_552);
x_553 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set_uint64(x_553, sizeof(void*)*1, x_548);
x_554 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1;
x_555 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2;
x_556 = l_Lean_NameSet_empty;
lean_inc_ref_n(x_552, 2);
x_557 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_557, 0, x_552);
lean_ctor_set(x_557, 1, x_552);
lean_ctor_set(x_557, 2, x_556);
x_558 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_558, 0, x_554);
lean_ctor_set(x_558, 1, x_554);
lean_ctor_set(x_558, 2, x_552);
lean_ctor_set_uint8(x_558, sizeof(void*)*3, x_296);
x_559 = lean_mk_empty_array_with_capacity(x_306);
x_560 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_560, 0, x_543);
lean_ctor_set(x_560, 1, x_545);
lean_ctor_set(x_560, 2, x_546);
lean_ctor_set(x_560, 3, x_547);
lean_ctor_set(x_560, 4, x_553);
lean_ctor_set(x_560, 5, x_555);
lean_ctor_set(x_560, 6, x_557);
lean_ctor_set(x_560, 7, x_558);
lean_ctor_set(x_560, 8, x_559);
x_561 = lean_st_mk_ref(x_560);
x_562 = l_Lean_inheritedTraceOptions;
x_563 = lean_st_ref_get(x_562);
x_564 = lean_st_ref_get(x_561);
x_565 = l_Lean_instInhabitedFileMap_default;
x_566 = lean_unsigned_to_nat(1000u);
x_567 = lean_box(0);
x_568 = l_Lean_Core_getMaxHeartbeats(x_175);
x_569 = 0;
x_570 = lean_box(0);
lean_inc(x_300);
lean_inc_n(x_306, 2);
lean_inc(x_175);
lean_inc(x_27);
x_571 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_571, 0, x_27);
lean_ctor_set(x_571, 1, x_565);
lean_ctor_set(x_571, 2, x_175);
lean_ctor_set(x_571, 3, x_306);
lean_ctor_set(x_571, 4, x_566);
lean_ctor_set(x_571, 5, x_567);
lean_ctor_set(x_571, 6, x_300);
lean_ctor_set(x_571, 7, x_178);
lean_ctor_set(x_571, 8, x_306);
lean_ctor_set(x_571, 9, x_568);
lean_ctor_set(x_571, 10, x_300);
lean_ctor_set(x_571, 11, x_544);
lean_ctor_set(x_571, 12, x_570);
lean_ctor_set(x_571, 13, x_563);
lean_ctor_set_uint8(x_571, sizeof(void*)*14, x_569);
lean_ctor_set_uint8(x_571, sizeof(void*)*14 + 1, x_569);
x_572 = lean_ctor_get(x_564, 0);
lean_inc_ref(x_572);
lean_dec(x_564);
x_573 = l_Lean_diagnostics;
x_574 = l_Lean_Option_get___at___00main_spec__4(x_175, x_573);
x_575 = l_Lean_Kernel_isDiagnosticsEnabled(x_572);
lean_dec_ref(x_572);
if (x_575 == 0)
{
if (x_574 == 0)
{
x_263 = x_299;
x_264 = x_571;
x_265 = x_302;
x_266 = x_301;
x_267 = x_555;
x_268 = x_574;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_561;
x_273 = x_316;
goto block_291;
}
else
{
x_263 = x_299;
x_264 = x_571;
x_265 = x_302;
x_266 = x_301;
x_267 = x_555;
x_268 = x_574;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_561;
x_273 = x_575;
goto block_291;
}
}
else
{
x_263 = x_299;
x_264 = x_571;
x_265 = x_302;
x_266 = x_301;
x_267 = x_555;
x_268 = x_574;
x_269 = x_306;
x_270 = x_307;
x_271 = lean_box(0);
x_272 = x_561;
x_273 = x_574;
goto block_291;
}
}
}
}
block_602:
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_586 = l_Lean_IR_declMapExt;
x_587 = lean_ctor_get(x_586, 0);
lean_inc_ref(x_587);
x_588 = lean_ctor_get(x_587, 2);
lean_inc(x_578);
lean_inc_ref(x_585);
x_589 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_293, x_587, x_585, x_588, x_578);
x_590 = lean_ctor_get(x_589, 0);
lean_inc_ref(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = lean_array_get_borrowed(x_294, x_590, x_579);
x_593 = lean_array_get_size(x_592);
x_594 = lean_nat_dec_lt(x_582, x_593);
if (x_594 == 0)
{
x_299 = x_577;
x_300 = x_578;
x_301 = x_580;
x_302 = x_579;
x_303 = x_587;
x_304 = x_581;
x_305 = x_585;
x_306 = x_582;
x_307 = x_584;
x_308 = lean_box(0);
x_309 = x_590;
x_310 = x_591;
goto block_576;
}
else
{
uint8_t x_595; 
x_595 = lean_nat_dec_le(x_593, x_593);
if (x_595 == 0)
{
if (x_594 == 0)
{
x_299 = x_577;
x_300 = x_578;
x_301 = x_580;
x_302 = x_579;
x_303 = x_587;
x_304 = x_581;
x_305 = x_585;
x_306 = x_582;
x_307 = x_584;
x_308 = lean_box(0);
x_309 = x_590;
x_310 = x_591;
goto block_576;
}
else
{
size_t x_596; size_t x_597; lean_object* x_598; 
x_596 = 0;
x_597 = lean_usize_of_nat(x_593);
lean_inc_ref(x_585);
x_598 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(x_585, x_592, x_596, x_597, x_591);
x_299 = x_577;
x_300 = x_578;
x_301 = x_580;
x_302 = x_579;
x_303 = x_587;
x_304 = x_581;
x_305 = x_585;
x_306 = x_582;
x_307 = x_584;
x_308 = lean_box(0);
x_309 = x_590;
x_310 = x_598;
goto block_576;
}
}
else
{
size_t x_599; size_t x_600; lean_object* x_601; 
x_599 = 0;
x_600 = lean_usize_of_nat(x_593);
lean_inc_ref(x_585);
x_601 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(x_585, x_592, x_599, x_600, x_591);
x_299 = x_577;
x_300 = x_578;
x_301 = x_580;
x_302 = x_579;
x_303 = x_587;
x_304 = x_581;
x_305 = x_585;
x_306 = x_582;
x_307 = x_584;
x_308 = lean_box(0);
x_309 = x_590;
x_310 = x_601;
goto block_576;
}
}
}
block_622:
{
uint8_t x_614; 
x_614 = lean_nat_dec_lt(x_608, x_612);
if (x_614 == 0)
{
lean_dec(x_612);
lean_dec_ref(x_611);
x_577 = x_603;
x_578 = x_604;
x_579 = x_606;
x_580 = x_605;
x_581 = x_607;
x_582 = x_608;
x_583 = lean_box(0);
x_584 = x_609;
x_585 = x_613;
goto block_602;
}
else
{
uint8_t x_615; 
x_615 = lean_nat_dec_le(x_612, x_612);
if (x_615 == 0)
{
if (x_614 == 0)
{
lean_dec(x_612);
lean_dec_ref(x_611);
x_577 = x_603;
x_578 = x_604;
x_579 = x_606;
x_580 = x_605;
x_581 = x_607;
x_582 = x_608;
x_583 = lean_box(0);
x_584 = x_609;
x_585 = x_613;
goto block_602;
}
else
{
size_t x_616; size_t x_617; lean_object* x_618; 
x_616 = 0;
x_617 = lean_usize_of_nat(x_612);
lean_dec(x_612);
x_618 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(x_611, x_616, x_617, x_613);
lean_dec_ref(x_611);
x_577 = x_603;
x_578 = x_604;
x_579 = x_606;
x_580 = x_605;
x_581 = x_607;
x_582 = x_608;
x_583 = lean_box(0);
x_584 = x_609;
x_585 = x_618;
goto block_602;
}
}
else
{
size_t x_619; size_t x_620; lean_object* x_621; 
x_619 = 0;
x_620 = lean_usize_of_nat(x_612);
lean_dec(x_612);
x_621 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(x_611, x_619, x_620, x_613);
lean_dec_ref(x_611);
x_577 = x_603;
x_578 = x_604;
x_579 = x_606;
x_580 = x_605;
x_581 = x_607;
x_582 = x_608;
x_583 = lean_box(0);
x_584 = x_609;
x_585 = x_621;
goto block_602;
}
}
}
block_642:
{
lean_object* x_633; uint8_t x_634; 
x_633 = lean_array_get_size(x_632);
x_634 = lean_nat_dec_lt(x_628, x_633);
if (x_634 == 0)
{
x_603 = x_623;
x_604 = x_624;
x_605 = x_626;
x_606 = x_625;
x_607 = x_627;
x_608 = x_628;
x_609 = x_630;
x_610 = lean_box(0);
x_611 = x_632;
x_612 = x_633;
x_613 = x_631;
goto block_622;
}
else
{
uint8_t x_635; 
x_635 = lean_nat_dec_le(x_633, x_633);
if (x_635 == 0)
{
if (x_634 == 0)
{
x_603 = x_623;
x_604 = x_624;
x_605 = x_626;
x_606 = x_625;
x_607 = x_627;
x_608 = x_628;
x_609 = x_630;
x_610 = lean_box(0);
x_611 = x_632;
x_612 = x_633;
x_613 = x_631;
goto block_622;
}
else
{
size_t x_636; size_t x_637; lean_object* x_638; 
x_636 = 0;
x_637 = lean_usize_of_nat(x_633);
x_638 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(x_632, x_636, x_637, x_631);
x_603 = x_623;
x_604 = x_624;
x_605 = x_626;
x_606 = x_625;
x_607 = x_627;
x_608 = x_628;
x_609 = x_630;
x_610 = lean_box(0);
x_611 = x_632;
x_612 = x_633;
x_613 = x_638;
goto block_622;
}
}
else
{
size_t x_639; size_t x_640; lean_object* x_641; 
x_639 = 0;
x_640 = lean_usize_of_nat(x_633);
x_641 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(x_632, x_639, x_640, x_631);
x_603 = x_623;
x_604 = x_624;
x_605 = x_626;
x_606 = x_625;
x_607 = x_627;
x_608 = x_628;
x_609 = x_630;
x_610 = lean_box(0);
x_611 = x_632;
x_612 = x_633;
x_613 = x_641;
goto block_622;
}
}
}
block_666:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; 
lean_inc_ref(x_650);
x_653 = l_Lean_SimplePersistentEnvExtension_setState___redArg(x_650, x_651, x_652);
x_654 = l_Lean_Compiler_LCNF_impureSigExt;
x_655 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_292, x_654, x_653, x_646, x_645);
x_656 = lean_array_get_size(x_655);
x_657 = lean_mk_empty_array_with_capacity(x_648);
x_658 = lean_nat_dec_lt(x_648, x_656);
if (x_658 == 0)
{
lean_dec_ref(x_655);
x_623 = x_643;
x_624 = x_644;
x_625 = x_646;
x_626 = x_645;
x_627 = x_647;
x_628 = x_648;
x_629 = lean_box(0);
x_630 = x_650;
x_631 = x_653;
x_632 = x_657;
goto block_642;
}
else
{
uint8_t x_659; 
x_659 = lean_nat_dec_le(x_656, x_656);
if (x_659 == 0)
{
if (x_658 == 0)
{
lean_dec_ref(x_655);
x_623 = x_643;
x_624 = x_644;
x_625 = x_646;
x_626 = x_645;
x_627 = x_647;
x_628 = x_648;
x_629 = lean_box(0);
x_630 = x_650;
x_631 = x_653;
x_632 = x_657;
goto block_642;
}
else
{
size_t x_660; size_t x_661; lean_object* x_662; 
x_660 = 0;
x_661 = lean_usize_of_nat(x_656);
lean_inc_ref(x_653);
x_662 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(x_653, x_655, x_660, x_661, x_657);
lean_dec_ref(x_655);
x_623 = x_643;
x_624 = x_644;
x_625 = x_646;
x_626 = x_645;
x_627 = x_647;
x_628 = x_648;
x_629 = lean_box(0);
x_630 = x_650;
x_631 = x_653;
x_632 = x_662;
goto block_642;
}
}
else
{
size_t x_663; size_t x_664; lean_object* x_665; 
x_663 = 0;
x_664 = lean_usize_of_nat(x_656);
lean_inc_ref(x_653);
x_665 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(x_653, x_655, x_663, x_664, x_657);
lean_dec_ref(x_655);
x_623 = x_643;
x_624 = x_644;
x_625 = x_646;
x_626 = x_645;
x_627 = x_647;
x_628 = x_648;
x_629 = lean_box(0);
x_630 = x_650;
x_631 = x_653;
x_632 = x_665;
goto block_642;
}
}
}
block_1052:
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_671 = l_Lean_instInhabitedImportState_default;
x_672 = lean_box(x_669);
x_673 = lean_box(x_670);
x_674 = lean_box(x_296);
lean_inc(x_175);
lean_inc(x_171);
x_675 = lean_alloc_closure((void*)(l_main___lam__0___boxed), 9, 8);
lean_closure_set(x_675, 0, x_671);
lean_closure_set(x_675, 1, x_668);
lean_closure_set(x_675, 2, x_672);
lean_closure_set(x_675, 3, x_180);
lean_closure_set(x_675, 4, x_673);
lean_closure_set(x_675, 5, x_171);
lean_closure_set(x_675, 6, x_175);
lean_closure_set(x_675, 7, x_674);
x_676 = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(x_676, 0, lean_box(0));
lean_closure_set(x_676, 1, x_675);
x_677 = lean_box(0);
x_678 = l_Lean_profileitIOUnsafe___redArg(x_295, x_175, x_676, x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
lean_dec_ref(x_678);
x_680 = l_Lean_Compiler_CSimp_ext;
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; uint8_t x_689; 
x_682 = lean_ctor_get(x_680, 1);
x_683 = lean_ctor_get(x_680, 0);
lean_dec(x_683);
x_684 = lean_ctor_get(x_682, 0);
lean_inc_ref(x_684);
x_685 = lean_ctor_get(x_682, 2);
lean_inc_ref(x_685);
lean_dec_ref(x_682);
x_686 = lean_ctor_get(x_684, 2);
lean_inc(x_171);
x_687 = l_Lean_Environment_setMainModule(x_679, x_171);
lean_inc_ref(x_687);
x_688 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_177, x_684, x_687, x_686, x_677);
x_689 = !lean_is_exclusive(x_688);
if (x_689 == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_688, 0);
x_691 = lean_ctor_get(x_688, 1);
lean_dec(x_691);
x_692 = l_Lean_Options_empty;
lean_inc_ref(x_687);
lean_ctor_set(x_680, 1, x_692);
lean_ctor_set(x_680, 0, x_687);
lean_inc_ref(x_690);
x_693 = lean_apply_3(x_685, x_690, x_680, lean_box(0));
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; uint8_t x_696; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
lean_dec_ref(x_693);
x_695 = l_Lean_Meta_instanceExtension;
x_696 = !lean_is_exclusive(x_695);
if (x_696 == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; 
x_697 = lean_ctor_get(x_695, 1);
x_698 = lean_ctor_get(x_695, 0);
lean_dec(x_698);
x_699 = lean_ctor_get(x_697, 0);
lean_inc_ref(x_699);
x_700 = lean_ctor_get(x_697, 2);
lean_inc_ref(x_700);
lean_dec_ref(x_697);
x_701 = lean_ctor_get(x_699, 2);
lean_ctor_set(x_688, 1, x_694);
x_702 = lean_box(0);
x_703 = l_Lean_EnvExtension_setState___redArg(x_684, x_687, x_688, x_702);
lean_inc_ref(x_703);
x_704 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_177, x_699, x_703, x_701, x_677);
x_705 = !lean_is_exclusive(x_704);
if (x_705 == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_704, 0);
x_707 = lean_ctor_get(x_704, 1);
lean_dec(x_707);
lean_inc_ref(x_703);
lean_ctor_set(x_695, 1, x_692);
lean_ctor_set(x_695, 0, x_703);
lean_inc_ref(x_706);
x_708 = lean_apply_3(x_700, x_706, x_695, lean_box(0));
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec_ref(x_708);
x_710 = l_Lean_classExtension;
x_711 = lean_ctor_get(x_710, 0);
lean_inc_ref(x_711);
x_712 = lean_ctor_get(x_710, 2);
lean_inc_ref(x_712);
x_713 = lean_ctor_get(x_711, 2);
lean_ctor_set(x_704, 1, x_709);
x_714 = l_Lean_EnvExtension_setState___redArg(x_699, x_703, x_704, x_702);
lean_inc_ref(x_714);
x_715 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_179, x_711, x_714, x_713, x_677);
x_716 = !lean_is_exclusive(x_715);
if (x_716 == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_717 = lean_ctor_get(x_715, 0);
x_718 = lean_ctor_get(x_715, 1);
lean_dec(x_718);
lean_inc_ref(x_714);
if (lean_is_scalar(x_28)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_28;
 lean_ctor_set_tag(x_719, 0);
}
lean_ctor_set(x_719, 0, x_714);
lean_ctor_set(x_719, 1, x_692);
lean_inc_ref(x_717);
x_720 = lean_apply_3(x_712, x_717, x_719, lean_box(0));
if (lean_obj_tag(x_720) == 0)
{
uint8_t x_721; 
x_721 = !lean_is_exclusive(x_720);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_720, 0);
lean_ctor_set(x_715, 1, x_722);
x_723 = l_Lean_EnvExtension_setState___redArg(x_711, x_714, x_715, x_702);
x_724 = l_Lean_Environment_getModuleIdx_x3f(x_723, x_171);
if (lean_obj_tag(x_724) == 1)
{
lean_object* x_725; lean_object* x_726; uint8_t x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
lean_free_object(x_720);
lean_dec(x_171);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
lean_dec_ref(x_724);
x_726 = l_Lean_postponedCompileDeclsExt;
x_727 = 0;
x_728 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_726, x_723, x_725, x_727);
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_array_get_size(x_728);
x_731 = lean_nat_dec_lt(x_729, x_730);
if (x_731 == 0)
{
lean_dec_ref(x_728);
x_643 = x_180;
x_644 = x_677;
x_645 = x_727;
x_646 = x_725;
x_647 = x_702;
x_648 = x_729;
x_649 = lean_box(0);
x_650 = x_726;
x_651 = x_723;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_732; 
x_732 = lean_nat_dec_le(x_730, x_730);
if (x_732 == 0)
{
if (x_731 == 0)
{
lean_dec_ref(x_728);
x_643 = x_180;
x_644 = x_677;
x_645 = x_727;
x_646 = x_725;
x_647 = x_702;
x_648 = x_729;
x_649 = lean_box(0);
x_650 = x_726;
x_651 = x_723;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_733; size_t x_734; lean_object* x_735; 
x_733 = 0;
x_734 = lean_usize_of_nat(x_730);
x_735 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_728, x_733, x_734, x_180);
lean_dec_ref(x_728);
x_643 = x_180;
x_644 = x_677;
x_645 = x_727;
x_646 = x_725;
x_647 = x_702;
x_648 = x_729;
x_649 = lean_box(0);
x_650 = x_726;
x_651 = x_723;
x_652 = x_735;
goto block_666;
}
}
else
{
size_t x_736; size_t x_737; lean_object* x_738; 
x_736 = 0;
x_737 = lean_usize_of_nat(x_730);
x_738 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_728, x_736, x_737, x_180);
lean_dec_ref(x_728);
x_643 = x_180;
x_644 = x_677;
x_645 = x_727;
x_646 = x_725;
x_647 = x_702;
x_648 = x_729;
x_649 = lean_box(0);
x_650 = x_726;
x_651 = x_723;
x_652 = x_738;
goto block_666;
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_724);
lean_dec_ref(x_723);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_739 = ((lean_object*)(l_main___closed__26));
x_740 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_741 = lean_string_append(x_739, x_740);
lean_dec_ref(x_740);
x_742 = ((lean_object*)(l_main___closed__27));
x_743 = lean_string_append(x_741, x_742);
x_744 = lean_mk_io_user_error(x_743);
lean_ctor_set_tag(x_720, 1);
lean_ctor_set(x_720, 0, x_744);
return x_720;
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = lean_ctor_get(x_720, 0);
lean_inc(x_745);
lean_dec(x_720);
lean_ctor_set(x_715, 1, x_745);
x_746 = l_Lean_EnvExtension_setState___redArg(x_711, x_714, x_715, x_702);
x_747 = l_Lean_Environment_getModuleIdx_x3f(x_746, x_171);
if (lean_obj_tag(x_747) == 1)
{
lean_object* x_748; lean_object* x_749; uint8_t x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; 
lean_dec(x_171);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
lean_dec_ref(x_747);
x_749 = l_Lean_postponedCompileDeclsExt;
x_750 = 0;
x_751 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_749, x_746, x_748, x_750);
x_752 = lean_unsigned_to_nat(0u);
x_753 = lean_array_get_size(x_751);
x_754 = lean_nat_dec_lt(x_752, x_753);
if (x_754 == 0)
{
lean_dec_ref(x_751);
x_643 = x_180;
x_644 = x_677;
x_645 = x_750;
x_646 = x_748;
x_647 = x_702;
x_648 = x_752;
x_649 = lean_box(0);
x_650 = x_749;
x_651 = x_746;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_755; 
x_755 = lean_nat_dec_le(x_753, x_753);
if (x_755 == 0)
{
if (x_754 == 0)
{
lean_dec_ref(x_751);
x_643 = x_180;
x_644 = x_677;
x_645 = x_750;
x_646 = x_748;
x_647 = x_702;
x_648 = x_752;
x_649 = lean_box(0);
x_650 = x_749;
x_651 = x_746;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_756; size_t x_757; lean_object* x_758; 
x_756 = 0;
x_757 = lean_usize_of_nat(x_753);
x_758 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_751, x_756, x_757, x_180);
lean_dec_ref(x_751);
x_643 = x_180;
x_644 = x_677;
x_645 = x_750;
x_646 = x_748;
x_647 = x_702;
x_648 = x_752;
x_649 = lean_box(0);
x_650 = x_749;
x_651 = x_746;
x_652 = x_758;
goto block_666;
}
}
else
{
size_t x_759; size_t x_760; lean_object* x_761; 
x_759 = 0;
x_760 = lean_usize_of_nat(x_753);
x_761 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_751, x_759, x_760, x_180);
lean_dec_ref(x_751);
x_643 = x_180;
x_644 = x_677;
x_645 = x_750;
x_646 = x_748;
x_647 = x_702;
x_648 = x_752;
x_649 = lean_box(0);
x_650 = x_749;
x_651 = x_746;
x_652 = x_761;
goto block_666;
}
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_747);
lean_dec_ref(x_746);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_762 = ((lean_object*)(l_main___closed__26));
x_763 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_764 = lean_string_append(x_762, x_763);
lean_dec_ref(x_763);
x_765 = ((lean_object*)(l_main___closed__27));
x_766 = lean_string_append(x_764, x_765);
x_767 = lean_mk_io_user_error(x_766);
x_768 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_768, 0, x_767);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_free_object(x_715);
lean_dec_ref(x_717);
lean_dec_ref(x_714);
lean_dec_ref(x_711);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_769 = !lean_is_exclusive(x_720);
if (x_769 == 0)
{
return x_720;
}
else
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_720, 0);
lean_inc(x_770);
lean_dec(x_720);
x_771 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_771, 0, x_770);
return x_771;
}
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_715, 0);
lean_inc(x_772);
lean_dec(x_715);
lean_inc_ref(x_714);
if (lean_is_scalar(x_28)) {
 x_773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_773 = x_28;
 lean_ctor_set_tag(x_773, 0);
}
lean_ctor_set(x_773, 0, x_714);
lean_ctor_set(x_773, 1, x_692);
lean_inc_ref(x_772);
x_774 = lean_apply_3(x_712, x_772, x_773, lean_box(0));
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_776 = x_774;
} else {
 lean_dec_ref(x_774);
 x_776 = lean_box(0);
}
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_772);
lean_ctor_set(x_777, 1, x_775);
x_778 = l_Lean_EnvExtension_setState___redArg(x_711, x_714, x_777, x_702);
x_779 = l_Lean_Environment_getModuleIdx_x3f(x_778, x_171);
if (lean_obj_tag(x_779) == 1)
{
lean_object* x_780; lean_object* x_781; uint8_t x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; 
lean_dec(x_776);
lean_dec(x_171);
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
lean_dec_ref(x_779);
x_781 = l_Lean_postponedCompileDeclsExt;
x_782 = 0;
x_783 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_781, x_778, x_780, x_782);
x_784 = lean_unsigned_to_nat(0u);
x_785 = lean_array_get_size(x_783);
x_786 = lean_nat_dec_lt(x_784, x_785);
if (x_786 == 0)
{
lean_dec_ref(x_783);
x_643 = x_180;
x_644 = x_677;
x_645 = x_782;
x_646 = x_780;
x_647 = x_702;
x_648 = x_784;
x_649 = lean_box(0);
x_650 = x_781;
x_651 = x_778;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_787; 
x_787 = lean_nat_dec_le(x_785, x_785);
if (x_787 == 0)
{
if (x_786 == 0)
{
lean_dec_ref(x_783);
x_643 = x_180;
x_644 = x_677;
x_645 = x_782;
x_646 = x_780;
x_647 = x_702;
x_648 = x_784;
x_649 = lean_box(0);
x_650 = x_781;
x_651 = x_778;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_788; size_t x_789; lean_object* x_790; 
x_788 = 0;
x_789 = lean_usize_of_nat(x_785);
x_790 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_783, x_788, x_789, x_180);
lean_dec_ref(x_783);
x_643 = x_180;
x_644 = x_677;
x_645 = x_782;
x_646 = x_780;
x_647 = x_702;
x_648 = x_784;
x_649 = lean_box(0);
x_650 = x_781;
x_651 = x_778;
x_652 = x_790;
goto block_666;
}
}
else
{
size_t x_791; size_t x_792; lean_object* x_793; 
x_791 = 0;
x_792 = lean_usize_of_nat(x_785);
x_793 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_783, x_791, x_792, x_180);
lean_dec_ref(x_783);
x_643 = x_180;
x_644 = x_677;
x_645 = x_782;
x_646 = x_780;
x_647 = x_702;
x_648 = x_784;
x_649 = lean_box(0);
x_650 = x_781;
x_651 = x_778;
x_652 = x_793;
goto block_666;
}
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_794 = ((lean_object*)(l_main___closed__26));
x_795 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_796 = lean_string_append(x_794, x_795);
lean_dec_ref(x_795);
x_797 = ((lean_object*)(l_main___closed__27));
x_798 = lean_string_append(x_796, x_797);
x_799 = lean_mk_io_user_error(x_798);
if (lean_is_scalar(x_776)) {
 x_800 = lean_alloc_ctor(1, 1, 0);
} else {
 x_800 = x_776;
 lean_ctor_set_tag(x_800, 1);
}
lean_ctor_set(x_800, 0, x_799);
return x_800;
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec_ref(x_772);
lean_dec_ref(x_714);
lean_dec_ref(x_711);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_801 = lean_ctor_get(x_774, 0);
lean_inc(x_801);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_802 = x_774;
} else {
 lean_dec_ref(x_774);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(1, 1, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_801);
return x_803;
}
}
}
else
{
uint8_t x_804; 
lean_free_object(x_704);
lean_dec_ref(x_706);
lean_dec_ref(x_703);
lean_dec_ref(x_699);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_804 = !lean_is_exclusive(x_708);
if (x_804 == 0)
{
return x_708;
}
else
{
lean_object* x_805; lean_object* x_806; 
x_805 = lean_ctor_get(x_708, 0);
lean_inc(x_805);
lean_dec(x_708);
x_806 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_806, 0, x_805);
return x_806;
}
}
}
else
{
lean_object* x_807; lean_object* x_808; 
x_807 = lean_ctor_get(x_704, 0);
lean_inc(x_807);
lean_dec(x_704);
lean_inc_ref(x_703);
lean_ctor_set(x_695, 1, x_692);
lean_ctor_set(x_695, 0, x_703);
lean_inc_ref(x_807);
x_808 = lean_apply_3(x_700, x_807, x_695, lean_box(0));
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
lean_dec_ref(x_808);
x_810 = l_Lean_classExtension;
x_811 = lean_ctor_get(x_810, 0);
lean_inc_ref(x_811);
x_812 = lean_ctor_get(x_810, 2);
lean_inc_ref(x_812);
x_813 = lean_ctor_get(x_811, 2);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_807);
lean_ctor_set(x_814, 1, x_809);
x_815 = l_Lean_EnvExtension_setState___redArg(x_699, x_703, x_814, x_702);
lean_inc_ref(x_815);
x_816 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_179, x_811, x_815, x_813, x_677);
x_817 = lean_ctor_get(x_816, 0);
lean_inc_ref(x_817);
if (lean_is_exclusive(x_816)) {
 lean_ctor_release(x_816, 0);
 lean_ctor_release(x_816, 1);
 x_818 = x_816;
} else {
 lean_dec_ref(x_816);
 x_818 = lean_box(0);
}
lean_inc_ref(x_815);
if (lean_is_scalar(x_28)) {
 x_819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_819 = x_28;
 lean_ctor_set_tag(x_819, 0);
}
lean_ctor_set(x_819, 0, x_815);
lean_ctor_set(x_819, 1, x_692);
lean_inc_ref(x_817);
x_820 = lean_apply_3(x_812, x_817, x_819, lean_box(0));
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
if (lean_is_exclusive(x_820)) {
 lean_ctor_release(x_820, 0);
 x_822 = x_820;
} else {
 lean_dec_ref(x_820);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_823 = x_818;
}
lean_ctor_set(x_823, 0, x_817);
lean_ctor_set(x_823, 1, x_821);
x_824 = l_Lean_EnvExtension_setState___redArg(x_811, x_815, x_823, x_702);
x_825 = l_Lean_Environment_getModuleIdx_x3f(x_824, x_171);
if (lean_obj_tag(x_825) == 1)
{
lean_object* x_826; lean_object* x_827; uint8_t x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; 
lean_dec(x_822);
lean_dec(x_171);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
lean_dec_ref(x_825);
x_827 = l_Lean_postponedCompileDeclsExt;
x_828 = 0;
x_829 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_827, x_824, x_826, x_828);
x_830 = lean_unsigned_to_nat(0u);
x_831 = lean_array_get_size(x_829);
x_832 = lean_nat_dec_lt(x_830, x_831);
if (x_832 == 0)
{
lean_dec_ref(x_829);
x_643 = x_180;
x_644 = x_677;
x_645 = x_828;
x_646 = x_826;
x_647 = x_702;
x_648 = x_830;
x_649 = lean_box(0);
x_650 = x_827;
x_651 = x_824;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_833; 
x_833 = lean_nat_dec_le(x_831, x_831);
if (x_833 == 0)
{
if (x_832 == 0)
{
lean_dec_ref(x_829);
x_643 = x_180;
x_644 = x_677;
x_645 = x_828;
x_646 = x_826;
x_647 = x_702;
x_648 = x_830;
x_649 = lean_box(0);
x_650 = x_827;
x_651 = x_824;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_834; size_t x_835; lean_object* x_836; 
x_834 = 0;
x_835 = lean_usize_of_nat(x_831);
x_836 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_829, x_834, x_835, x_180);
lean_dec_ref(x_829);
x_643 = x_180;
x_644 = x_677;
x_645 = x_828;
x_646 = x_826;
x_647 = x_702;
x_648 = x_830;
x_649 = lean_box(0);
x_650 = x_827;
x_651 = x_824;
x_652 = x_836;
goto block_666;
}
}
else
{
size_t x_837; size_t x_838; lean_object* x_839; 
x_837 = 0;
x_838 = lean_usize_of_nat(x_831);
x_839 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_829, x_837, x_838, x_180);
lean_dec_ref(x_829);
x_643 = x_180;
x_644 = x_677;
x_645 = x_828;
x_646 = x_826;
x_647 = x_702;
x_648 = x_830;
x_649 = lean_box(0);
x_650 = x_827;
x_651 = x_824;
x_652 = x_839;
goto block_666;
}
}
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_825);
lean_dec_ref(x_824);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_840 = ((lean_object*)(l_main___closed__26));
x_841 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_842 = lean_string_append(x_840, x_841);
lean_dec_ref(x_841);
x_843 = ((lean_object*)(l_main___closed__27));
x_844 = lean_string_append(x_842, x_843);
x_845 = lean_mk_io_user_error(x_844);
if (lean_is_scalar(x_822)) {
 x_846 = lean_alloc_ctor(1, 1, 0);
} else {
 x_846 = x_822;
 lean_ctor_set_tag(x_846, 1);
}
lean_ctor_set(x_846, 0, x_845);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_818);
lean_dec_ref(x_817);
lean_dec_ref(x_815);
lean_dec_ref(x_811);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_847 = lean_ctor_get(x_820, 0);
lean_inc(x_847);
if (lean_is_exclusive(x_820)) {
 lean_ctor_release(x_820, 0);
 x_848 = x_820;
} else {
 lean_dec_ref(x_820);
 x_848 = lean_box(0);
}
if (lean_is_scalar(x_848)) {
 x_849 = lean_alloc_ctor(1, 1, 0);
} else {
 x_849 = x_848;
}
lean_ctor_set(x_849, 0, x_847);
return x_849;
}
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
lean_dec_ref(x_807);
lean_dec_ref(x_703);
lean_dec_ref(x_699);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_850 = lean_ctor_get(x_808, 0);
lean_inc(x_850);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 x_851 = x_808;
} else {
 lean_dec_ref(x_808);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(1, 1, 0);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_850);
return x_852;
}
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_853 = lean_ctor_get(x_695, 1);
lean_inc(x_853);
lean_dec(x_695);
x_854 = lean_ctor_get(x_853, 0);
lean_inc_ref(x_854);
x_855 = lean_ctor_get(x_853, 2);
lean_inc_ref(x_855);
lean_dec_ref(x_853);
x_856 = lean_ctor_get(x_854, 2);
lean_ctor_set(x_688, 1, x_694);
x_857 = lean_box(0);
x_858 = l_Lean_EnvExtension_setState___redArg(x_684, x_687, x_688, x_857);
lean_inc_ref(x_858);
x_859 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_177, x_854, x_858, x_856, x_677);
x_860 = lean_ctor_get(x_859, 0);
lean_inc_ref(x_860);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 lean_ctor_release(x_859, 1);
 x_861 = x_859;
} else {
 lean_dec_ref(x_859);
 x_861 = lean_box(0);
}
lean_inc_ref(x_858);
x_862 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_862, 0, x_858);
lean_ctor_set(x_862, 1, x_692);
lean_inc_ref(x_860);
x_863 = lean_apply_3(x_855, x_860, x_862, lean_box(0));
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
lean_dec_ref(x_863);
x_865 = l_Lean_classExtension;
x_866 = lean_ctor_get(x_865, 0);
lean_inc_ref(x_866);
x_867 = lean_ctor_get(x_865, 2);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_866, 2);
if (lean_is_scalar(x_861)) {
 x_869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_869 = x_861;
}
lean_ctor_set(x_869, 0, x_860);
lean_ctor_set(x_869, 1, x_864);
x_870 = l_Lean_EnvExtension_setState___redArg(x_854, x_858, x_869, x_857);
lean_inc_ref(x_870);
x_871 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_179, x_866, x_870, x_868, x_677);
x_872 = lean_ctor_get(x_871, 0);
lean_inc_ref(x_872);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_873 = x_871;
} else {
 lean_dec_ref(x_871);
 x_873 = lean_box(0);
}
lean_inc_ref(x_870);
if (lean_is_scalar(x_28)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_28;
 lean_ctor_set_tag(x_874, 0);
}
lean_ctor_set(x_874, 0, x_870);
lean_ctor_set(x_874, 1, x_692);
lean_inc_ref(x_872);
x_875 = lean_apply_3(x_867, x_872, x_874, lean_box(0));
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 x_877 = x_875;
} else {
 lean_dec_ref(x_875);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_873;
}
lean_ctor_set(x_878, 0, x_872);
lean_ctor_set(x_878, 1, x_876);
x_879 = l_Lean_EnvExtension_setState___redArg(x_866, x_870, x_878, x_857);
x_880 = l_Lean_Environment_getModuleIdx_x3f(x_879, x_171);
if (lean_obj_tag(x_880) == 1)
{
lean_object* x_881; lean_object* x_882; uint8_t x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; uint8_t x_887; 
lean_dec(x_877);
lean_dec(x_171);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
lean_dec_ref(x_880);
x_882 = l_Lean_postponedCompileDeclsExt;
x_883 = 0;
x_884 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_882, x_879, x_881, x_883);
x_885 = lean_unsigned_to_nat(0u);
x_886 = lean_array_get_size(x_884);
x_887 = lean_nat_dec_lt(x_885, x_886);
if (x_887 == 0)
{
lean_dec_ref(x_884);
x_643 = x_180;
x_644 = x_677;
x_645 = x_883;
x_646 = x_881;
x_647 = x_857;
x_648 = x_885;
x_649 = lean_box(0);
x_650 = x_882;
x_651 = x_879;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_888; 
x_888 = lean_nat_dec_le(x_886, x_886);
if (x_888 == 0)
{
if (x_887 == 0)
{
lean_dec_ref(x_884);
x_643 = x_180;
x_644 = x_677;
x_645 = x_883;
x_646 = x_881;
x_647 = x_857;
x_648 = x_885;
x_649 = lean_box(0);
x_650 = x_882;
x_651 = x_879;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_889; size_t x_890; lean_object* x_891; 
x_889 = 0;
x_890 = lean_usize_of_nat(x_886);
x_891 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_884, x_889, x_890, x_180);
lean_dec_ref(x_884);
x_643 = x_180;
x_644 = x_677;
x_645 = x_883;
x_646 = x_881;
x_647 = x_857;
x_648 = x_885;
x_649 = lean_box(0);
x_650 = x_882;
x_651 = x_879;
x_652 = x_891;
goto block_666;
}
}
else
{
size_t x_892; size_t x_893; lean_object* x_894; 
x_892 = 0;
x_893 = lean_usize_of_nat(x_886);
x_894 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_884, x_892, x_893, x_180);
lean_dec_ref(x_884);
x_643 = x_180;
x_644 = x_677;
x_645 = x_883;
x_646 = x_881;
x_647 = x_857;
x_648 = x_885;
x_649 = lean_box(0);
x_650 = x_882;
x_651 = x_879;
x_652 = x_894;
goto block_666;
}
}
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_880);
lean_dec_ref(x_879);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_895 = ((lean_object*)(l_main___closed__26));
x_896 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_897 = lean_string_append(x_895, x_896);
lean_dec_ref(x_896);
x_898 = ((lean_object*)(l_main___closed__27));
x_899 = lean_string_append(x_897, x_898);
x_900 = lean_mk_io_user_error(x_899);
if (lean_is_scalar(x_877)) {
 x_901 = lean_alloc_ctor(1, 1, 0);
} else {
 x_901 = x_877;
 lean_ctor_set_tag(x_901, 1);
}
lean_ctor_set(x_901, 0, x_900);
return x_901;
}
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec_ref(x_870);
lean_dec_ref(x_866);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_902 = lean_ctor_get(x_875, 0);
lean_inc(x_902);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 x_903 = x_875;
} else {
 lean_dec_ref(x_875);
 x_903 = lean_box(0);
}
if (lean_is_scalar(x_903)) {
 x_904 = lean_alloc_ctor(1, 1, 0);
} else {
 x_904 = x_903;
}
lean_ctor_set(x_904, 0, x_902);
return x_904;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_861);
lean_dec_ref(x_860);
lean_dec_ref(x_858);
lean_dec_ref(x_854);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_905 = lean_ctor_get(x_863, 0);
lean_inc(x_905);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 x_906 = x_863;
} else {
 lean_dec_ref(x_863);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(1, 1, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_905);
return x_907;
}
}
}
else
{
uint8_t x_908; 
lean_free_object(x_688);
lean_dec_ref(x_690);
lean_dec_ref(x_687);
lean_dec_ref(x_684);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_908 = !lean_is_exclusive(x_693);
if (x_908 == 0)
{
return x_693;
}
else
{
lean_object* x_909; lean_object* x_910; 
x_909 = lean_ctor_get(x_693, 0);
lean_inc(x_909);
lean_dec(x_693);
x_910 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_910, 0, x_909);
return x_910;
}
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_688, 0);
lean_inc(x_911);
lean_dec(x_688);
x_912 = l_Lean_Options_empty;
lean_inc_ref(x_687);
lean_ctor_set(x_680, 1, x_912);
lean_ctor_set(x_680, 0, x_687);
lean_inc_ref(x_911);
x_913 = lean_apply_3(x_685, x_911, x_680, lean_box(0));
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
lean_dec_ref(x_913);
x_915 = l_Lean_Meta_instanceExtension;
x_916 = lean_ctor_get(x_915, 1);
lean_inc_ref(x_916);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_917 = x_915;
} else {
 lean_dec_ref(x_915);
 x_917 = lean_box(0);
}
x_918 = lean_ctor_get(x_916, 0);
lean_inc_ref(x_918);
x_919 = lean_ctor_get(x_916, 2);
lean_inc_ref(x_919);
lean_dec_ref(x_916);
x_920 = lean_ctor_get(x_918, 2);
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_911);
lean_ctor_set(x_921, 1, x_914);
x_922 = lean_box(0);
x_923 = l_Lean_EnvExtension_setState___redArg(x_684, x_687, x_921, x_922);
lean_inc_ref(x_923);
x_924 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_177, x_918, x_923, x_920, x_677);
x_925 = lean_ctor_get(x_924, 0);
lean_inc_ref(x_925);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_926 = x_924;
} else {
 lean_dec_ref(x_924);
 x_926 = lean_box(0);
}
lean_inc_ref(x_923);
if (lean_is_scalar(x_917)) {
 x_927 = lean_alloc_ctor(0, 2, 0);
} else {
 x_927 = x_917;
}
lean_ctor_set(x_927, 0, x_923);
lean_ctor_set(x_927, 1, x_912);
lean_inc_ref(x_925);
x_928 = lean_apply_3(x_919, x_925, x_927, lean_box(0));
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
lean_dec_ref(x_928);
x_930 = l_Lean_classExtension;
x_931 = lean_ctor_get(x_930, 0);
lean_inc_ref(x_931);
x_932 = lean_ctor_get(x_930, 2);
lean_inc_ref(x_932);
x_933 = lean_ctor_get(x_931, 2);
if (lean_is_scalar(x_926)) {
 x_934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_934 = x_926;
}
lean_ctor_set(x_934, 0, x_925);
lean_ctor_set(x_934, 1, x_929);
x_935 = l_Lean_EnvExtension_setState___redArg(x_918, x_923, x_934, x_922);
lean_inc_ref(x_935);
x_936 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_179, x_931, x_935, x_933, x_677);
x_937 = lean_ctor_get(x_936, 0);
lean_inc_ref(x_937);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 x_938 = x_936;
} else {
 lean_dec_ref(x_936);
 x_938 = lean_box(0);
}
lean_inc_ref(x_935);
if (lean_is_scalar(x_28)) {
 x_939 = lean_alloc_ctor(0, 2, 0);
} else {
 x_939 = x_28;
 lean_ctor_set_tag(x_939, 0);
}
lean_ctor_set(x_939, 0, x_935);
lean_ctor_set(x_939, 1, x_912);
lean_inc_ref(x_937);
x_940 = lean_apply_3(x_932, x_937, x_939, lean_box(0));
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 x_942 = x_940;
} else {
 lean_dec_ref(x_940);
 x_942 = lean_box(0);
}
if (lean_is_scalar(x_938)) {
 x_943 = lean_alloc_ctor(0, 2, 0);
} else {
 x_943 = x_938;
}
lean_ctor_set(x_943, 0, x_937);
lean_ctor_set(x_943, 1, x_941);
x_944 = l_Lean_EnvExtension_setState___redArg(x_931, x_935, x_943, x_922);
x_945 = l_Lean_Environment_getModuleIdx_x3f(x_944, x_171);
if (lean_obj_tag(x_945) == 1)
{
lean_object* x_946; lean_object* x_947; uint8_t x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; uint8_t x_952; 
lean_dec(x_942);
lean_dec(x_171);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
lean_dec_ref(x_945);
x_947 = l_Lean_postponedCompileDeclsExt;
x_948 = 0;
x_949 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_947, x_944, x_946, x_948);
x_950 = lean_unsigned_to_nat(0u);
x_951 = lean_array_get_size(x_949);
x_952 = lean_nat_dec_lt(x_950, x_951);
if (x_952 == 0)
{
lean_dec_ref(x_949);
x_643 = x_180;
x_644 = x_677;
x_645 = x_948;
x_646 = x_946;
x_647 = x_922;
x_648 = x_950;
x_649 = lean_box(0);
x_650 = x_947;
x_651 = x_944;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_953; 
x_953 = lean_nat_dec_le(x_951, x_951);
if (x_953 == 0)
{
if (x_952 == 0)
{
lean_dec_ref(x_949);
x_643 = x_180;
x_644 = x_677;
x_645 = x_948;
x_646 = x_946;
x_647 = x_922;
x_648 = x_950;
x_649 = lean_box(0);
x_650 = x_947;
x_651 = x_944;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_954; size_t x_955; lean_object* x_956; 
x_954 = 0;
x_955 = lean_usize_of_nat(x_951);
x_956 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_949, x_954, x_955, x_180);
lean_dec_ref(x_949);
x_643 = x_180;
x_644 = x_677;
x_645 = x_948;
x_646 = x_946;
x_647 = x_922;
x_648 = x_950;
x_649 = lean_box(0);
x_650 = x_947;
x_651 = x_944;
x_652 = x_956;
goto block_666;
}
}
else
{
size_t x_957; size_t x_958; lean_object* x_959; 
x_957 = 0;
x_958 = lean_usize_of_nat(x_951);
x_959 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_949, x_957, x_958, x_180);
lean_dec_ref(x_949);
x_643 = x_180;
x_644 = x_677;
x_645 = x_948;
x_646 = x_946;
x_647 = x_922;
x_648 = x_950;
x_649 = lean_box(0);
x_650 = x_947;
x_651 = x_944;
x_652 = x_959;
goto block_666;
}
}
}
else
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_945);
lean_dec_ref(x_944);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_960 = ((lean_object*)(l_main___closed__26));
x_961 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_962 = lean_string_append(x_960, x_961);
lean_dec_ref(x_961);
x_963 = ((lean_object*)(l_main___closed__27));
x_964 = lean_string_append(x_962, x_963);
x_965 = lean_mk_io_user_error(x_964);
if (lean_is_scalar(x_942)) {
 x_966 = lean_alloc_ctor(1, 1, 0);
} else {
 x_966 = x_942;
 lean_ctor_set_tag(x_966, 1);
}
lean_ctor_set(x_966, 0, x_965);
return x_966;
}
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; 
lean_dec(x_938);
lean_dec_ref(x_937);
lean_dec_ref(x_935);
lean_dec_ref(x_931);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_967 = lean_ctor_get(x_940, 0);
lean_inc(x_967);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 x_968 = x_940;
} else {
 lean_dec_ref(x_940);
 x_968 = lean_box(0);
}
if (lean_is_scalar(x_968)) {
 x_969 = lean_alloc_ctor(1, 1, 0);
} else {
 x_969 = x_968;
}
lean_ctor_set(x_969, 0, x_967);
return x_969;
}
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec(x_926);
lean_dec_ref(x_925);
lean_dec_ref(x_923);
lean_dec_ref(x_918);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_970 = lean_ctor_get(x_928, 0);
lean_inc(x_970);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 x_971 = x_928;
} else {
 lean_dec_ref(x_928);
 x_971 = lean_box(0);
}
if (lean_is_scalar(x_971)) {
 x_972 = lean_alloc_ctor(1, 1, 0);
} else {
 x_972 = x_971;
}
lean_ctor_set(x_972, 0, x_970);
return x_972;
}
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec_ref(x_911);
lean_dec_ref(x_687);
lean_dec_ref(x_684);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_973 = lean_ctor_get(x_913, 0);
lean_inc(x_973);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 x_974 = x_913;
} else {
 lean_dec_ref(x_913);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 1, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_973);
return x_975;
}
}
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_976 = lean_ctor_get(x_680, 1);
lean_inc(x_976);
lean_dec(x_680);
x_977 = lean_ctor_get(x_976, 0);
lean_inc_ref(x_977);
x_978 = lean_ctor_get(x_976, 2);
lean_inc_ref(x_978);
lean_dec_ref(x_976);
x_979 = lean_ctor_get(x_977, 2);
lean_inc(x_171);
x_980 = l_Lean_Environment_setMainModule(x_679, x_171);
lean_inc_ref(x_980);
x_981 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_177, x_977, x_980, x_979, x_677);
x_982 = lean_ctor_get(x_981, 0);
lean_inc_ref(x_982);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_983 = x_981;
} else {
 lean_dec_ref(x_981);
 x_983 = lean_box(0);
}
x_984 = l_Lean_Options_empty;
lean_inc_ref(x_980);
x_985 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_985, 0, x_980);
lean_ctor_set(x_985, 1, x_984);
lean_inc_ref(x_982);
x_986 = lean_apply_3(x_978, x_982, x_985, lean_box(0));
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
lean_dec_ref(x_986);
x_988 = l_Lean_Meta_instanceExtension;
x_989 = lean_ctor_get(x_988, 1);
lean_inc_ref(x_989);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_990 = x_988;
} else {
 lean_dec_ref(x_988);
 x_990 = lean_box(0);
}
x_991 = lean_ctor_get(x_989, 0);
lean_inc_ref(x_991);
x_992 = lean_ctor_get(x_989, 2);
lean_inc_ref(x_992);
lean_dec_ref(x_989);
x_993 = lean_ctor_get(x_991, 2);
if (lean_is_scalar(x_983)) {
 x_994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_994 = x_983;
}
lean_ctor_set(x_994, 0, x_982);
lean_ctor_set(x_994, 1, x_987);
x_995 = lean_box(0);
x_996 = l_Lean_EnvExtension_setState___redArg(x_977, x_980, x_994, x_995);
lean_inc_ref(x_996);
x_997 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_177, x_991, x_996, x_993, x_677);
x_998 = lean_ctor_get(x_997, 0);
lean_inc_ref(x_998);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_999 = x_997;
} else {
 lean_dec_ref(x_997);
 x_999 = lean_box(0);
}
lean_inc_ref(x_996);
if (lean_is_scalar(x_990)) {
 x_1000 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1000 = x_990;
}
lean_ctor_set(x_1000, 0, x_996);
lean_ctor_set(x_1000, 1, x_984);
lean_inc_ref(x_998);
x_1001 = lean_apply_3(x_992, x_998, x_1000, lean_box(0));
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
lean_dec_ref(x_1001);
x_1003 = l_Lean_classExtension;
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc_ref(x_1004);
x_1005 = lean_ctor_get(x_1003, 2);
lean_inc_ref(x_1005);
x_1006 = lean_ctor_get(x_1004, 2);
if (lean_is_scalar(x_999)) {
 x_1007 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1007 = x_999;
}
lean_ctor_set(x_1007, 0, x_998);
lean_ctor_set(x_1007, 1, x_1002);
x_1008 = l_Lean_EnvExtension_setState___redArg(x_991, x_996, x_1007, x_995);
lean_inc_ref(x_1008);
x_1009 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_179, x_1004, x_1008, x_1006, x_677);
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc_ref(x_1010);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1011 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1011 = lean_box(0);
}
lean_inc_ref(x_1008);
if (lean_is_scalar(x_28)) {
 x_1012 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1012 = x_28;
 lean_ctor_set_tag(x_1012, 0);
}
lean_ctor_set(x_1012, 0, x_1008);
lean_ctor_set(x_1012, 1, x_984);
lean_inc_ref(x_1010);
x_1013 = lean_apply_3(x_1005, x_1010, x_1012, lean_box(0));
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 x_1015 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1011)) {
 x_1016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1016 = x_1011;
}
lean_ctor_set(x_1016, 0, x_1010);
lean_ctor_set(x_1016, 1, x_1014);
x_1017 = l_Lean_EnvExtension_setState___redArg(x_1004, x_1008, x_1016, x_995);
x_1018 = l_Lean_Environment_getModuleIdx_x3f(x_1017, x_171);
if (lean_obj_tag(x_1018) == 1)
{
lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; uint8_t x_1025; 
lean_dec(x_1015);
lean_dec(x_171);
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
lean_dec_ref(x_1018);
x_1020 = l_Lean_postponedCompileDeclsExt;
x_1021 = 0;
x_1022 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_181, x_1020, x_1017, x_1019, x_1021);
x_1023 = lean_unsigned_to_nat(0u);
x_1024 = lean_array_get_size(x_1022);
x_1025 = lean_nat_dec_lt(x_1023, x_1024);
if (x_1025 == 0)
{
lean_dec_ref(x_1022);
x_643 = x_180;
x_644 = x_677;
x_645 = x_1021;
x_646 = x_1019;
x_647 = x_995;
x_648 = x_1023;
x_649 = lean_box(0);
x_650 = x_1020;
x_651 = x_1017;
x_652 = x_180;
goto block_666;
}
else
{
uint8_t x_1026; 
x_1026 = lean_nat_dec_le(x_1024, x_1024);
if (x_1026 == 0)
{
if (x_1025 == 0)
{
lean_dec_ref(x_1022);
x_643 = x_180;
x_644 = x_677;
x_645 = x_1021;
x_646 = x_1019;
x_647 = x_995;
x_648 = x_1023;
x_649 = lean_box(0);
x_650 = x_1020;
x_651 = x_1017;
x_652 = x_180;
goto block_666;
}
else
{
size_t x_1027; size_t x_1028; lean_object* x_1029; 
x_1027 = 0;
x_1028 = lean_usize_of_nat(x_1024);
x_1029 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_1022, x_1027, x_1028, x_180);
lean_dec_ref(x_1022);
x_643 = x_180;
x_644 = x_677;
x_645 = x_1021;
x_646 = x_1019;
x_647 = x_995;
x_648 = x_1023;
x_649 = lean_box(0);
x_650 = x_1020;
x_651 = x_1017;
x_652 = x_1029;
goto block_666;
}
}
else
{
size_t x_1030; size_t x_1031; lean_object* x_1032; 
x_1030 = 0;
x_1031 = lean_usize_of_nat(x_1024);
x_1032 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(x_1022, x_1030, x_1031, x_180);
lean_dec_ref(x_1022);
x_643 = x_180;
x_644 = x_677;
x_645 = x_1021;
x_646 = x_1019;
x_647 = x_995;
x_648 = x_1023;
x_649 = lean_box(0);
x_650 = x_1020;
x_651 = x_1017;
x_652 = x_1032;
goto block_666;
}
}
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_1018);
lean_dec_ref(x_1017);
lean_dec(x_175);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_1033 = ((lean_object*)(l_main___closed__26));
x_1034 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_171, x_296);
x_1035 = lean_string_append(x_1033, x_1034);
lean_dec_ref(x_1034);
x_1036 = ((lean_object*)(l_main___closed__27));
x_1037 = lean_string_append(x_1035, x_1036);
x_1038 = lean_mk_io_user_error(x_1037);
if (lean_is_scalar(x_1015)) {
 x_1039 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1039 = x_1015;
 lean_ctor_set_tag(x_1039, 1);
}
lean_ctor_set(x_1039, 0, x_1038);
return x_1039;
}
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
lean_dec(x_1011);
lean_dec_ref(x_1010);
lean_dec_ref(x_1008);
lean_dec_ref(x_1004);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_1040 = lean_ctor_get(x_1013, 0);
lean_inc(x_1040);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 x_1041 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1041 = lean_box(0);
}
if (lean_is_scalar(x_1041)) {
 x_1042 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1042 = x_1041;
}
lean_ctor_set(x_1042, 0, x_1040);
return x_1042;
}
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
lean_dec(x_999);
lean_dec_ref(x_998);
lean_dec_ref(x_996);
lean_dec_ref(x_991);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_1043 = lean_ctor_get(x_1001, 0);
lean_inc(x_1043);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 x_1044 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1044 = lean_box(0);
}
if (lean_is_scalar(x_1044)) {
 x_1045 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1045 = x_1044;
}
lean_ctor_set(x_1045, 0, x_1043);
return x_1045;
}
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_983);
lean_dec_ref(x_982);
lean_dec_ref(x_980);
lean_dec_ref(x_977);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_1046 = lean_ctor_get(x_986, 0);
lean_inc(x_1046);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 x_1047 = x_986;
} else {
 lean_dec_ref(x_986);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1046);
return x_1048;
}
}
}
else
{
uint8_t x_1049; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_1049 = !lean_is_exclusive(x_678);
if (x_1049 == 0)
{
return x_678;
}
else
{
lean_object* x_1050; lean_object* x_1051; 
x_1050 = lean_ctor_get(x_678, 0);
lean_inc(x_1050);
lean_dec(x_678);
x_1051 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1051, 0, x_1050);
return x_1051;
}
}
}
}
else
{
uint8_t x_1055; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_1055 = !lean_is_exclusive(x_176);
if (x_1055 == 0)
{
return x_176;
}
else
{
lean_object* x_1056; lean_object* x_1057; 
x_1056 = lean_ctor_get(x_176, 0);
lean_inc(x_1056);
lean_dec(x_176);
x_1057 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1057, 0, x_1056);
return x_1057;
}
}
}
else
{
uint8_t x_1058; 
lean_dec(x_171);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_1058 = !lean_is_exclusive(x_174);
if (x_1058 == 0)
{
return x_174;
}
else
{
lean_object* x_1059; lean_object* x_1060; 
x_1059 = lean_ctor_get(x_174, 0);
lean_inc(x_1059);
lean_dec(x_174);
x_1060 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1060, 0, x_1059);
return x_1060;
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_1061 = !lean_is_exclusive(x_169);
if (x_1061 == 0)
{
return x_169;
}
else
{
lean_object* x_1062; lean_object* x_1063; 
x_1062 = lean_ctor_get(x_169, 0);
lean_inc(x_1062);
lean_dec(x_169);
x_1063 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1063, 0, x_1062);
return x_1063;
}
}
block_134:
{
lean_object* x_36; 
x_36 = l_Lean_addTraceAsMessages___at___00main_spec__6(x_33, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_36);
x_37 = lean_st_ref_get(x_34);
lean_dec(x_34);
x_38 = lean_ctor_get(x_37, 6);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_box(0);
lean_inc_ref(x_40);
x_42 = l_Lean_PersistentArray_forIn___at___00main_spec__8(x_40, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lean_MessageLog_hasErrors(x_38);
lean_dec_ref(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_42);
lean_inc_ref(x_39);
x_46 = l___private_LeanIR_0__mkIRData(x_39);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Environment_mainModule(x_39);
x_49 = ((lean_object*)(l_main___closed__6));
lean_inc(x_48);
x_50 = l_Lean_Name_append(x_48, x_49);
x_51 = l_Lean_saveModuleData(x_27, x_50, x_47);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = 1;
x_53 = lean_io_prim_handle_mk(x_29, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_29);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_IR_emitC(x_39, x_48);
x_56 = l_IO_ofExcept___at___00main_spec__9___redArg(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_string_to_utf8(x_57);
lean_dec(x_57);
x_59 = lean_io_prim_handle_write(x_54, x_58);
lean_dec_ref(x_58);
lean_dec(x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_display_cumulative_profiling_times();
x_63 = l_main___boxed__const__2;
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
x_64 = lean_display_cumulative_profiling_times();
x_65 = l_main___boxed__const__2;
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_54);
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
lean_dec(x_56);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_53);
lean_dec(x_48);
lean_dec_ref(x_39);
x_73 = ((lean_object*)(l_main___closed__7));
x_74 = lean_string_append(x_73, x_29);
lean_dec(x_29);
x_75 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
x_76 = lean_string_append(x_74, x_75);
x_77 = l_IO_eprintln___at___00main_spec__7(x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = l_main___boxed__const__1;
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
x_81 = l_main___boxed__const__1;
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_48);
lean_dec_ref(x_39);
lean_dec(x_29);
x_86 = !lean_is_exclusive(x_51);
if (x_86 == 0)
{
return x_51;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_51, 0);
lean_inc(x_87);
lean_dec(x_51);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec_ref(x_39);
lean_dec(x_29);
lean_dec(x_27);
x_89 = l_main___boxed__const__1;
lean_ctor_set(x_42, 0, x_89);
return x_42;
}
}
else
{
uint8_t x_90; 
lean_dec(x_42);
x_90 = l_Lean_MessageLog_hasErrors(x_38);
lean_dec_ref(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc_ref(x_39);
x_91 = l___private_LeanIR_0__mkIRData(x_39);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_Lean_Environment_mainModule(x_39);
x_94 = ((lean_object*)(l_main___closed__6));
lean_inc(x_93);
x_95 = l_Lean_Name_append(x_93, x_94);
x_96 = l_Lean_saveModuleData(x_27, x_95, x_92);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; lean_object* x_98; 
lean_dec_ref(x_96);
x_97 = 1;
x_98 = lean_io_prim_handle_mk(x_29, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_29);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lean_IR_emitC(x_39, x_93);
x_101 = l_IO_ofExcept___at___00main_spec__9___redArg(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_string_to_utf8(x_102);
lean_dec(x_102);
x_104 = lean_io_prim_handle_write(x_99, x_103);
lean_dec_ref(x_103);
lean_dec(x_99);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_105 = x_104;
} else {
 lean_dec_ref(x_104);
 x_105 = lean_box(0);
}
x_106 = lean_display_cumulative_profiling_times();
x_107 = l_main___boxed__const__2;
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_99);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_113 = x_101;
} else {
 lean_dec_ref(x_101);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_98);
lean_dec(x_93);
lean_dec_ref(x_39);
x_115 = ((lean_object*)(l_main___closed__7));
x_116 = lean_string_append(x_115, x_29);
lean_dec(x_29);
x_117 = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
x_118 = lean_string_append(x_116, x_117);
x_119 = l_IO_eprintln___at___00main_spec__7(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_120 = x_119;
} else {
 lean_dec_ref(x_119);
 x_120 = lean_box(0);
}
x_121 = l_main___boxed__const__1;
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 1, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_93);
lean_dec_ref(x_39);
lean_dec(x_29);
x_126 = lean_ctor_get(x_96, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_127 = x_96;
} else {
 lean_dec_ref(x_96);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_39);
lean_dec(x_29);
lean_dec(x_27);
x_129 = l_main___boxed__const__1;
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_29);
lean_dec(x_27);
x_131 = !lean_is_exclusive(x_42);
if (x_131 == 0)
{
return x_42;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_42, 0);
lean_inc(x_132);
lean_dec(x_42);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
else
{
lean_dec_ref(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_27);
x_15 = lean_box(0);
goto block_18;
}
}
block_144:
{
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Exception_isInterrupt(x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Exception_toMessageData(x_139);
lean_inc_ref(x_136);
x_143 = l_Lean_logError___at___00main_spec__13(x_142, x_136, x_135);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_143);
x_32 = x_135;
x_33 = x_136;
x_34 = x_138;
x_35 = lean_box(0);
goto block_134;
}
else
{
lean_dec_ref(x_143);
lean_dec(x_138);
lean_dec(x_29);
lean_dec(x_27);
x_19 = x_135;
x_20 = x_136;
x_21 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec_ref(x_139);
x_32 = x_135;
x_33 = x_136;
x_34 = x_138;
x_35 = lean_box(0);
goto block_134;
}
}
else
{
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_29);
lean_dec(x_27);
x_19 = x_135;
x_20 = x_136;
x_21 = lean_box(0);
goto block_23;
}
}
block_168:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; 
x_159 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_150);
lean_ctor_set(x_159, 2, x_151);
lean_ctor_set(x_159, 3, x_152);
lean_ctor_set(x_159, 4, x_153);
lean_ctor_set(x_159, 5, x_145);
lean_ctor_set(x_159, 6, x_154);
lean_ctor_set(x_159, 7, x_155);
lean_ctor_set(x_159, 8, x_156);
x_160 = lean_st_ref_set(x_147, x_159);
x_161 = lean_box(0);
x_162 = lean_array_size(x_148);
x_163 = 0;
lean_inc(x_147);
lean_inc_ref(x_146);
x_164 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(x_148, x_162, x_163, x_161, x_146, x_147);
lean_dec_ref(x_148);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
x_32 = x_147;
x_33 = x_146;
x_34 = x_149;
x_35 = lean_box(0);
goto block_134;
}
else
{
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
x_32 = x_147;
x_33 = x_146;
x_34 = x_149;
x_35 = lean_box(0);
goto block_134;
}
else
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = l_Lean_Exception_isInterrupt(x_165);
if (x_166 == 0)
{
uint8_t x_167; 
lean_inc(x_165);
x_167 = l_Lean_Exception_isRuntime(x_165);
x_135 = x_147;
x_136 = x_146;
x_137 = lean_box(0);
x_138 = x_149;
x_139 = x_165;
x_140 = x_167;
goto block_144;
}
else
{
x_135 = x_147;
x_136 = x_146;
x_137 = lean_box(0);
x_138 = x_149;
x_139 = x_165;
x_140 = x_166;
goto block_144;
}
}
}
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_3 = lean_box(0);
goto block_14;
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_1);
x_3 = lean_box(0);
goto block_14;
}
}
else
{
lean_dec(x_1);
x_3 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_main___closed__0));
x_5 = l_IO_println___at___00Lean_Environment_displayStats_spec__1(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = l_main___boxed__const__1;
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_main___boxed__const__1;
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_main___closed__4;
x_17 = l_panic___at___00main_spec__1(x_16);
return x_17;
}
block_23:
{
lean_object* x_22; 
x_22 = l_Lean_addTraceAsMessages___at___00main_spec__6(x_20, x_19);
lean_dec(x_19);
lean_dec_ref(x_22);
x_15 = lean_box(0);
goto block_18;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = _lean_main(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00main_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00main_spec__2___redArg(x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00main_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__9_spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__13(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__15___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27_spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__10_spec__14_spec__27_spec__37___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__17_spec__32_spec__42(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_LeanIR_0__mkIRData___closed__0 = _init_l___private_LeanIR_0__mkIRData___closed__0();
lean_mark_persistent(l___private_LeanIR_0__mkIRData___closed__0);
l___private_LeanIR_0__setConfigOption___closed__3 = _init_l___private_LeanIR_0__setConfigOption___closed__3();
lean_mark_persistent(l___private_LeanIR_0__setConfigOption___closed__3);
l_panic___at___00main_spec__1___closed__0 = _init_l_panic___at___00main_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00main_spec__1___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__8___redArg___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__12___closed__0();
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__6_spec__11_spec__18_spec__34___redArg___closed__0);
l_Lean_addTraceAsMessages___at___00main_spec__6___closed__0 = _init_l_Lean_addTraceAsMessages___at___00main_spec__6___closed__0();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___00main_spec__6___closed__0);
l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1 = _init_l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___00main_spec__6___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___closed__3);
l_main___closed__4 = _init_l_main___closed__4();
lean_mark_persistent(l_main___closed__4);
l_main___closed__10 = _init_l_main___closed__10();
lean_mark_persistent(l_main___closed__10);
l_main___closed__11 = _init_l_main___closed__11();
lean_mark_persistent(l_main___closed__11);
l_main___closed__12 = _init_l_main___closed__12();
lean_mark_persistent(l_main___closed__12);
l_main___closed__13 = _init_l_main___closed__13();
lean_mark_persistent(l_main___closed__13);
l_main___closed__15 = _init_l_main___closed__15();
lean_mark_persistent(l_main___closed__15);
l_main___closed__16 = _init_l_main___closed__16();
lean_mark_persistent(l_main___closed__16);
l_main___closed__17 = _init_l_main___closed__17();
lean_mark_persistent(l_main___closed__17);
l_main___closed__18 = _init_l_main___closed__18();
lean_mark_persistent(l_main___closed__18);
l_main___closed__20 = _init_l_main___closed__20();
lean_mark_persistent(l_main___closed__20);
l_main___closed__21 = _init_l_main___closed__21();
lean_mark_persistent(l_main___closed__21);
l_main___closed__25 = _init_l_main___closed__25();
lean_mark_persistent(l_main___closed__25);
l_main___closed__28 = _init_l_main___closed__28();
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
  #endif
  lean_object* in; lean_object* res;
argv = lean_setup_args(argc, argv);
lean_initialize();
lean_set_panic_messages(false);
res = initialize_LeanIR(1 /* builtin */);
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
in = lean_box(0);
int i = argc;
while (i > 1) {
 lean_object* n;
 i--;
 n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
 in = n;
}
res = _lean_main(in);
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = lean_unbox_uint32(lean_io_result_get_value(res));
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
