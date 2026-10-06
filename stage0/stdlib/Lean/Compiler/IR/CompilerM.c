// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: public import Lean.Compiler.IR.Format public import Lean.Compiler.ExportAttr public import Lean.Compiler.LCNF.PublicDeclsExt import Lean.Compiler.InitAttr import all Lean.Compiler.ModPkgExt import Init.Data.Format.Macro import Lean.Compiler.LCNF.Basic
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
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_get_export_name_for(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_regularInitAttr;
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_LogEntry_fmt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_LogEntry_fmt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__0 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__0_value;
static const lean_string_object l_Lean_IR_LogEntry_fmt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__1 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__1_value;
static lean_once_cell_t l_Lean_IR_LogEntry_fmt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__2;
static lean_once_cell_t l_Lean_IR_LogEntry_fmt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__3;
static const lean_ctor_object l_Lean_IR_LogEntry_fmt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_LogEntry_fmt___closed__0_value)}};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__4 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__4_value;
static const lean_ctor_object l_Lean_IR_LogEntry_fmt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_LogEntry_fmt___closed__1_value)}};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__5 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
static const lean_closure_object l_Lean_IR_LogEntry_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_LogEntry_fmt, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_LogEntry_instToFormat___closed__0 = (const lean_object*)&l_Lean_IR_LogEntry_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_LogEntry_instToFormat = (const lean_object*)&l_Lean_IR_LogEntry_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_log___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_IR_log___closed__0 = (const lean_object*)&l_Lean_IR_log___closed__0_value;
static const lean_string_object l_Lean_IR_log___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l_Lean_IR_log___closed__1 = (const lean_object*)&l_Lean_IR_log___closed__1_value;
static const lean_ctor_object l_Lean_IR_log___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_log___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_IR_log___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_log___closed__2_value_aux_0),((lean_object*)&l_Lean_IR_log___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 183, 71, 31, 86, 224, 207, 192)}};
static const lean_object* l_Lean_IR_log___closed__2 = (const lean_object*)&l_Lean_IR_log___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_tracePrefixOptionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__0 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__0_value;
static const lean_string_object l_Lean_IR_tracePrefixOptionName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__1 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__1_value;
static const lean_string_object l_Lean_IR_tracePrefixOptionName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__2 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__2_value;
static const lean_ctor_object l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_0),((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 121, 176, 5, 201, 231, 94, 72)}};
static const lean_ctor_object l_Lean_IR_tracePrefixOptionName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_1),((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 180, 88, 7, 84, 16, 192, 27)}};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__3 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_IR_tracePrefixOptionName = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 186, 94, 176, 136, 38, 52, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_IR_log___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 220, 115, 150, 240, 139, 111, 12)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 236, 150, 45, 29, 146, 124, 106)}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value;
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_findEnvDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_findEnvDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_getDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown declaration `"};
static const lean_object* l_Lean_IR_getDecl___closed__0 = (const lean_object*)&l_Lean_IR_getDecl___closed__0_value;
static const lean_string_object l_Lean_IR_getDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_IR_getDecl___closed__1 = (const lean_object*)&l_Lean_IR_getDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_addDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_IR_addDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addDecl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value;
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_IR_LogEntry_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_cls_7_; lean_object* v_decls_8_; lean_object* v___x_9_; 
v_cls_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_cls_7_);
v_decls_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_decls_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_cls_7_, v_decls_8_);
return v___x_9_;
}
else
{
lean_object* v_msg_10_; lean_object* v___x_11_; 
v_msg_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_msg_10_);
lean_dec_ref_known(v_t_5_, 1);
v___x_11_ = lean_apply_1(v_k_6_, v_msg_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_IR_LogEntry_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim___redArg(lean_object* v_t_24_, lean_object* v_step_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_24_, v_step_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_step_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_28_, v_step_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim___redArg(lean_object* v_t_32_, lean_object* v_message_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_32_, v_message_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_message_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_36_, v_message_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_LogEntry_fmt_spec__0(lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_nat_to_int(v_a_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(lean_object* v_as_42_, size_t v_i_43_, size_t v_stop_44_, lean_object* v_b_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_usize_dec_eq(v_i_43_, v_stop_44_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; size_t v___x_53_; size_t v___x_54_; 
v___x_47_ = lean_array_uget_borrowed(v_as_42_, v_i_43_);
v___x_48_ = lean_box(1);
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v_b_45_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_47_);
v___x_51_ = l_Lean_IR_formatDecl(v___x_47_, v___x_50_);
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_49_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_add(v_i_43_, v___x_53_);
v_i_43_ = v___x_54_;
v_b_45_ = v___x_52_;
goto _start;
}
else
{
return v_b_45_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_stop_58_, lean_object* v_b_59_){
_start:
{
size_t v_i_boxed_60_; size_t v_stop_boxed_61_; lean_object* v_res_62_; 
v_i_boxed_60_ = lean_unbox_usize(v_i_57_);
lean_dec(v_i_57_);
v_stop_boxed_61_ = lean_unbox_usize(v_stop_58_);
lean_dec(v_stop_58_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_as_56_, v_i_boxed_60_, v_stop_boxed_61_, v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_62_;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__2(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__0));
v___x_66_ = lean_string_length(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__3(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_obj_once(&l_Lean_IR_LogEntry_fmt___closed__2, &l_Lean_IR_LogEntry_fmt___closed__2_once, _init_l_Lean_IR_LogEntry_fmt___closed__2);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v_cls_74_; lean_object* v_decls_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_107_; 
v_cls_74_ = lean_ctor_get(v_x_73_, 0);
v_decls_75_ = lean_ctor_get(v_x_73_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_107_ == 0)
{
v___x_77_ = v_x_73_;
v_isShared_78_ = v_isSharedCheck_107_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_decls_75_);
lean_inc(v_cls_74_);
lean_dec(v_x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_107_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_79_ = 1;
v___x_80_ = l_Lean_Name_toString(v_cls_74_, v___x_79_);
v___x_81_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
v___x_82_ = lean_obj_once(&l_Lean_IR_LogEntry_fmt___closed__3, &l_Lean_IR_LogEntry_fmt___closed__3_once, _init_l_Lean_IR_LogEntry_fmt___closed__3);
v___x_83_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__4));
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 5);
lean_ctor_set(v___x_77_, 1, v___x_81_);
lean_ctor_set(v___x_77_, 0, v___x_83_);
v___x_85_ = v___x_77_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_81_);
v___x_85_ = v_reuseFailAlloc_106_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_86_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__5));
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_82_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_array_get_size(v_decls_75_);
v___x_94_ = lean_nat_dec_lt(v___x_92_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v_decls_75_);
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_90_);
lean_ctor_set(v___x_95_, 1, v___x_91_);
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = lean_nat_dec_le(v___x_93_, v___x_93_);
if (v___x_96_ == 0)
{
if (v___x_94_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v_decls_75_);
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_90_);
lean_ctor_set(v___x_97_, 1, v___x_91_);
return v___x_97_;
}
else
{
size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = ((size_t)0ULL);
v___x_99_ = lean_usize_of_nat(v___x_93_);
v___x_100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_75_, v___x_98_, v___x_99_, v___x_91_);
lean_dec_ref(v_decls_75_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_90_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
return v___x_101_;
}
}
else
{
size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = ((size_t)0ULL);
v___x_103_ = lean_usize_of_nat(v___x_93_);
v___x_104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_75_, v___x_102_, v___x_103_, v___x_91_);
lean_dec_ref(v_decls_75_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_90_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
return v___x_105_;
}
}
}
}
}
else
{
lean_object* v_msg_108_; 
v_msg_108_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_msg_108_);
lean_dec_ref_known(v_x_73_, 1);
return v_msg_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(lean_object* v_as_111_, size_t v_i_112_, size_t v_stop_113_, lean_object* v_b_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = lean_usize_dec_eq(v_i_112_, v_stop_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; size_t v___x_121_; size_t v___x_122_; 
v___x_116_ = lean_array_uget_borrowed(v_as_111_, v_i_112_);
v___x_117_ = lean_box(1);
v___x_118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_118_, 0, v_b_114_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
lean_inc(v___x_116_);
v___x_119_ = l_Lean_IR_LogEntry_fmt(v___x_116_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_add(v_i_112_, v___x_121_);
v_i_112_ = v___x_122_;
v_b_114_ = v___x_120_;
goto _start;
}
else
{
return v_b_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(lean_object* v_as_124_, lean_object* v_i_125_, lean_object* v_stop_126_, lean_object* v_b_127_){
_start:
{
size_t v_i_boxed_128_; size_t v_stop_boxed_129_; lean_object* v_res_130_; 
v_i_boxed_128_ = lean_unbox_usize(v_i_125_);
lean_dec(v_i_125_);
v_stop_boxed_129_ = lean_unbox_usize(v_stop_126_);
lean_dec(v_stop_126_);
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_as_124_, v_i_boxed_128_, v_stop_boxed_129_, v_b_127_);
lean_dec_ref(v_as_124_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object* v_log_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_132_ = lean_box(0);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v_log_131_);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
return v___x_132_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = lean_nat_dec_le(v___x_134_, v___x_134_);
if (v___x_136_ == 0)
{
if (v___x_135_ == 0)
{
return v___x_132_;
}
else
{
size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_134_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_131_, v___x_137_, v___x_138_, v___x_132_);
return v___x_139_;
}
}
else
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_134_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_131_, v___x_140_, v___x_141_, v___x_132_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object* v_log_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_IR_Log_format(v_log_143_);
lean_dec_ref(v_log_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object* v_log_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = l_Lean_IR_Log_format(v_log_145_);
v___x_147_ = l_Std_Format_defWidth;
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_Std_Format_pretty(v___x_146_, v___x_147_, v___x_148_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object* v_log_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_IR_Log_toString(v_log_150_);
lean_dec_ref(v_log_150_);
return v_res_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_ctor_set(v___x_158_, 3, v___x_157_);
lean_ctor_set(v___x_158_, 4, v___x_156_);
lean_ctor_set(v___x_158_, 5, v___x_156_);
lean_ctor_set(v___x_158_, 6, v___x_156_);
lean_ctor_set(v___x_158_, 7, v___x_156_);
lean_ctor_set(v___x_158_, 8, v___x_156_);
lean_ctor_set(v___x_158_, 9, v___x_156_);
lean_ctor_set(v___x_158_, 10, v___x_156_);
lean_ctor_set(v___x_158_, 11, v___x_155_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(32u);
v___x_160_ = lean_mk_empty_array_with_capacity(v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_162_ = ((size_t)5ULL);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_unsigned_to_nat(32u);
v___x_165_ = lean_mk_empty_array_with_capacity(v___x_164_);
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3);
v___x_167_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_163_);
lean_ctor_set(v___x_167_, 3, v___x_163_);
lean_ctor_set_usize(v___x_167_, 4, v___x_162_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_box(1);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4);
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; lean_object* v_toCold_177_; lean_object* v_env_178_; lean_object* v_options_179_; uint8_t v___x_180_; lean_object* v_env_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_toCold_177_ = lean_ctor_get(v___y_173_, 0);
v_env_178_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_178_);
lean_dec(v___x_176_);
v_options_179_ = lean_ctor_get(v_toCold_177_, 2);
v___x_180_ = 0;
v_env_181_ = l_Lean_Environment_setRecordingDeps(v_env_178_, v___x_180_);
v___x_182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_179_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v_env_181_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
lean_ctor_set(v___x_184_, 3, v_options_179_);
v___x_185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_msgData_172_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msgData_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_191_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0(void){
_start:
{
lean_object* v___x_192_; double v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_float_of_nat(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object* v_cls_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_249_; 
v_ref_202_ = lean_ctor_get(v___y_199_, 2);
v___x_203_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_198_, v___y_199_, v___y_200_);
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_249_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_249_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_249_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v_traceState_209_; lean_object* v_env_210_; lean_object* v_nextMacroScope_211_; lean_object* v_ngen_212_; lean_object* v_auxDeclNGen_213_; lean_object* v_cache_214_; lean_object* v_recordedDeps_215_; lean_object* v_messages_216_; lean_object* v_infoState_217_; lean_object* v_snapshotTasks_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_248_; 
v___x_208_ = lean_st_ref_take(v___y_200_);
v_traceState_209_ = lean_ctor_get(v___x_208_, 4);
v_env_210_ = lean_ctor_get(v___x_208_, 0);
v_nextMacroScope_211_ = lean_ctor_get(v___x_208_, 1);
v_ngen_212_ = lean_ctor_get(v___x_208_, 2);
v_auxDeclNGen_213_ = lean_ctor_get(v___x_208_, 3);
v_cache_214_ = lean_ctor_get(v___x_208_, 5);
v_recordedDeps_215_ = lean_ctor_get(v___x_208_, 6);
v_messages_216_ = lean_ctor_get(v___x_208_, 7);
v_infoState_217_ = lean_ctor_get(v___x_208_, 8);
v_snapshotTasks_218_ = lean_ctor_get(v___x_208_, 9);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_248_ == 0)
{
v___x_220_ = v___x_208_;
v_isShared_221_ = v_isSharedCheck_248_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snapshotTasks_218_);
lean_inc(v_infoState_217_);
lean_inc(v_messages_216_);
lean_inc(v_recordedDeps_215_);
lean_inc(v_cache_214_);
lean_inc(v_traceState_209_);
lean_inc(v_auxDeclNGen_213_);
lean_inc(v_ngen_212_);
lean_inc(v_nextMacroScope_211_);
lean_inc(v_env_210_);
lean_dec(v___x_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_248_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint64_t v_tid_222_; lean_object* v_traces_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_247_; 
v_tid_222_ = lean_ctor_get_uint64(v_traceState_209_, sizeof(void*)*1);
v_traces_223_ = lean_ctor_get(v_traceState_209_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_traceState_209_);
if (v_isSharedCheck_247_ == 0)
{
v___x_225_ = v_traceState_209_;
v_isShared_226_ = v_isSharedCheck_247_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_traces_223_);
lean_dec(v_traceState_209_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_247_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; double v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_227_ = lean_box(0);
v___x_228_ = lean_box(0);
v___x_229_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_230_ = 0;
v___x_231_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_232_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_232_, 0, v_cls_197_);
lean_ctor_set(v___x_232_, 1, v___x_228_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
lean_ctor_set_float(v___x_232_, sizeof(void*)*3, v___x_229_);
lean_ctor_set_float(v___x_232_, sizeof(void*)*3 + 8, v___x_229_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*3 + 16, v___x_230_);
v___x_233_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_234_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v_a_204_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
lean_inc(v_ref_202_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_202_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_PersistentArray_push___redArg(v_traces_223_, v___x_235_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_236_);
v___x_238_ = v___x_225_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_236_);
lean_ctor_set_uint64(v_reuseFailAlloc_246_, sizeof(void*)*1, v_tid_222_);
v___x_238_ = v_reuseFailAlloc_246_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 4, v___x_238_);
v___x_240_ = v___x_220_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_env_210_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_nextMacroScope_211_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_ngen_212_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_auxDeclNGen_213_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_245_, 5, v_cache_214_);
lean_ctor_set(v_reuseFailAlloc_245_, 6, v_recordedDeps_215_);
lean_ctor_set(v_reuseFailAlloc_245_, 7, v_messages_216_);
lean_ctor_set(v_reuseFailAlloc_245_, 8, v_infoState_217_);
lean_ctor_set(v_reuseFailAlloc_245_, 9, v_snapshotTasks_218_);
v___x_240_ = v_reuseFailAlloc_245_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_st_ref_put(v___y_200_, v___x_240_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_227_);
v___x_243_ = v___x_206_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_227_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_250_, lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_250_, v_msg_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_266_ = l_Lean_IR_LogEntry_fmt(v_entry_261_);
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
v___x_268_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_265_, v___x_267_, v_a_262_, v_a_263_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_IR_log(v_entry_269_, v_a_270_, v_a_271_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_282_, lean_object* v_optName_283_){
_start:
{
lean_object* v_map_284_; lean_object* v___x_291_; 
v_map_284_ = lean_ctor_get(v_opts_282_, 0);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_284_, v_optName_283_);
if (lean_obj_tag(v___x_291_) == 1)
{
lean_object* v_val_292_; 
v_val_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v___x_291_, 1);
if (lean_obj_tag(v_val_292_) == 1)
{
uint8_t v_v_293_; 
v_v_293_ = lean_ctor_get_uint8(v_val_292_, 0);
lean_dec_ref_known(v_val_292_, 0);
return v_v_293_;
}
else
{
lean_dec(v_val_292_);
goto v___jp_285_;
}
}
else
{
lean_dec(v___x_291_);
goto v___jp_285_;
}
v___jp_285_:
{
lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; 
v___x_286_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_287_ = 0;
v___x_288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_284_, v___x_286_);
if (lean_obj_tag(v___x_288_) == 0)
{
return v___x_287_;
}
else
{
lean_object* v_val_289_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
if (lean_obj_tag(v_val_289_) == 1)
{
uint8_t v_v_290_; 
v_v_290_ = lean_ctor_get_uint8(v_val_289_, 0);
lean_dec_ref_known(v_val_289_, 0);
return v_v_290_;
}
else
{
lean_dec(v_val_289_);
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_294_, lean_object* v_optName_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_294_, v_optName_295_);
lean_dec(v_optName_295_);
lean_dec_ref(v_opts_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_298_, lean_object* v_cls_299_, lean_object* v_decls_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_301_);
v___x_305_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_304_, v_optName_298_);
lean_dec_ref(v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v_decls_300_);
lean_dec(v_cls_299_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_cls_299_);
lean_ctor_set(v___x_308_, 1, v_decls_300_);
v___x_309_ = l_Lean_IR_log(v___x_308_, v_a_301_, v_a_302_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_310_, lean_object* v_cls_311_, lean_object* v_decls_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_310_, v_cls_311_, v_decls_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_optName_310_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_317_, lean_object* v_decl_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_317_);
v___x_323_ = l_Lean_Name_append(v___x_322_, v_cls_317_);
v___x_324_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_323_, v_cls_317_, v_decl_318_, v_a_319_, v_a_320_);
lean_dec(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_325_, lean_object* v_decl_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_IR_logDecls(v_cls_325_, v_decl_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_331_, lean_object* v_optName_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_334_);
v___x_338_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_337_, v_optName_332_);
lean_dec_ref(v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_a_333_);
lean_dec_ref(v_inst_331_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_apply_1(v_inst_331_, v_a_333_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
v___x_343_ = l_Lean_IR_log(v___x_342_, v_a_334_, v_a_335_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_344_, lean_object* v_optName_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_344_, v_optName_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_optName_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_351_, lean_object* v_inst_352_, lean_object* v_optName_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_352_, v_optName_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_359_, lean_object* v_inst_360_, lean_object* v_optName_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_359_, v_inst_360_, v_optName_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_optName_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_367_, lean_object* v_cls_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_374_ = l_Lean_Name_append(v___x_373_, v_cls_368_);
v___x_375_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_367_, v___x_374_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_376_, lean_object* v_cls_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_IR_logMessageIf___redArg(v_inst_376_, v_cls_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_383_, lean_object* v_inst_384_, lean_object* v_cls_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_391_ = l_Lean_Name_append(v___x_390_, v_cls_385_);
v___x_392_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_384_, v___x_391_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_cls_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_IR_logMessageIf(v_00_u03b1_393_, v_inst_394_, v_cls_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_407_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_401_, v___x_406_, v_a_402_, v_a_403_, v_a_404_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_IR_logMessage___redArg(v_inst_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_414_, lean_object* v_inst_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_421_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_415_, v___x_420_, v_a_416_, v_a_417_, v_a_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_422_, lean_object* v_inst_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_IR_logMessage(v_00_u03b1_422_, v_inst_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_429_, lean_object* v_b_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = l_Lean_IR_Decl_name(v_a_429_);
v___x_432_ = l_Lean_IR_Decl_name(v_b_430_);
v___x_433_ = l_Lean_Name_quickLt(v___x_431_, v___x_432_);
lean_dec(v___x_432_);
lean_dec(v___x_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_434_, v_b_435_);
lean_dec_ref(v_b_435_);
lean_dec_ref(v_a_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_array_get_size(v_decls_439_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_nat_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___y_447_; uint8_t v___x_451_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_sub(v___x_440_, v___x_444_);
v___x_451_ = lean_nat_dec_le(v___x_441_, v___x_445_);
if (v___x_451_ == 0)
{
lean_inc(v___x_445_);
v___y_447_ = v___x_445_;
goto v___jp_446_;
}
else
{
v___y_447_ = v___x_441_;
goto v___jp_446_;
}
v___jp_446_:
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_le(v___y_447_, v___x_445_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v___x_445_);
lean_inc(v___y_447_);
v___x_449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_443_, v___x_440_, v_decls_439_, v___y_447_, v___y_447_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_447_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_443_, v___x_440_, v_decls_439_, v___y_447_, v___x_445_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_445_);
return v___x_450_;
}
}
}
else
{
return v_decls_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_455_, lean_object* v_declName_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_array_get_size(v_decls_455_);
v___x_459_ = lean_nat_dec_lt(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_declName_456_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_sub(v___x_458_, v___x_461_);
v___x_463_ = lean_nat_dec_le(v___x_457_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_dec(v___x_462_);
lean_dec(v_declName_456_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_tmpDecl_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_466_ = lean_box(0);
v___x_467_ = lean_box(0);
v_tmpDecl_468_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_468_, 0, v_declName_456_);
lean_ctor_set(v_tmpDecl_468_, 1, v___x_465_);
lean_ctor_set(v_tmpDecl_468_, 2, v___x_466_);
lean_ctor_set(v_tmpDecl_468_, 3, v___x_467_);
v___x_469_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_470_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_471_ = l_Array_binSearchAux___redArg(v___x_469_, v___x_470_, v_decls_455_, v_tmpDecl_468_, v___x_457_, v___x_462_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_472_, lean_object* v_declName_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_472_, v_declName_473_);
lean_dec_ref(v_decls_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_475_, lean_object* v_pivot_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_k_479_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_lt(v_k_479_, v_hi_475_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_k_479_);
v___x_481_ = lean_array_fswap(v_as_477_, v_i_478_, v_hi_475_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_i_478_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_483_ = lean_array_fget_borrowed(v_as_477_, v_k_479_);
v___x_484_ = l_Lean_IR_Decl_name(v___x_483_);
v___x_485_ = l_Lean_IR_Decl_name(v_pivot_476_);
v___x_486_ = l_Lean_Name_quickLt(v___x_484_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v___x_484_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_k_479_, v___x_487_);
lean_dec(v_k_479_);
v_k_479_ = v___x_488_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_array_fswap(v_as_477_, v_i_478_, v_k_479_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_i_478_, v___x_491_);
lean_dec(v_i_478_);
v___x_493_ = lean_nat_add(v_k_479_, v___x_491_);
lean_dec(v_k_479_);
v_as_477_ = v___x_490_;
v_i_478_ = v___x_492_;
v_k_479_ = v___x_493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_495_, lean_object* v_pivot_496_, lean_object* v_as_497_, lean_object* v_i_498_, lean_object* v_k_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_495_, v_pivot_496_, v_as_497_, v_i_498_, v_k_499_);
lean_dec_ref(v_pivot_496_);
lean_dec(v_hi_495_);
return v_res_500_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = l_Lean_IR_Decl_name(v___y_501_);
v___x_504_ = l_Lean_IR_Decl_name(v___y_502_);
v___x_505_ = l_Lean_Name_quickLt(v___x_503_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_506_, v___y_507_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v___y_506_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_510_, lean_object* v_as_511_, lean_object* v_lo_512_, lean_object* v_hi_513_){
_start:
{
lean_object* v___y_515_; uint8_t v___x_525_; 
v___x_525_ = lean_nat_dec_lt(v_lo_512_, v_hi_513_);
if (v___x_525_ == 0)
{
lean_dec(v_lo_512_);
return v_as_511_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_mid_528_; lean_object* v___y_530_; lean_object* v___y_536_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_526_ = lean_nat_add(v_lo_512_, v_hi_513_);
v___x_527_ = lean_unsigned_to_nat(1u);
v_mid_528_ = lean_nat_shiftr(v___x_526_, v___x_527_);
lean_dec(v___x_526_);
v___x_541_ = lean_array_fget_borrowed(v_as_511_, v_mid_528_);
v___x_542_ = lean_array_fget_borrowed(v_as_511_, v_lo_512_);
v___x_543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
v___y_536_ = v_as_511_;
goto v___jp_535_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = lean_array_fswap(v_as_511_, v_lo_512_, v_mid_528_);
v___y_536_ = v___x_544_;
goto v___jp_535_;
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_array_fget_borrowed(v___y_530_, v_mid_528_);
v___x_532_ = lean_array_fget_borrowed(v___y_530_, v_hi_513_);
v___x_533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v_mid_528_);
v___y_515_ = v___y_530_;
goto v___jp_514_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_array_fswap(v___y_530_, v_mid_528_, v_hi_513_);
lean_dec(v_mid_528_);
v___y_515_ = v___x_534_;
goto v___jp_514_;
}
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_537_ = lean_array_fget_borrowed(v___y_536_, v_hi_513_);
v___x_538_ = lean_array_fget_borrowed(v___y_536_, v_lo_512_);
v___x_539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
v___y_530_ = v___y_536_;
goto v___jp_529_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = lean_array_fswap(v___y_536_, v_lo_512_, v_hi_513_);
v___y_530_ = v___x_540_;
goto v___jp_529_;
}
}
}
v___jp_514_:
{
lean_object* v_pivot_516_; lean_object* v___x_517_; lean_object* v_fst_518_; lean_object* v_snd_519_; uint8_t v___x_520_; 
v_pivot_516_ = lean_array_fget(v___y_515_, v_hi_513_);
lean_inc_n(v_lo_512_, 2);
v___x_517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_513_, v_pivot_516_, v___y_515_, v_lo_512_, v_lo_512_);
lean_dec(v_pivot_516_);
v_fst_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_fst_518_);
v_snd_519_ = lean_ctor_get(v___x_517_, 1);
lean_inc(v_snd_519_);
lean_dec_ref(v___x_517_);
v___x_520_ = lean_nat_dec_le(v_hi_513_, v_fst_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_510_, v_snd_519_, v_lo_512_, v_fst_518_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_fst_518_, v___x_522_);
lean_dec(v_fst_518_);
v_as_511_ = v___x_521_;
v_lo_512_ = v___x_523_;
goto _start;
}
else
{
lean_dec(v_fst_518_);
lean_dec(v_lo_512_);
return v_snd_519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_545_, lean_object* v_as_546_, lean_object* v_lo_547_, lean_object* v_hi_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_545_, v_as_546_, v_lo_547_, v_hi_548_);
lean_dec(v_hi_548_);
lean_dec(v_n_545_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_556_, lean_object* v_as_557_, size_t v_i_558_, size_t v_stop_559_, lean_object* v_b_560_){
_start:
{
lean_object* v___y_562_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_558_, v_stop_559_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___y_576_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_574_ = lean_array_uget_borrowed(v_as_557_, v_i_558_);
v___x_591_ = l_Lean_IR_Decl_name(v___x_574_);
lean_inc_ref(v_env_556_);
v___x_592_ = l_Lean_isDeclMeta(v_env_556_, v___x_591_);
if (v___x_592_ == 0)
{
uint8_t v___x_593_; 
lean_inc_ref(v_env_556_);
v___x_593_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_556_, v___x_591_);
if (v___x_593_ == 0)
{
lean_dec(v___x_591_);
v___y_562_ = v_b_560_;
goto v___jp_561_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_591_);
if (v___x_594_ == 0)
{
lean_dec(v___x_591_);
v___y_576_ = v___x_592_;
goto v___jp_575_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_Name_getPrefix(v___x_591_);
lean_dec(v___x_591_);
lean_inc_ref(v_env_556_);
v___x_596_ = l_Lean_isExtern(v_env_556_, v___x_595_);
v___y_576_ = v___x_596_;
goto v___jp_575_;
}
}
}
else
{
lean_object* v___x_597_; 
lean_dec(v___x_591_);
lean_inc(v___x_574_);
v___x_597_ = lean_array_push(v_b_560_, v___x_574_);
v___y_562_ = v___x_597_;
goto v___jp_561_;
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_f_577_; lean_object* v_xs_578_; lean_object* v_type_579_; lean_object* v___x_580_; 
v_f_577_ = lean_ctor_get(v___x_574_, 0);
v_xs_578_ = lean_ctor_get(v___x_574_, 1);
v_type_579_ = lean_ctor_get(v___x_574_, 2);
lean_inc(v_f_577_);
lean_inc_ref(v_env_556_);
v___x_580_ = lean_get_export_name_for(v_env_556_, v_f_577_);
if (lean_obj_tag(v___x_580_) == 1)
{
lean_object* v_val_581_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v___x_580_, 1);
if (lean_obj_tag(v_val_581_) == 1)
{
lean_object* v_str_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_str_582_ = lean_ctor_get(v_val_581_, 1);
lean_inc_ref(v_str_582_);
lean_dec_ref_known(v_val_581_, 2);
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_str_582_);
v___x_585_ = lean_box(0);
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
lean_inc(v_type_579_);
lean_inc_ref(v_xs_578_);
lean_inc(v_f_577_);
v___x_587_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_587_, 0, v_f_577_);
lean_ctor_set(v___x_587_, 1, v_xs_578_);
lean_ctor_set(v___x_587_, 2, v_type_579_);
lean_ctor_set(v___x_587_, 3, v___x_586_);
v___x_588_ = lean_array_push(v_b_560_, v___x_587_);
v___y_562_ = v___x_588_;
goto v___jp_561_;
}
else
{
lean_dec(v_val_581_);
lean_inc_ref(v_xs_578_);
lean_inc(v_f_577_);
lean_inc(v_type_579_);
v___y_567_ = v_type_579_;
v___y_568_ = v_f_577_;
v___y_569_ = v_xs_578_;
goto v___jp_566_;
}
}
else
{
lean_dec(v___x_580_);
lean_inc_ref(v_xs_578_);
lean_inc(v_f_577_);
lean_inc(v_type_579_);
v___y_567_ = v_type_579_;
v___y_568_ = v_f_577_;
v___y_569_ = v_xs_578_;
goto v___jp_566_;
}
}
else
{
lean_object* v___x_589_; 
lean_inc(v___x_574_);
v___x_589_ = lean_array_push(v_b_560_, v___x_574_);
v___y_562_ = v___x_589_;
goto v___jp_561_;
}
}
else
{
lean_object* v___x_590_; 
lean_inc(v___x_574_);
v___x_590_ = lean_array_push(v_b_560_, v___x_574_);
v___y_562_ = v___x_590_;
goto v___jp_561_;
}
}
}
else
{
lean_dec_ref(v_env_556_);
return v_b_560_;
}
v___jp_561_:
{
size_t v___x_563_; size_t v___x_564_; 
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_558_, v___x_563_);
v_i_558_ = v___x_564_;
v_b_560_ = v___y_562_;
goto _start;
}
v___jp_566_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_571_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_571_, 0, v___y_568_);
lean_ctor_set(v___x_571_, 1, v___y_569_);
lean_ctor_set(v___x_571_, 2, v___y_567_);
lean_ctor_set(v___x_571_, 3, v___x_570_);
v___x_572_ = lean_array_push(v_b_560_, v___x_571_);
v___y_562_ = v___x_572_;
goto v___jp_561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_598_, lean_object* v_as_599_, lean_object* v_i_600_, lean_object* v_stop_601_, lean_object* v_b_602_){
_start:
{
size_t v_i_boxed_603_; size_t v_stop_boxed_604_; lean_object* v_res_605_; 
v_i_boxed_603_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_stop_boxed_604_ = lean_unbox_usize(v_stop_601_);
lean_dec(v_stop_601_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_598_, v_as_599_, v_i_boxed_603_, v_stop_boxed_604_, v_b_602_);
lean_dec_ref(v_as_599_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_608_, lean_object* v_as_609_, lean_object* v_start_610_, lean_object* v_stop_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_613_ = lean_nat_dec_lt(v_start_610_, v_stop_611_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_env_608_);
return v___x_612_;
}
else
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_array_get_size(v_as_609_);
v___x_615_ = lean_nat_dec_le(v_stop_611_, v___x_614_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v_start_610_, v___x_614_);
if (v___x_616_ == 0)
{
lean_dec_ref(v_env_608_);
return v___x_612_;
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_usize_of_nat(v_start_610_);
v___x_618_ = lean_usize_of_nat(v___x_614_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_608_, v_as_609_, v___x_617_, v___x_618_, v___x_612_);
return v___x_619_;
}
}
else
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_usize_of_nat(v_start_610_);
v___x_621_ = lean_usize_of_nat(v_stop_611_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_608_, v_as_609_, v___x_620_, v___x_621_, v___x_612_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_623_, lean_object* v_as_624_, lean_object* v_start_625_, lean_object* v_stop_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_623_, v_as_624_, v_start_625_, v_stop_626_);
lean_dec(v_stop_626_);
lean_dec(v_start_625_);
lean_dec_ref(v_as_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
return v_x_628_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v___x_632_; 
v_head_630_ = lean_ctor_get(v_x_629_, 0);
lean_inc(v_head_630_);
v_tail_631_ = lean_ctor_get(v_x_629_, 1);
lean_inc(v_tail_631_);
lean_dec_ref_known(v_x_629_, 2);
v___x_632_ = lean_array_push(v_x_628_, v_head_630_);
v_x_628_ = v___x_632_;
v_x_629_ = v_tail_631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_634_, lean_object* v_s_635_, lean_object* v_entries_636_){
_start:
{
lean_object* v___y_638_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_decls_648_; lean_object* v___x_649_; lean_object* v___y_651_; lean_object* v___y_652_; uint8_t v___x_654_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_648_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_647_, v_entries_636_);
v___x_649_ = lean_array_get_size(v_decls_648_);
v___x_654_ = lean_nat_dec_eq(v___x_649_, v___x_646_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___y_658_; uint8_t v___x_660_; 
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_sub(v___x_649_, v___x_655_);
v___x_660_ = lean_nat_dec_le(v___x_646_, v___x_656_);
if (v___x_660_ == 0)
{
lean_inc(v___x_656_);
v___y_658_ = v___x_656_;
goto v___jp_657_;
}
else
{
v___y_658_ = v___x_646_;
goto v___jp_657_;
}
v___jp_657_:
{
uint8_t v___x_659_; 
v___x_659_ = lean_nat_dec_le(v___y_658_, v___x_656_);
if (v___x_659_ == 0)
{
lean_dec(v___x_656_);
lean_inc(v___y_658_);
v___y_651_ = v___y_658_;
v___y_652_ = v___y_658_;
goto v___jp_650_;
}
else
{
v___y_651_ = v___y_658_;
v___y_652_ = v___x_656_;
goto v___jp_650_;
}
}
}
else
{
v___y_638_ = v_decls_648_;
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v___x_639_; uint8_t v_isModule_640_; 
v___x_639_ = l_Lean_Environment_header(v_env_634_);
v_isModule_640_ = lean_ctor_get_uint8(v___x_639_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_639_);
if (v_isModule_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_env_634_);
lean_inc_ref_n(v___y_638_, 2);
v___x_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_641_, 0, v___y_638_);
lean_ctor_set(v___x_641_, 1, v___y_638_);
lean_ctor_set(v___x_641_, 2, v___y_638_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v___y_638_);
v___x_644_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_634_, v___y_638_, v___x_642_, v___x_643_);
lean_dec_ref(v___y_638_);
lean_inc_ref_n(v___x_644_, 2);
v___x_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_ctor_set(v___x_645_, 2, v___x_644_);
return v___x_645_;
}
}
v___jp_650_:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_649_, v_decls_648_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
v___y_638_ = v___x_653_;
goto v___jp_637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_661_, lean_object* v_s_662_, lean_object* v_entries_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_661_, v_s_662_, v_entries_663_);
lean_dec_ref(v_s_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_array_mk(v_es_665_);
return v___x_666_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object* v_keys_667_, lean_object* v_i_668_, lean_object* v_k_669_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = lean_array_get_size(v_keys_667_);
v___x_671_ = lean_nat_dec_lt(v_i_668_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v_i_668_);
return v___x_671_;
}
else
{
lean_object* v_k_x27_672_; uint8_t v___x_673_; 
v_k_x27_672_ = lean_array_fget_borrowed(v_keys_667_, v_i_668_);
v___x_673_ = lean_name_eq(v_k_669_, v_k_x27_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_i_668_, v___x_674_);
lean_dec(v_i_668_);
v_i_668_ = v___x_675_;
goto _start;
}
else
{
lean_dec(v_i_668_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_677_, lean_object* v_i_678_, lean_object* v_k_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_677_, v_i_678_, v_k_679_);
lean_dec(v_k_679_);
lean_dec_ref(v_keys_677_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_682_, size_t v_x_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
lean_object* v_es_685_; lean_object* v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v_j_689_; lean_object* v___x_690_; 
v_es_685_ = lean_ctor_get(v_x_682_, 0);
v___x_686_ = lean_box(2);
v___x_687_ = ((size_t)31ULL);
v___x_688_ = lean_usize_land(v_x_683_, v___x_687_);
v_j_689_ = lean_usize_to_nat(v___x_688_);
v___x_690_ = lean_array_get_borrowed(v___x_686_, v_es_685_, v_j_689_);
lean_dec(v_j_689_);
switch(lean_obj_tag(v___x_690_))
{
case 0:
{
lean_object* v_key_691_; uint8_t v___x_692_; 
v_key_691_ = lean_ctor_get(v___x_690_, 0);
v___x_692_ = lean_name_eq(v_x_684_, v_key_691_);
return v___x_692_;
}
case 1:
{
lean_object* v_node_693_; size_t v___x_694_; size_t v___x_695_; 
v_node_693_ = lean_ctor_get(v___x_690_, 0);
v___x_694_ = ((size_t)5ULL);
v___x_695_ = lean_usize_shift_right(v_x_683_, v___x_694_);
v_x_682_ = v_node_693_;
v_x_683_ = v___x_695_;
goto _start;
}
default: 
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
}
else
{
lean_object* v_ks_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_ks_698_ = lean_ctor_get(v_x_682_, 0);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_698_, v___x_699_, v_x_684_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
size_t v_x_2165__boxed_704_; uint8_t v_res_705_; lean_object* v_r_706_; 
v_x_2165__boxed_704_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_res_705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_701_, v_x_2165__boxed_704_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_x_701_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
uint64_t v___y_710_; 
if (lean_obj_tag(v_x_708_) == 0)
{
uint64_t v___x_713_; 
v___x_713_ = 1723ULL;
v___y_710_ = v___x_713_;
goto v___jp_709_;
}
else
{
uint64_t v_hash_714_; 
v_hash_714_ = lean_ctor_get_uint64(v_x_708_, sizeof(void*)*2);
v___y_710_ = v_hash_714_;
goto v___jp_709_;
}
v___jp_709_:
{
size_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_uint64_to_usize(v___y_710_);
v___x_712_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_707_, v___x_711_, v_x_708_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_715_, v_x_716_);
lean_dec(v_x_716_);
lean_dec_ref(v_x_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_719_, lean_object* v_x2_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = l_Lean_IR_Decl_name(v_x2_720_);
v___x_722_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_719_, v___x_721_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = 1;
return v___x_723_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_725_, lean_object* v_x2_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_725_, v_x2_726_);
lean_dec_ref(v_x2_726_);
lean_dec_ref(v_x1_725_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_733_);
lean_dec_ref(v_x_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
lean_object* v_ks_739_; lean_object* v_vs_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_764_; 
v_ks_739_ = lean_ctor_get(v_x_735_, 0);
v_vs_740_ = lean_ctor_get(v_x_735_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_735_);
if (v_isSharedCheck_764_ == 0)
{
v___x_742_ = v_x_735_;
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_vs_740_);
lean_inc(v_ks_739_);
lean_dec(v_x_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_array_get_size(v_ks_739_);
v___x_745_ = lean_nat_dec_lt(v_x_736_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec(v_x_736_);
v___x_746_ = lean_array_push(v_ks_739_, v_x_737_);
v___x_747_ = lean_array_push(v_vs_740_, v_x_738_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_747_);
lean_ctor_set(v___x_742_, 0, v___x_746_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v_k_x27_751_; uint8_t v___x_752_; 
v_k_x27_751_ = lean_array_fget_borrowed(v_ks_739_, v_x_736_);
v___x_752_ = lean_name_eq(v_x_737_, v_k_x27_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_754_; 
if (v_isShared_743_ == 0)
{
v___x_754_ = v___x_742_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_ks_739_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_vs_740_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_x_736_, v___x_755_);
lean_dec(v_x_736_);
v_x_735_ = v___x_754_;
v_x_736_ = v___x_756_;
goto _start;
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_759_ = lean_array_fset(v_ks_739_, v_x_736_, v_x_737_);
v___x_760_ = lean_array_fset(v_vs_740_, v_x_736_, v_x_738_);
lean_dec(v_x_736_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_760_);
lean_ctor_set(v___x_742_, 0, v___x_759_);
v___x_762_ = v___x_742_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_765_, lean_object* v_k_766_, lean_object* v_v_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_765_, v___x_768_, v_k_766_, v_v_767_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_771_, size_t v_x_772_, size_t v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_object* v_es_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v_j_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_es_776_ = lean_ctor_get(v_x_771_, 0);
v___x_777_ = ((size_t)31ULL);
v___x_778_ = lean_usize_land(v_x_772_, v___x_777_);
v_j_779_ = lean_usize_to_nat(v___x_778_);
v___x_780_ = lean_array_get_size(v_es_776_);
v___x_781_ = lean_nat_dec_lt(v_j_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v_j_779_);
lean_dec(v_x_775_);
lean_dec(v_x_774_);
return v_x_771_;
}
else
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_820_; 
lean_inc_ref(v_es_776_);
v_isSharedCheck_820_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_x_771_, 0);
lean_dec(v_unused_821_);
v___x_783_ = v_x_771_;
v_isShared_784_ = v_isSharedCheck_820_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_x_771_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_820_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_v_785_; lean_object* v___x_786_; lean_object* v_xs_x27_787_; lean_object* v___y_789_; 
v_v_785_ = lean_array_fget(v_es_776_, v_j_779_);
v___x_786_ = lean_box(0);
v_xs_x27_787_ = lean_array_fset(v_es_776_, v_j_779_, v___x_786_);
switch(lean_obj_tag(v_v_785_))
{
case 0:
{
lean_object* v_key_794_; lean_object* v_val_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_805_; 
v_key_794_ = lean_ctor_get(v_v_785_, 0);
v_val_795_ = lean_ctor_get(v_v_785_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_v_785_);
if (v_isSharedCheck_805_ == 0)
{
v___x_797_ = v_v_785_;
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_val_795_);
lean_inc(v_key_794_);
lean_dec(v_v_785_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
uint8_t v___x_799_; 
v___x_799_ = lean_name_eq(v_x_774_, v_key_794_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_del_object(v___x_797_);
v___x_800_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_794_, v_val_795_, v_x_774_, v_x_775_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___y_789_ = v___x_801_;
goto v___jp_788_;
}
else
{
lean_object* v___x_803_; 
lean_dec(v_val_795_);
lean_dec(v_key_794_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_x_775_);
lean_ctor_set(v___x_797_, 0, v_x_774_);
v___x_803_ = v___x_797_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_x_774_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_x_775_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v___y_789_ = v___x_803_;
goto v___jp_788_;
}
}
}
}
case 1:
{
lean_object* v_node_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
v_node_806_ = lean_ctor_get(v_v_785_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_v_785_);
if (v_isSharedCheck_818_ == 0)
{
v___x_808_ = v_v_785_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_node_806_);
lean_dec(v_v_785_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_810_ = ((size_t)5ULL);
v___x_811_ = lean_usize_shift_right(v_x_772_, v___x_810_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_add(v_x_773_, v___x_812_);
v___x_814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_806_, v___x_811_, v___x_813_, v_x_774_, v_x_775_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_814_);
v___x_816_ = v___x_808_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v___y_789_ = v___x_816_;
goto v___jp_788_;
}
}
}
default: 
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_x_774_);
lean_ctor_set(v___x_819_, 1, v_x_775_);
v___y_789_ = v___x_819_;
goto v___jp_788_;
}
}
v___jp_788_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_array_fset(v_xs_x27_787_, v_j_779_, v___y_789_);
lean_dec(v_j_779_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_790_);
v___x_792_ = v___x_783_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v_ks_822_; lean_object* v_vs_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_841_; 
v_ks_822_ = lean_ctor_get(v_x_771_, 0);
v_vs_823_ = lean_ctor_get(v_x_771_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_841_ == 0)
{
v___x_825_ = v_x_771_;
v_isShared_826_ = v_isSharedCheck_841_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_vs_823_);
lean_inc(v_ks_822_);
lean_dec(v_x_771_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_841_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_ks_822_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_vs_823_);
v___x_828_ = v_reuseFailAlloc_840_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v_newNode_829_; size_t v___x_830_; uint8_t v___x_831_; 
v_newNode_829_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_828_, v_x_774_, v_x_775_);
v___x_830_ = ((size_t)7ULL);
v___x_831_ = lean_usize_dec_le(v___x_830_, v_x_773_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_829_);
v___x_833_ = lean_unsigned_to_nat(4u);
v___x_834_ = lean_nat_dec_lt(v___x_832_, v___x_833_);
lean_dec(v___x_832_);
if (v___x_834_ == 0)
{
lean_object* v_ks_835_; lean_object* v_vs_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_ks_835_ = lean_ctor_get(v_newNode_829_, 0);
lean_inc_ref(v_ks_835_);
v_vs_836_ = lean_ctor_get(v_newNode_829_, 1);
lean_inc_ref(v_vs_836_);
lean_dec_ref(v_newNode_829_);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_773_, v_ks_835_, v_vs_836_, v___x_837_, v___x_838_);
lean_dec_ref(v_vs_836_);
lean_dec_ref(v_ks_835_);
return v___x_839_;
}
else
{
return v_newNode_829_;
}
}
else
{
return v_newNode_829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t v_depth_842_, lean_object* v_keys_843_, lean_object* v_vals_844_, lean_object* v_i_845_, lean_object* v_entries_846_){
_start:
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_array_get_size(v_keys_843_);
v___x_848_ = lean_nat_dec_lt(v_i_845_, v___x_847_);
if (v___x_848_ == 0)
{
lean_dec(v_i_845_);
return v_entries_846_;
}
else
{
lean_object* v_k_849_; lean_object* v_v_850_; uint64_t v___y_852_; 
v_k_849_ = lean_array_fget_borrowed(v_keys_843_, v_i_845_);
v_v_850_ = lean_array_fget_borrowed(v_vals_844_, v_i_845_);
if (lean_obj_tag(v_k_849_) == 0)
{
uint64_t v___x_863_; 
v___x_863_ = 1723ULL;
v___y_852_ = v___x_863_;
goto v___jp_851_;
}
else
{
uint64_t v_hash_864_; 
v_hash_864_ = lean_ctor_get_uint64(v_k_849_, sizeof(void*)*2);
v___y_852_ = v_hash_864_;
goto v___jp_851_;
}
v___jp_851_:
{
size_t v_h_853_; size_t v___x_854_; lean_object* v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v_h_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_h_853_ = lean_uint64_to_usize(v___y_852_);
v___x_854_ = ((size_t)5ULL);
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_sub(v_depth_842_, v___x_856_);
v___x_858_ = lean_usize_mul(v___x_854_, v___x_857_);
v_h_859_ = lean_usize_shift_right(v_h_853_, v___x_858_);
v___x_860_ = lean_nat_add(v_i_845_, v___x_855_);
lean_dec(v_i_845_);
lean_inc(v_v_850_);
lean_inc(v_k_849_);
v___x_861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_846_, v_h_859_, v_depth_842_, v_k_849_, v_v_850_);
v_i_845_ = v___x_860_;
v_entries_846_ = v___x_861_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_865_, lean_object* v_keys_866_, lean_object* v_vals_867_, lean_object* v_i_868_, lean_object* v_entries_869_){
_start:
{
size_t v_depth_boxed_870_; lean_object* v_res_871_; 
v_depth_boxed_870_ = lean_unbox_usize(v_depth_865_);
lean_dec(v_depth_865_);
v_res_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_870_, v_keys_866_, v_vals_867_, v_i_868_, v_entries_869_);
lean_dec_ref(v_vals_867_);
lean_dec_ref(v_keys_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
size_t v_x_2326__boxed_877_; size_t v_x_2327__boxed_878_; lean_object* v_res_879_; 
v_x_2326__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_x_2327__boxed_878_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_872_, v_x_2326__boxed_877_, v_x_2327__boxed_878_, v_x_875_, v_x_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
uint64_t v___y_884_; 
if (lean_obj_tag(v_x_881_) == 0)
{
uint64_t v___x_888_; 
v___x_888_ = 1723ULL;
v___y_884_ = v___x_888_;
goto v___jp_883_;
}
else
{
uint64_t v_hash_889_; 
v_hash_889_ = lean_ctor_get_uint64(v_x_881_, sizeof(void*)*2);
v___y_884_ = v_hash_889_;
goto v___jp_883_;
}
v___jp_883_:
{
size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_uint64_to_usize(v___y_884_);
v___x_886_ = ((size_t)1ULL);
v___x_887_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_880_, v___x_885_, v___x_886_, v_x_881_, v_x_882_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_890_, lean_object* v_d_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = l_Lean_IR_Decl_name(v_d_891_);
v___x_893_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_890_, v___x_892_, v_d_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_923_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_926_, lean_object* v_as_927_, lean_object* v_lo_928_, lean_object* v_hi_929_, lean_object* v_w_930_, lean_object* v_hlo_931_, lean_object* v_hhi_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_926_, v_as_927_, v_lo_928_, v_hi_929_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_934_, lean_object* v_as_935_, lean_object* v_lo_936_, lean_object* v_hi_937_, lean_object* v_w_938_, lean_object* v_hlo_939_, lean_object* v_hhi_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_934_, v_as_935_, v_lo_936_, v_hi_937_, v_w_938_, v_hlo_939_, v_hhi_940_);
lean_dec(v_hi_937_);
lean_dec(v_n_934_);
return v_res_941_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_943_, v_x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_946_, v_x_947_, v_x_948_);
lean_dec(v_x_948_);
lean_dec_ref(v_x_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_952_, v_x_953_, v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_956_, lean_object* v_lo_957_, lean_object* v_hi_958_, lean_object* v_hhi_959_, lean_object* v_pivot_960_, lean_object* v_as_961_, lean_object* v_i_962_, lean_object* v_k_963_, lean_object* v_ilo_964_, lean_object* v_ik_965_, lean_object* v_w_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_958_, v_pivot_960_, v_as_961_, v_i_962_, v_k_963_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_968_, lean_object* v_lo_969_, lean_object* v_hi_970_, lean_object* v_hhi_971_, lean_object* v_pivot_972_, lean_object* v_as_973_, lean_object* v_i_974_, lean_object* v_k_975_, lean_object* v_ilo_976_, lean_object* v_ik_977_, lean_object* v_w_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_968_, v_lo_969_, v_hi_970_, v_hhi_971_, v_pivot_972_, v_as_973_, v_i_974_, v_k_975_, v_ilo_976_, v_ik_977_, v_w_978_);
lean_dec_ref(v_pivot_972_);
lean_dec(v_hi_970_);
lean_dec(v_lo_969_);
lean_dec(v_n_968_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, size_t v_x_982_, lean_object* v_x_983_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_981_, v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
size_t v_x_2611__boxed_989_; uint8_t v_res_990_; lean_object* v_r_991_; 
v_x_2611__boxed_989_ = lean_unbox_usize(v_x_987_);
lean_dec(v_x_987_);
v_res_990_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_985_, v_x_986_, v_x_2611__boxed_989_, v_x_988_);
lean_dec(v_x_988_);
lean_dec_ref(v_x_986_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, size_t v_x_994_, size_t v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_993_, v_x_994_, v_x_995_, v_x_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
size_t v_x_2622__boxed_1005_; size_t v_x_2623__boxed_1006_; lean_object* v_res_1007_; 
v_x_2622__boxed_1005_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_x_2623__boxed_1006_ = lean_unbox_usize(v_x_1002_);
lean_dec(v_x_1002_);
v_res_1007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_999_, v_x_1000_, v_x_2622__boxed_1005_, v_x_2623__boxed_1006_, v_x_1003_, v_x_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1008_, lean_object* v_keys_1009_, lean_object* v_vals_1010_, lean_object* v_heq_1011_, lean_object* v_i_1012_, lean_object* v_k_1013_){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_1009_, v_i_1012_, v_k_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1015_, lean_object* v_keys_1016_, lean_object* v_vals_1017_, lean_object* v_heq_1018_, lean_object* v_i_1019_, lean_object* v_k_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1015_, v_keys_1016_, v_vals_1017_, v_heq_1018_, v_i_1019_, v_k_1020_);
lean_dec(v_k_1020_);
lean_dec_ref(v_vals_1017_);
lean_dec_ref(v_keys_1016_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1023_, lean_object* v_n_1024_, lean_object* v_k_1025_, lean_object* v_v_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1024_, v_k_1025_, v_v_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1028_, size_t v_depth_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_heq_1032_, lean_object* v_i_1033_, lean_object* v_entries_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1029_, v_keys_1030_, v_vals_1031_, v_i_1033_, v_entries_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_depth_1037_, lean_object* v_keys_1038_, lean_object* v_vals_1039_, lean_object* v_heq_1040_, lean_object* v_i_1041_, lean_object* v_entries_1042_){
_start:
{
size_t v_depth_boxed_1043_; lean_object* v_res_1044_; 
v_depth_boxed_1043_ = lean_unbox_usize(v_depth_1037_);
lean_dec(v_depth_1037_);
v_res_1044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1036_, v_depth_boxed_1043_, v_keys_1038_, v_vals_1039_, v_heq_1040_, v_i_1041_, v_entries_1042_);
lean_dec_ref(v_vals_1039_);
lean_dec_ref(v_keys_1038_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1046_, v_x_1047_, v_x_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = lean_array_get_size(v_irDecls_1051_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_nat_dec_eq(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___y_1059_; uint8_t v___x_1063_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_nat_sub(v___x_1052_, v___x_1056_);
v___x_1063_ = lean_nat_dec_le(v___x_1053_, v___x_1057_);
if (v___x_1063_ == 0)
{
lean_inc(v___x_1057_);
v___y_1059_ = v___x_1057_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v___x_1053_;
goto v___jp_1058_;
}
v___jp_1058_:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_le(v___y_1059_, v___x_1057_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v___x_1057_);
lean_inc(v___y_1059_);
v___x_1061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1055_, v___x_1052_, v_irDecls_1051_, v___y_1059_, v___y_1059_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1059_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1055_, v___x_1052_, v_irDecls_1051_, v___y_1059_, v___x_1057_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_1057_);
return v___x_1062_;
}
}
}
else
{
return v_irDecls_1051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1064_){
_start:
{
lean_inc_ref(v_initDecls_1064_);
return v_initDecls_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1065_);
lean_dec_ref(v_initDecls_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1067_){
_start:
{
lean_inc_ref(v_modPkg_1067_);
return v_modPkg_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1068_);
lean_dec_ref(v_modPkg_1068_);
return v_res_1069_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0(void){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v_toEnvExtension_1076_; lean_object* v_name_1077_; lean_object* v_asyncMode_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___y_1083_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_irDecls_1114_; lean_object* v___x_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; uint8_t v___x_1120_; 
v___x_1075_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1076_ = lean_ctor_get(v___x_1075_, 0);
v_name_1077_ = lean_ctor_get(v___x_1075_, 1);
v_asyncMode_1078_ = lean_ctor_get(v_toEnvExtension_1076_, 2);
v___x_1079_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1080_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1081_ = lean_box(0);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1074_);
v___x_1113_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1079_, v___x_1075_, v_env_1074_, v_asyncMode_1078_);
v_irDecls_1114_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1112_, v___x_1113_);
v___x_1115_ = lean_array_get_size(v_irDecls_1114_);
v___x_1120_ = lean_nat_dec_eq(v___x_1115_, v___x_1111_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___y_1124_; uint8_t v___x_1126_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_sub(v___x_1115_, v___x_1121_);
v___x_1126_ = lean_nat_dec_le(v___x_1111_, v___x_1122_);
if (v___x_1126_ == 0)
{
lean_inc(v___x_1122_);
v___y_1124_ = v___x_1122_;
goto v___jp_1123_;
}
else
{
v___y_1124_ = v___x_1111_;
goto v___jp_1123_;
}
v___jp_1123_:
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_nat_dec_le(v___y_1124_, v___x_1122_);
if (v___x_1125_ == 0)
{
lean_dec(v___x_1122_);
lean_inc(v___y_1124_);
v___y_1117_ = v___y_1124_;
v___y_1118_ = v___y_1124_;
goto v___jp_1116_;
}
else
{
v___y_1117_ = v___y_1124_;
v___y_1118_ = v___x_1122_;
goto v___jp_1116_;
}
}
}
else
{
v___y_1083_ = v_irDecls_1114_;
goto v___jp_1082_;
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v_ext_1085_; lean_object* v_toEnvExtension_1086_; lean_object* v_name_1087_; lean_object* v_exportEntriesFn_1088_; lean_object* v_asyncMode_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_private_1094_; lean_object* v___x_1095_; lean_object* v_toEnvExtension_1096_; lean_object* v_name_1097_; lean_object* v_exportEntriesFn_1098_; lean_object* v_asyncMode_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_private_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1084_ = l_Lean_regularInitAttr;
v_ext_1085_ = lean_ctor_get(v___x_1084_, 1);
v_toEnvExtension_1086_ = lean_ctor_get(v_ext_1085_, 0);
v_name_1087_ = lean_ctor_get(v_ext_1085_, 1);
v_exportEntriesFn_1088_ = lean_ctor_get(v_ext_1085_, 4);
v_asyncMode_1089_ = lean_ctor_get(v_toEnvExtension_1086_, 2);
v___x_1090_ = lean_box(0);
v___x_1091_ = 0;
lean_inc_ref_n(v_env_1074_, 3);
v___x_1092_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1080_, v_ext_1085_, v_env_1074_, v_asyncMode_1089_, v___x_1090_, v___x_1091_);
lean_inc_ref(v_exportEntriesFn_1088_);
v___x_1093_ = lean_apply_2(v_exportEntriesFn_1088_, v_env_1074_, v___x_1092_);
v_private_1094_ = lean_ctor_get(v___x_1093_, 2);
lean_inc(v_private_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1096_ = lean_ctor_get(v___x_1095_, 0);
v_name_1097_ = lean_ctor_get(v___x_1095_, 1);
v_exportEntriesFn_1098_ = lean_ctor_get(v___x_1095_, 4);
v_asyncMode_1099_ = lean_ctor_get(v_toEnvExtension_1096_, 2);
v___x_1100_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1081_, v___x_1095_, v_env_1074_, v_asyncMode_1099_, v___x_1090_, v___x_1091_);
lean_inc_ref(v_exportEntriesFn_1098_);
v___x_1101_ = lean_apply_2(v_exportEntriesFn_1098_, v_env_1074_, v___x_1100_);
v_private_1102_ = lean_ctor_get(v___x_1101_, 2);
lean_inc(v_private_1102_);
lean_dec_ref(v___x_1101_);
lean_inc(v_name_1077_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_name_1077_);
lean_ctor_set(v___x_1103_, 1, v___y_1083_);
lean_inc(v_name_1087_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_name_1087_);
lean_ctor_set(v___x_1104_, 1, v_private_1094_);
lean_inc(v_name_1097_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_name_1097_);
lean_ctor_set(v___x_1105_, 1, v_private_1102_);
v___x_1106_ = lean_unsigned_to_nat(3u);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1106_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1103_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1104_);
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1105_);
return v___x_1110_;
}
v___jp_1116_:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1115_, v_irDecls_1114_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
v___y_1083_ = v___x_1119_;
goto v___jp_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1127_, lean_object* v_k_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_m_1133_; lean_object* v_a_1134_; uint8_t v___x_1135_; 
v___x_1131_ = lean_nat_add(v_x_1129_, v_x_1130_);
v___x_1132_ = lean_unsigned_to_nat(1u);
v_m_1133_ = lean_nat_shiftr(v___x_1131_, v___x_1132_);
lean_dec(v___x_1131_);
v_a_1134_ = lean_array_fget_borrowed(v_as_1127_, v_m_1133_);
v___x_1135_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1134_, v_k_1128_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1136_; 
lean_dec(v_x_1130_);
v___x_1136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1128_, v_a_1134_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_dec(v_m_1133_);
lean_dec(v_x_1129_);
lean_inc(v_a_1134_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1134_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v_m_1133_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_nat_sub(v_m_1133_, v___x_1132_);
lean_dec(v_m_1133_);
v___x_1141_ = lean_nat_dec_lt(v___x_1140_, v_x_1129_);
if (v___x_1141_ == 0)
{
v_x_1130_ = v___x_1140_;
goto _start;
}
else
{
lean_object* v___x_1143_; 
lean_dec(v___x_1140_);
lean_dec(v_x_1129_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v_m_1133_);
lean_dec(v_x_1129_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
}
}
else
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
lean_dec(v_x_1129_);
v___x_1145_ = lean_nat_add(v_m_1133_, v___x_1132_);
lean_dec(v_m_1133_);
v___x_1146_ = lean_nat_dec_le(v___x_1145_, v_x_1130_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec(v___x_1145_);
lean_dec(v_x_1130_);
v___x_1147_ = lean_box(0);
return v___x_1147_;
}
else
{
v_x_1129_ = v___x_1145_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1149_, lean_object* v_k_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1149_, v_k_1150_, v_x_1151_, v_x_1152_);
lean_dec_ref(v_k_1150_);
lean_dec_ref(v_as_1149_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1154_, lean_object* v_vals_1155_, lean_object* v_i_1156_, lean_object* v_k_1157_){
_start:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_array_get_size(v_keys_1154_);
v___x_1159_ = lean_nat_dec_lt(v_i_1156_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_i_1156_);
v___x_1160_ = lean_box(0);
return v___x_1160_;
}
else
{
lean_object* v_k_x27_1161_; uint8_t v___x_1162_; 
v_k_x27_1161_ = lean_array_fget_borrowed(v_keys_1154_, v_i_1156_);
v___x_1162_ = lean_name_eq(v_k_1157_, v_k_x27_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1156_, v___x_1163_);
lean_dec(v_i_1156_);
v_i_1156_ = v___x_1164_;
goto _start;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_array_fget_borrowed(v_vals_1155_, v_i_1156_);
lean_dec(v_i_1156_);
lean_inc(v___x_1166_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1168_, lean_object* v_vals_1169_, lean_object* v_i_1170_, lean_object* v_k_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1168_, v_vals_1169_, v_i_1170_, v_k_1171_);
lean_dec(v_k_1171_);
lean_dec_ref(v_vals_1169_);
lean_dec_ref(v_keys_1168_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1173_, size_t v_x_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
lean_object* v_es_1176_; lean_object* v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v_j_1180_; lean_object* v___x_1181_; 
v_es_1176_ = lean_ctor_get(v_x_1173_, 0);
v___x_1177_ = lean_box(2);
v___x_1178_ = ((size_t)31ULL);
v___x_1179_ = lean_usize_land(v_x_1174_, v___x_1178_);
v_j_1180_ = lean_usize_to_nat(v___x_1179_);
v___x_1181_ = lean_array_get_borrowed(v___x_1177_, v_es_1176_, v_j_1180_);
lean_dec(v_j_1180_);
switch(lean_obj_tag(v___x_1181_))
{
case 0:
{
lean_object* v_key_1182_; lean_object* v_val_1183_; uint8_t v___x_1184_; 
v_key_1182_ = lean_ctor_get(v___x_1181_, 0);
v_val_1183_ = lean_ctor_get(v___x_1181_, 1);
v___x_1184_ = lean_name_eq(v_x_1175_, v_key_1182_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_box(0);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; 
lean_inc(v_val_1183_);
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_val_1183_);
return v___x_1186_;
}
}
case 1:
{
lean_object* v_node_1187_; size_t v___x_1188_; size_t v___x_1189_; 
v_node_1187_ = lean_ctor_get(v___x_1181_, 0);
v___x_1188_ = ((size_t)5ULL);
v___x_1189_ = lean_usize_shift_right(v_x_1174_, v___x_1188_);
v_x_1173_ = v_node_1187_;
v_x_1174_ = v___x_1189_;
goto _start;
}
default: 
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
}
}
else
{
lean_object* v_ks_1192_; lean_object* v_vs_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_ks_1192_ = lean_ctor_get(v_x_1173_, 0);
v_vs_1193_ = lean_ctor_get(v_x_1173_, 1);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1192_, v_vs_1193_, v___x_1194_, v_x_1175_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
size_t v_x_422__boxed_1199_; lean_object* v_res_1200_; 
v_x_422__boxed_1199_ = lean_unbox_usize(v_x_1197_);
lean_dec(v_x_1197_);
v_res_1200_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1196_, v_x_422__boxed_1199_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_x_1196_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
uint64_t v___y_1204_; 
if (lean_obj_tag(v_x_1202_) == 0)
{
uint64_t v___x_1207_; 
v___x_1207_ = 1723ULL;
v___y_1204_ = v___x_1207_;
goto v___jp_1203_;
}
else
{
uint64_t v_hash_1208_; 
v_hash_1208_ = lean_ctor_get_uint64(v_x_1202_, sizeof(void*)*2);
v___y_1204_ = v_hash_1208_;
goto v___jp_1203_;
}
v___jp_1203_:
{
size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_uint64_to_usize(v___y_1204_);
v___x_1206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1201_, v___x_1205_, v_x_1202_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1209_, v_x_1210_);
lean_dec(v_x_1210_);
lean_dec_ref(v_x_1209_);
return v_res_1211_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1215_, lean_object* v_declName_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1228_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1219_ = l_Lean_IR_declMapExt;
v___x_1228_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1215_, v_declName_1216_);
if (lean_obj_tag(v___x_1228_) == 0)
{
goto v___jp_1220_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1243_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1218_, v___x_1219_, v_env_1215_, v_val_1229_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_array_get_size(v___x_1243_);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v___x_1243_);
goto v___jp_1230_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_sub(v___x_1245_, v___x_1247_);
v___x_1249_ = lean_nat_dec_le(v___x_1244_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v___x_1248_);
lean_dec_ref(v___x_1243_);
goto v___jp_1230_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_tmpDecl_1252_; lean_object* v___x_1253_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1251_ = lean_box(0);
lean_inc(v_declName_1216_);
v_tmpDecl_1252_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1252_, 0, v_declName_1216_);
lean_ctor_set(v_tmpDecl_1252_, 1, v___x_1250_);
lean_ctor_set(v_tmpDecl_1252_, 2, v___x_1251_);
lean_ctor_set(v_tmpDecl_1252_, 3, v___x_1217_);
v___x_1253_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1243_, v_tmpDecl_1252_, v___x_1244_, v___x_1248_);
lean_dec_ref_known(v_tmpDecl_1252_, 4);
lean_dec_ref(v___x_1243_);
if (lean_obj_tag(v___x_1253_) == 0)
{
goto v___jp_1230_;
}
else
{
lean_dec(v_val_1229_);
lean_dec(v_declName_1216_);
lean_dec_ref(v_env_1215_);
return v___x_1253_;
}
}
}
v___jp_1230_:
{
uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1231_ = 0;
v___x_1232_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1218_, v___x_1219_, v_env_1215_, v_val_1229_, v___x_1231_);
lean_dec(v_val_1229_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_array_get_size(v___x_1232_);
v___x_1235_ = lean_nat_dec_lt(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v___x_1232_);
goto v___jp_1220_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_sub(v___x_1234_, v___x_1236_);
v___x_1238_ = lean_nat_dec_le(v___x_1233_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v___x_1237_);
lean_dec_ref(v___x_1232_);
goto v___jp_1220_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_tmpDecl_1241_; lean_object* v___x_1242_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1240_ = lean_box(0);
lean_inc(v_declName_1216_);
v_tmpDecl_1241_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1241_, 0, v_declName_1216_);
lean_ctor_set(v_tmpDecl_1241_, 1, v___x_1239_);
lean_ctor_set(v_tmpDecl_1241_, 2, v___x_1240_);
lean_ctor_set(v_tmpDecl_1241_, 3, v___x_1217_);
v___x_1242_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1232_, v_tmpDecl_1241_, v___x_1233_, v___x_1237_);
lean_dec_ref_known(v_tmpDecl_1241_, 4);
lean_dec_ref(v___x_1232_);
if (lean_obj_tag(v___x_1242_) == 0)
{
goto v___jp_1220_;
}
else
{
lean_dec(v_declName_1216_);
lean_dec_ref(v_env_1215_);
return v___x_1242_;
}
}
}
}
}
v___jp_1220_:
{
lean_object* v_toEnvExtension_1221_; lean_object* v_asyncMode_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v_snd_1226_; lean_object* v___x_1227_; 
v_toEnvExtension_1221_ = lean_ctor_get(v___x_1219_, 0);
v_asyncMode_1222_ = lean_ctor_get(v_toEnvExtension_1221_, 2);
v___x_1223_ = lean_box(0);
v___x_1224_ = 0;
v___x_1225_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1218_, v___x_1219_, v_env_1215_, v_asyncMode_1222_, v___x_1223_, v___x_1224_);
v_snd_1226_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_snd_1226_);
lean_dec(v___x_1225_);
v___x_1227_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1226_, v_declName_1216_);
lean_dec(v_declName_1216_);
lean_dec(v_snd_1226_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1258_, v_x_1259_, v_x_1260_);
lean_dec(v_x_1260_);
lean_dec_ref(v_x_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1262_, lean_object* v_k_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1262_, v_k_1263_, v_x_1264_, v_x_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1268_, lean_object* v_k_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1268_, v_k_1269_, v_x_1270_, v_x_1271_, v_x_1272_);
lean_dec_ref(v_k_1269_);
lean_dec_ref(v_as_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1274_, lean_object* v_x_1275_, size_t v_x_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1275_, v_x_1276_, v_x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
size_t v_x_584__boxed_1283_; lean_object* v_res_1284_; 
v_x_584__boxed_1283_ = lean_unbox_usize(v_x_1281_);
lean_dec(v_x_1281_);
v_res_1284_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1279_, v_x_1280_, v_x_584__boxed_1283_, v_x_1282_);
lean_dec(v_x_1282_);
lean_dec_ref(v_x_1280_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1285_, lean_object* v_keys_1286_, lean_object* v_vals_1287_, lean_object* v_heq_1288_, lean_object* v_i_1289_, lean_object* v_k_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1286_, v_vals_1287_, v_i_1289_, v_k_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1292_, lean_object* v_keys_1293_, lean_object* v_vals_1294_, lean_object* v_heq_1295_, lean_object* v_i_1296_, lean_object* v_k_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1292_, v_keys_1293_, v_vals_1294_, v_heq_1295_, v_i_1296_, v_k_1297_);
lean_dec(v_k_1297_);
lean_dec_ref(v_vals_1294_);
lean_dec_ref(v_keys_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1299_, lean_object* v_declName_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1302_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1299_, v_declName_1300_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v___x_1303_; lean_object* v_toEnvExtension_1304_; lean_object* v_asyncMode_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1303_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1304_ = lean_ctor_get(v___x_1303_, 0);
v_asyncMode_1305_ = lean_ctor_get(v_toEnvExtension_1304_, 2);
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1301_, v___x_1303_, v_env_1299_, v_asyncMode_1305_, v___x_1306_);
v___x_1308_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1307_, v_declName_1300_);
lean_dec(v_declName_1300_);
lean_dec(v___x_1307_);
return v___x_1308_;
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___y_1314_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_val_1309_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1312_ = l_Lean_IR_declMapExt;
v___x_1327_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1311_, v___x_1312_, v_env_1299_, v_val_1309_);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_array_get_size(v___x_1327_);
v___x_1330_ = lean_nat_dec_lt(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec_ref(v___x_1327_);
v___x_1331_ = lean_box(0);
v___y_1314_ = v___x_1331_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_sub(v___x_1329_, v___x_1332_);
v___x_1334_ = lean_nat_dec_le(v___x_1328_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec(v___x_1333_);
lean_dec_ref(v___x_1327_);
v___x_1335_ = lean_box(0);
v___y_1314_ = v___x_1335_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_tmpDecl_1338_; lean_object* v___x_1339_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1337_ = lean_box(0);
lean_inc(v_declName_1300_);
v_tmpDecl_1338_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1338_, 0, v_declName_1300_);
lean_ctor_set(v_tmpDecl_1338_, 1, v___x_1336_);
lean_ctor_set(v_tmpDecl_1338_, 2, v___x_1337_);
lean_ctor_set(v_tmpDecl_1338_, 3, v___x_1310_);
v___x_1339_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1327_, v_tmpDecl_1338_, v___x_1328_, v___x_1333_);
lean_dec_ref_known(v_tmpDecl_1338_, 4);
lean_dec_ref(v___x_1327_);
if (lean_obj_tag(v___x_1339_) == 0)
{
v___y_1314_ = v___x_1339_;
goto v___jp_1313_;
}
else
{
lean_dec(v_val_1309_);
lean_dec(v_declName_1300_);
lean_dec_ref(v_env_1299_);
return v___x_1339_;
}
}
}
v___jp_1313_:
{
uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1315_ = 0;
v___x_1316_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1311_, v___x_1312_, v_env_1299_, v_val_1309_, v___x_1315_);
lean_dec(v_val_1309_);
lean_dec_ref(v_env_1299_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v___x_1316_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v___x_1316_);
lean_dec(v_declName_1300_);
return v___y_1314_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_sub(v___x_1318_, v___x_1320_);
v___x_1322_ = lean_nat_dec_le(v___x_1317_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v___x_1321_);
lean_dec_ref(v___x_1316_);
lean_dec(v_declName_1300_);
return v___y_1314_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_tmpDecl_1325_; lean_object* v___x_1326_; 
lean_dec(v___y_1314_);
v___x_1323_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1324_ = lean_box(0);
v_tmpDecl_1325_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1325_, 0, v_declName_1300_);
lean_ctor_set(v_tmpDecl_1325_, 1, v___x_1323_);
lean_ctor_set(v_tmpDecl_1325_, 2, v___x_1324_);
lean_ctor_set(v_tmpDecl_1325_, 3, v___x_1310_);
v___x_1326_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1316_, v_tmpDecl_1325_, v___x_1317_, v___x_1321_);
lean_dec_ref_known(v_tmpDecl_1325_, 4);
lean_dec_ref(v___x_1316_);
return v___x_1326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1340_, lean_object* v_declName_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v_boxed_1343_; lean_object* v___x_1344_; 
v___x_1342_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
lean_inc(v_declName_1341_);
v_boxed_1343_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1341_);
v___x_1344_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1340_, v_declName_1341_);
lean_dec(v_declName_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; lean_object* v_toEnvExtension_1346_; lean_object* v_asyncMode_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1345_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1346_ = lean_ctor_get(v___x_1345_, 0);
v_asyncMode_1347_ = lean_ctor_get(v_toEnvExtension_1346_, 2);
v___x_1348_ = lean_box(0);
v___x_1349_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1342_, v___x_1345_, v_env_1340_, v_asyncMode_1347_, v___x_1348_);
v___x_1350_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1349_, v_boxed_1343_);
lean_dec(v_boxed_1343_);
lean_dec(v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___y_1356_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_val_1351_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1354_ = l_Lean_IR_declMapExt;
v___x_1369_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1353_, v___x_1354_, v_env_1340_, v_val_1351_);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_array_get_size(v___x_1369_);
v___x_1372_ = lean_nat_dec_lt(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_dec_ref(v___x_1369_);
v___x_1373_ = lean_box(0);
v___y_1356_ = v___x_1373_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_sub(v___x_1371_, v___x_1374_);
v___x_1376_ = lean_nat_dec_le(v___x_1370_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v___x_1375_);
lean_dec_ref(v___x_1369_);
v___x_1377_ = lean_box(0);
v___y_1356_ = v___x_1377_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_tmpDecl_1380_; lean_object* v___x_1381_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1379_ = lean_box(0);
lean_inc(v_boxed_1343_);
v_tmpDecl_1380_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1380_, 0, v_boxed_1343_);
lean_ctor_set(v_tmpDecl_1380_, 1, v___x_1378_);
lean_ctor_set(v_tmpDecl_1380_, 2, v___x_1379_);
lean_ctor_set(v_tmpDecl_1380_, 3, v___x_1352_);
v___x_1381_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1369_, v_tmpDecl_1380_, v___x_1370_, v___x_1375_);
lean_dec_ref_known(v_tmpDecl_1380_, 4);
lean_dec_ref(v___x_1369_);
if (lean_obj_tag(v___x_1381_) == 0)
{
v___y_1356_ = v___x_1381_;
goto v___jp_1355_;
}
else
{
lean_dec(v_val_1351_);
lean_dec(v_boxed_1343_);
lean_dec_ref(v_env_1340_);
return v___x_1381_;
}
}
}
v___jp_1355_:
{
uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1357_ = 0;
v___x_1358_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1353_, v___x_1354_, v_env_1340_, v_val_1351_, v___x_1357_);
lean_dec(v_val_1351_);
lean_dec_ref(v_env_1340_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_array_get_size(v___x_1358_);
v___x_1361_ = lean_nat_dec_lt(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v___x_1358_);
lean_dec(v_boxed_1343_);
return v___y_1356_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_sub(v___x_1360_, v___x_1362_);
v___x_1364_ = lean_nat_dec_le(v___x_1359_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_dec(v___x_1363_);
lean_dec_ref(v___x_1358_);
lean_dec(v_boxed_1343_);
return v___y_1356_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_tmpDecl_1367_; lean_object* v___x_1368_; 
lean_dec(v___y_1356_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1366_ = lean_box(0);
v_tmpDecl_1367_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1367_, 0, v_boxed_1343_);
lean_ctor_set(v_tmpDecl_1367_, 1, v___x_1365_);
lean_ctor_set(v_tmpDecl_1367_, 2, v___x_1366_);
lean_ctor_set(v_tmpDecl_1367_, 3, v___x_1352_);
v___x_1368_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1358_, v_tmpDecl_1367_, v___x_1359_, v___x_1363_);
lean_dec_ref_known(v_tmpDecl_1367_, 4);
lean_dec_ref(v___x_1358_);
return v___x_1368_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1382_, lean_object* v_constName_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1382_, v_constName_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v___x_1385_; lean_object* v_toEnvExtension_1386_; lean_object* v_asyncMode_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1385_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1386_ = lean_ctor_get(v___x_1385_, 0);
v_asyncMode_1387_ = lean_ctor_get(v_toEnvExtension_1386_, 2);
v___x_1388_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1388_, v___x_1385_, v_env_1382_, v_asyncMode_1387_, v___x_1389_);
v___x_1391_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1390_, v_constName_1383_);
lean_dec(v_constName_1383_);
lean_dec(v___x_1390_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = 1;
return v___x_1392_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = 0;
return v___x_1393_;
}
}
else
{
uint8_t v___x_1394_; 
lean_dec_ref_known(v___x_1384_, 1);
lean_dec(v_constName_1383_);
lean_dec_ref(v_env_1382_);
v___x_1394_ = 0;
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1395_, lean_object* v_constName_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = lean_has_compile_error(v_env_1395_, v_constName_1396_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v_env_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = lean_st_ref_get(v_a_1400_);
v_env_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc_ref(v_env_1403_);
lean_dec(v___x_1402_);
v___x_1404_ = l_Lean_IR_findEnvDecl(v_env_1403_, v_n_1399_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_IR_findDecl___redArg(v_n_1406_, v_a_1407_);
lean_dec(v_a_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_IR_findDecl___redArg(v_n_1410_, v_a_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_IR_findDecl(v_n_1415_, v_a_1416_, v_a_1417_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1438_; 
v___x_1423_ = l_Lean_IR_findDecl___redArg(v_n_1420_, v_a_1421_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1428_ = 0;
v___x_1429_ = lean_box(v___x_1428_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1429_);
v___x_1431_ = v___x_1426_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
else
{
uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_dec_ref_known(v_a_1424_, 1);
v___x_1433_ = 1;
v___x_1434_ = lean_box(v___x_1433_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1434_);
v___x_1436_ = v___x_1426_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_IR_containsDecl___redArg(v_n_1439_, v_a_1440_);
lean_dec(v_a_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_IR_containsDecl___redArg(v_n_1443_, v_a_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_IR_containsDecl(v_n_1448_, v_a_1449_, v_a_1450_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_ref_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_ref_1457_ = lean_ctor_get(v___y_1454_, 2);
v___x_1458_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1453_, v___y_1454_, v___y_1455_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
lean_inc(v_ref_1457_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_ref_1457_);
lean_ctor_set(v___x_1463_, 1, v_a_1459_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 1);
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1497_; 
lean_inc(v_n_1475_);
v___x_1479_ = l_Lean_IR_findDecl___redArg(v_n_1475_, v_a_1477_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1497_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1497_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
if (lean_obj_tag(v_a_1480_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1486_; 
lean_dec(v_n_1475_);
v_val_1484_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_a_1480_, 1);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_val_1484_);
v___x_1486_ = v___x_1482_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_val_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
else
{
lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_del_object(v___x_1482_);
lean_dec(v_a_1480_);
v___x_1488_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1489_ = 1;
v___x_1490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1475_, v___x_1489_);
v___x_1491_ = lean_string_append(v___x_1488_, v___x_1490_);
lean_dec_ref(v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1493_ = lean_string_append(v___x_1491_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = l_Lean_MessageData_ofFormat(v___x_1494_);
v___x_1496_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1495_, v_a_1476_, v_a_1477_);
return v___x_1496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_IR_getDecl(v_n_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1504_, v___y_1505_, v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_msg_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1509_, v_msg_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_env_1520_; lean_object* v___x_1521_; lean_object* v_toEnvExtension_1522_; lean_object* v_asyncMode_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1518_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1519_ = lean_st_ref_get(v_a_1516_);
v_env_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc_ref(v_env_1520_);
lean_dec(v___x_1519_);
v___x_1521_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1522_ = lean_ctor_get(v___x_1521_, 0);
v_asyncMode_1523_ = lean_ctor_get(v_toEnvExtension_1522_, 2);
v___x_1524_ = lean_box(0);
v___x_1525_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1518_, v___x_1521_, v_env_1520_, v_asyncMode_1523_, v___x_1524_);
v___x_1526_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1525_, v_n_1515_);
lean_dec(v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_IR_findLocalDecl___redArg(v_n_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec(v_n_1528_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_IR_findLocalDecl___redArg(v_n_1532_, v_a_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_IR_findLocalDecl(v_n_1537_, v_a_1538_, v_a_1539_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_n_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v_toEnvExtension_1544_; lean_object* v_asyncMode_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1543_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1544_ = lean_ctor_get(v___x_1543_, 0);
v_asyncMode_1545_ = lean_ctor_get(v_toEnvExtension_1544_, 2);
v___x_1546_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1547_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1546_, v___x_1543_, v_env_1542_, v_asyncMode_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___lam__0(lean_object* v___x_1548_, lean_object* v_decl_1549_, lean_object* v_s_1550_){
_start:
{
lean_object* v_addEntryFn_1551_; lean_object* v_importedEntries_1552_; lean_object* v_state_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_addEntryFn_1551_ = lean_ctor_get(v___x_1548_, 3);
lean_inc(v_addEntryFn_1551_);
lean_dec_ref(v___x_1548_);
v_importedEntries_1552_ = lean_ctor_get(v_s_1550_, 0);
v_state_1553_ = lean_ctor_get(v_s_1550_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_s_1550_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v_s_1550_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_state_1553_);
lean_inc(v_importedEntries_1552_);
lean_dec(v_s_1550_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_state_1557_; lean_object* v___x_1559_; 
v_state_1557_ = lean_apply_2(v_addEntryFn_1551_, v_state_1553_, v_decl_1549_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 1, v_state_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_importedEntries_1552_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_state_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v_env_1570_; lean_object* v_nextMacroScope_1571_; lean_object* v_ngen_1572_; lean_object* v_auxDeclNGen_1573_; lean_object* v_traceState_1574_; lean_object* v_recordedDeps_1575_; lean_object* v_messages_1576_; lean_object* v_infoState_1577_; lean_object* v_snapshotTasks_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1601_; 
v___x_1569_ = lean_st_ref_take(v_a_1567_);
v_env_1570_ = lean_ctor_get(v___x_1569_, 0);
v_nextMacroScope_1571_ = lean_ctor_get(v___x_1569_, 1);
v_ngen_1572_ = lean_ctor_get(v___x_1569_, 2);
v_auxDeclNGen_1573_ = lean_ctor_get(v___x_1569_, 3);
v_traceState_1574_ = lean_ctor_get(v___x_1569_, 4);
v_recordedDeps_1575_ = lean_ctor_get(v___x_1569_, 6);
v_messages_1576_ = lean_ctor_get(v___x_1569_, 7);
v_infoState_1577_ = lean_ctor_get(v___x_1569_, 8);
v_snapshotTasks_1578_ = lean_ctor_get(v___x_1569_, 9);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1569_, 5);
lean_dec(v_unused_1602_);
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1601_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snapshotTasks_1578_);
lean_inc(v_infoState_1577_);
lean_inc(v_messages_1576_);
lean_inc(v_recordedDeps_1575_);
lean_inc(v_traceState_1574_);
lean_inc(v_auxDeclNGen_1573_);
lean_inc(v_ngen_1572_);
lean_inc(v_nextMacroScope_1571_);
lean_inc(v_env_1570_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1601_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v_toEnvExtension_1583_; lean_object* v_asyncMode_1584_; uint8_t v_logWrites_1585_; lean_object* v___x_1586_; lean_object* v___y_1588_; lean_object* v___f_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1582_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1583_ = lean_ctor_get(v___x_1582_, 0);
v_asyncMode_1584_ = lean_ctor_get(v_toEnvExtension_1583_, 2);
v_logWrites_1585_ = lean_ctor_get_uint8(v_toEnvExtension_1583_, sizeof(void*)*6);
v___x_1586_ = lean_box(0);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_IR_addDecl___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1595_, 0, v___x_1582_);
lean_closure_set(v___f_1595_, 1, v_decl_1566_);
v___x_1596_ = lean_box(0);
v___x_1597_ = 1;
if (v_logWrites_1585_ == 0)
{
lean_object* v___x_1598_; 
lean_inc_ref(v_toEnvExtension_1583_);
v___x_1598_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1583_, v_env_1570_, v___f_1595_, v_asyncMode_1584_, v___x_1596_, v___x_1597_);
v___y_1588_ = v___x_1598_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_inc_ref_n(v_toEnvExtension_1583_, 2);
v___x_1599_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1583_, v_env_1570_);
lean_dec_ref(v_env_1570_);
v___x_1600_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1583_, v___x_1599_, v___f_1595_, v_asyncMode_1584_, v___x_1596_, v___x_1597_);
v___y_1588_ = v___x_1600_;
goto v___jp_1587_;
}
v___jp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 5, v___x_1589_);
lean_ctor_set(v___x_1580_, 0, v___y_1588_);
v___x_1591_ = v___x_1580_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___y_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_nextMacroScope_1571_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_ngen_1572_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_auxDeclNGen_1573_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_traceState_1574_);
lean_ctor_set(v_reuseFailAlloc_1594_, 5, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1594_, 6, v_recordedDeps_1575_);
lean_ctor_set(v_reuseFailAlloc_1594_, 7, v_messages_1576_);
lean_ctor_set(v_reuseFailAlloc_1594_, 8, v_infoState_1577_);
lean_ctor_set(v_reuseFailAlloc_1594_, 9, v_snapshotTasks_1578_);
v___x_1591_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_st_ref_put(v_a_1567_, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1586_);
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_IR_addDecl___redArg(v_decl_1603_, v_a_1604_);
lean_dec(v_a_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_IR_addDecl___redArg(v_decl_1607_, v_a_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_IR_addDecl(v_decl_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1617_, size_t v_i_1618_, size_t v_stop_1619_, lean_object* v_b_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_usize_dec_eq(v_i_1618_, v_stop_1619_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_array_uget_borrowed(v_as_1617_, v_i_1618_);
lean_inc(v___x_1624_);
v___x_1625_ = l_Lean_IR_addDecl___redArg(v___x_1624_, v___y_1621_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; size_t v___x_1627_; size_t v___x_1628_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = ((size_t)1ULL);
v___x_1628_ = lean_usize_add(v_i_1618_, v___x_1627_);
v_i_1618_ = v___x_1628_;
v_b_1620_ = v_a_1626_;
goto _start;
}
else
{
return v___x_1625_;
}
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_b_1620_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1631_, lean_object* v_i_1632_, lean_object* v_stop_1633_, lean_object* v_b_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
size_t v_i_boxed_1637_; size_t v_stop_boxed_1638_; lean_object* v_res_1639_; 
v_i_boxed_1637_ = lean_unbox_usize(v_i_1632_);
lean_dec(v_i_1632_);
v_stop_boxed_1638_ = lean_unbox_usize(v_stop_1633_);
lean_dec(v_stop_1633_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1631_, v_i_boxed_1637_, v_stop_boxed_1638_, v_b_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v_as_1631_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = lean_array_get_size(v_decls_1640_);
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_nat_dec_lt(v___x_1644_, v___x_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
return v___x_1648_;
}
else
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_nat_dec_le(v___x_1645_, v___x_1645_);
if (v___x_1649_ == 0)
{
if (v___x_1647_ == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1646_);
return v___x_1650_;
}
else
{
size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = lean_usize_of_nat(v___x_1645_);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1640_, v___x_1651_, v___x_1652_, v___x_1646_, v_a_1642_);
return v___x_1653_;
}
}
else
{
size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = lean_usize_of_nat(v___x_1645_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1640_, v___x_1654_, v___x_1655_, v___x_1646_, v_a_1642_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_IR_addDecls(v_decls_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v_decls_1657_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1662_, size_t v_i_1663_, size_t v_stop_1664_, lean_object* v_b_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1662_, v_i_1663_, v_stop_1664_, v_b_1665_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1670_, lean_object* v_i_1671_, lean_object* v_stop_1672_, lean_object* v_b_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
size_t v_i_boxed_1677_; size_t v_stop_boxed_1678_; lean_object* v_res_1679_; 
v_i_boxed_1677_ = lean_unbox_usize(v_i_1671_);
lean_dec(v_i_1671_);
v_stop_boxed_1678_ = lean_unbox_usize(v_stop_1672_);
lean_dec(v_stop_1672_);
v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1670_, v_i_boxed_1677_, v_stop_boxed_1678_, v_b_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v_as_1670_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1683_, lean_object* v_as_1684_, size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_b_1687_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_lt(v_i_1686_, v_sz_1685_);
if (v___x_1688_ == 0)
{
lean_inc_ref(v_b_1687_);
return v_b_1687_;
}
else
{
lean_object* v___x_1689_; lean_object* v_a_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1689_ = lean_box(0);
v_a_1690_ = lean_array_uget_borrowed(v_as_1684_, v_i_1686_);
v___x_1691_ = l_Lean_IR_Decl_name(v_a_1690_);
v___x_1692_ = lean_name_eq(v___x_1691_, v_n_1683_);
lean_dec(v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; 
v___x_1693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1694_ = ((size_t)1ULL);
v___x_1695_ = lean_usize_add(v_i_1686_, v___x_1694_);
v_i_1686_ = v___x_1695_;
v_b_1687_ = v___x_1693_;
goto _start;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_inc(v_a_1690_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1690_);
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1689_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1700_, lean_object* v_as_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_b_1704_){
_start:
{
size_t v_sz_boxed_1705_; size_t v_i_boxed_1706_; lean_object* v_res_1707_; 
v_sz_boxed_1705_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1706_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1700_, v_as_1701_, v_sz_boxed_1705_, v_i_boxed_1706_, v_b_1704_);
lean_dec_ref(v_b_1704_);
lean_dec_ref(v_as_1701_);
lean_dec(v_n_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1708_, lean_object* v_n_1709_, lean_object* v_decls_1710_){
_start:
{
lean_object* v___x_1711_; size_t v_sz_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v_fst_1715_; 
v___x_1711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1712_ = lean_array_size(v_decls_1710_);
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1709_, v_decls_1710_, v_sz_1712_, v___x_1713_, v___x_1711_);
v_fst_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_fst_1715_);
lean_dec_ref(v___x_1714_);
if (lean_obj_tag(v_fst_1715_) == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_IR_findEnvDecl(v_env_1708_, v_n_1709_);
return v___x_1716_;
}
else
{
lean_object* v_val_1717_; 
v_val_1717_ = lean_ctor_get(v_fst_1715_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v_fst_1715_, 1);
if (lean_obj_tag(v_val_1717_) == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_IR_findEnvDecl(v_env_1708_, v_n_1709_);
return v___x_1718_;
}
else
{
lean_dec(v_n_1709_);
lean_dec_ref(v_env_1708_);
return v_val_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1719_, lean_object* v_n_1720_, lean_object* v_decls_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_IR_findEnvDecl_x27(v_env_1719_, v_n_1720_, v_decls_1721_);
lean_dec_ref(v_decls_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1723_, lean_object* v_decls_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v_env_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1727_ = lean_st_ref_get(v_a_1725_);
v_env_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc_ref(v_env_1728_);
lean_dec(v___x_1727_);
v___x_1729_ = l_Lean_IR_findEnvDecl_x27(v_env_1728_, v_n_1723_, v_decls_1724_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1731_, lean_object* v_decls_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_IR_findDecl_x27___redArg(v_n_1731_, v_decls_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_decls_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1736_, lean_object* v_decls_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_IR_findDecl_x27___redArg(v_n_1736_, v_decls_1737_, v_a_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1742_, lean_object* v_decls_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_IR_findDecl_x27(v_n_1742_, v_decls_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec_ref(v_decls_1743_);
return v_res_1747_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1748_, lean_object* v_as_1749_, size_t v_i_1750_, size_t v_stop_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_eq(v_i_1750_, v_stop_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_array_uget_borrowed(v_as_1749_, v_i_1750_);
v___x_1754_ = l_Lean_IR_Decl_name(v___x_1753_);
v___x_1755_ = lean_name_eq(v___x_1754_, v_n_1748_);
lean_dec(v___x_1754_);
if (v___x_1755_ == 0)
{
size_t v___x_1756_; size_t v___x_1757_; 
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1750_, v___x_1756_);
v_i_1750_ = v___x_1757_;
goto _start;
}
else
{
return v___x_1755_;
}
}
else
{
uint8_t v___x_1759_; 
v___x_1759_ = 0;
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1760_, lean_object* v_as_1761_, lean_object* v_i_1762_, lean_object* v_stop_1763_){
_start:
{
size_t v_i_boxed_1764_; size_t v_stop_boxed_1765_; uint8_t v_res_1766_; lean_object* v_r_1767_; 
v_i_boxed_1764_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_stop_boxed_1765_ = lean_unbox_usize(v_stop_1763_);
lean_dec(v_stop_1763_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1760_, v_as_1761_, v_i_boxed_1764_, v_stop_boxed_1765_);
lean_dec_ref(v_as_1761_);
lean_dec(v_n_1760_);
v_r_1767_ = lean_box(v_res_1766_);
return v_r_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1768_, lean_object* v_decls_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_array_get_size(v_decls_1769_);
v___x_1774_ = lean_nat_dec_lt(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_IR_containsDecl___redArg(v_n_1768_, v_a_1770_);
return v___x_1775_;
}
else
{
if (v___x_1774_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_IR_containsDecl___redArg(v_n_1768_, v_a_1770_);
return v___x_1776_;
}
else
{
size_t v___x_1777_; size_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = lean_usize_of_nat(v___x_1773_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1768_, v_decls_1769_, v___x_1777_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_IR_containsDecl___redArg(v_n_1768_, v_a_1770_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_n_1768_);
v___x_1781_ = lean_box(v___x_1774_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1783_, lean_object* v_decls_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1783_, v_decls_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_decls_1784_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1788_, lean_object* v_decls_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1788_, v_decls_1789_, v_a_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1794_, lean_object* v_decls_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_IR_containsDecl_x27(v_n_1794_, v_decls_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec_ref(v_decls_1795_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1800_, lean_object* v_decls_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1823_; 
lean_inc(v_n_1800_);
v___x_1805_ = l_Lean_IR_findDecl_x27___redArg(v_n_1800_, v_decls_1801_, v_a_1803_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1823_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1823_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
if (lean_obj_tag(v_a_1806_) == 1)
{
lean_object* v_val_1810_; lean_object* v___x_1812_; 
lean_dec(v_n_1800_);
v_val_1810_ = lean_ctor_get(v_a_1806_, 0);
lean_inc(v_val_1810_);
lean_dec_ref_known(v_a_1806_, 1);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_val_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_val_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
else
{
lean_object* v___x_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_del_object(v___x_1808_);
lean_dec(v_a_1806_);
v___x_1814_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1815_ = 1;
v___x_1816_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1800_, v___x_1815_);
v___x_1817_ = lean_string_append(v___x_1814_, v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
v___x_1821_ = l_Lean_MessageData_ofFormat(v___x_1820_);
v___x_1822_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1821_, v_a_1802_, v_a_1803_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1824_, lean_object* v_decls_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_IR_getDecl_x27(v_n_1824_, v_decls_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec_ref(v_decls_1825_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1830_, lean_object* v_declName_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_IR_findEnvDecl(v_env_1830_, v_declName_1831_);
if (lean_obj_tag(v___x_1832_) == 1)
{
lean_object* v_val_1833_; 
v_val_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v___x_1832_, 1);
if (lean_obj_tag(v_val_1833_) == 0)
{
lean_object* v_info_1834_; 
v_info_1834_ = lean_ctor_get(v_val_1833_, 4);
lean_inc(v_info_1834_);
lean_dec_ref_known(v_val_1833_, 5);
return v_info_1834_;
}
else
{
lean_object* v___x_1835_; 
lean_dec(v_val_1833_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
}
else
{
lean_object* v___x_1836_; 
lean_dec(v___x_1832_);
v___x_1836_ = lean_box(0);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(uint8_t v_level_1837_, lean_object* v_env_1838_, uint8_t v_includeDecls_1839_, lean_object* v_as_1840_, size_t v_i_1841_, size_t v_stop_1842_, lean_object* v_b_1843_){
_start:
{
lean_object* v___y_1845_; uint8_t v___x_1849_; 
v___x_1849_ = lean_usize_dec_eq(v_i_1841_, v_stop_1842_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; uint8_t v___y_1852_; 
v___x_1850_ = lean_array_uget_borrowed(v_as_1840_, v_i_1841_);
if (v_includeDecls_1839_ == 0)
{
uint8_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = 1;
lean_inc(v___x_1850_);
lean_inc_ref(v_env_1838_);
v___x_1863_ = l_Lean_Environment_contains(v_env_1838_, v___x_1850_, v___x_1862_);
if (v___x_1863_ == 0)
{
goto v___jp_1854_;
}
else
{
v___y_1845_ = v_b_1843_;
goto v___jp_1844_;
}
}
else
{
goto v___jp_1854_;
}
v___jp_1851_:
{
if (v___y_1852_ == 0)
{
v___y_1845_ = v_b_1843_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1853_; 
lean_inc(v___x_1850_);
v___x_1853_ = lean_array_push(v_b_1843_, v___x_1850_);
v___y_1845_ = v___x_1853_;
goto v___jp_1844_;
}
}
v___jp_1854_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1855_ = lean_box(v_level_1837_);
v___x_1856_ = lean_obj_tag_nat(v___x_1855_);
lean_dec(v___x_1855_);
v___x_1857_ = lean_unsigned_to_nat(2u);
v___x_1858_ = lean_nat_dec_eq(v___x_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
lean_inc_ref(v_env_1838_);
v___x_1859_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1838_, v___x_1850_);
if (v___x_1859_ == 0)
{
uint8_t v___x_1860_; 
lean_inc_ref(v_env_1838_);
v___x_1860_ = l_Lean_isDeclMeta(v_env_1838_, v___x_1850_);
v___y_1852_ = v___x_1860_;
goto v___jp_1851_;
}
else
{
v___y_1852_ = v___x_1859_;
goto v___jp_1851_;
}
}
else
{
lean_object* v___x_1861_; 
lean_inc(v___x_1850_);
v___x_1861_ = lean_array_push(v_b_1843_, v___x_1850_);
v___y_1845_ = v___x_1861_;
goto v___jp_1844_;
}
}
}
else
{
lean_dec_ref(v_env_1838_);
return v_b_1843_;
}
v___jp_1844_:
{
size_t v___x_1846_; size_t v___x_1847_; 
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1841_, v___x_1846_);
v_i_1841_ = v___x_1847_;
v_b_1843_ = v___y_1845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_level_1864_, lean_object* v_env_1865_, lean_object* v_includeDecls_1866_, lean_object* v_as_1867_, lean_object* v_i_1868_, lean_object* v_stop_1869_, lean_object* v_b_1870_){
_start:
{
uint8_t v_level_boxed_1871_; uint8_t v_includeDecls_boxed_1872_; size_t v_i_boxed_1873_; size_t v_stop_boxed_1874_; lean_object* v_res_1875_; 
v_level_boxed_1871_ = lean_unbox(v_level_1864_);
v_includeDecls_boxed_1872_ = lean_unbox(v_includeDecls_1866_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1868_);
lean_dec(v_i_1868_);
v_stop_boxed_1874_ = lean_unbox_usize(v_stop_1869_);
lean_dec(v_stop_1869_);
v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_boxed_1871_, v_env_1865_, v_includeDecls_boxed_1872_, v_as_1867_, v_i_boxed_1873_, v_stop_boxed_1874_, v_b_1870_);
lean_dec_ref(v_as_1867_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1876_, size_t v_i_1877_, lean_object* v_bs_1878_){
_start:
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_usize_dec_lt(v_i_1877_, v_sz_1876_);
if (v___x_1879_ == 0)
{
return v_bs_1878_;
}
else
{
lean_object* v_v_1880_; lean_object* v___x_1881_; lean_object* v_bs_x27_1882_; lean_object* v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v_v_1880_ = lean_array_uget(v_bs_1878_, v_i_1877_);
v___x_1881_ = lean_unsigned_to_nat(0u);
v_bs_x27_1882_ = lean_array_uset(v_bs_1878_, v_i_1877_, v___x_1881_);
v___x_1883_ = l_Lean_IR_Decl_name(v_v_1880_);
lean_dec(v_v_1880_);
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1877_, v___x_1884_);
v___x_1886_ = lean_array_uset(v_bs_x27_1882_, v_i_1877_, v___x_1883_);
v_i_1877_ = v___x_1885_;
v_bs_1878_ = v___x_1886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1888_, lean_object* v_i_1889_, lean_object* v_bs_1890_){
_start:
{
size_t v_sz_boxed_1891_; size_t v_i_boxed_1892_; lean_object* v_res_1893_; 
v_sz_boxed_1891_ = lean_unbox_usize(v_sz_1888_);
lean_dec(v_sz_1888_);
v_i_boxed_1892_ = lean_unbox_usize(v_i_1889_);
lean_dec(v_i_1889_);
v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1891_, v_i_boxed_1892_, v_bs_1890_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1896_, uint8_t v_level_1897_, uint8_t v_includeDecls_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v_toEnvExtension_1900_; lean_object* v_asyncMode_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; lean_object* v_env_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; size_t v_sz_1910_; size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1899_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1900_ = lean_ctor_get(v___x_1899_, 0);
v_asyncMode_1901_ = lean_ctor_get(v_toEnvExtension_1900_, 2);
v___x_1902_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1903_ = lean_box(v_level_1897_);
v___x_1904_ = lean_obj_tag_nat(v___x_1903_);
lean_dec(v___x_1903_);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_nat_dec_eq(v___x_1904_, v___x_1905_);
v_env_1907_ = l_Lean_Environment_setExporting(v_env_1896_, v___x_1906_);
lean_inc_ref(v_env_1907_);
v___x_1908_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1902_, v___x_1899_, v_env_1907_, v_asyncMode_1901_);
v___x_1909_ = lean_array_mk(v___x_1908_);
v_sz_1910_ = lean_array_size(v___x_1909_);
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1910_, v___x_1911_, v___x_1909_);
v___x_1913_ = lean_array_get_size(v___x_1912_);
v___x_1914_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1915_ = lean_nat_dec_lt(v___x_1905_, v___x_1913_);
if (v___x_1915_ == 0)
{
lean_dec_ref(v___x_1912_);
lean_dec_ref(v_env_1907_);
return v___x_1914_;
}
else
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_nat_dec_le(v___x_1913_, v___x_1913_);
if (v___x_1916_ == 0)
{
if (v___x_1915_ == 0)
{
lean_dec_ref(v___x_1912_);
lean_dec_ref(v_env_1907_);
return v___x_1914_;
}
else
{
size_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_usize_of_nat(v___x_1913_);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1897_, v_env_1907_, v_includeDecls_1898_, v___x_1912_, v___x_1911_, v___x_1917_, v___x_1914_);
lean_dec_ref(v___x_1912_);
return v___x_1918_;
}
}
else
{
size_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_usize_of_nat(v___x_1913_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1897_, v_env_1907_, v_includeDecls_1898_, v___x_1912_, v___x_1911_, v___x_1919_, v___x_1914_);
lean_dec_ref(v___x_1912_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1921_, lean_object* v_level_1922_, lean_object* v_includeDecls_1923_){
_start:
{
uint8_t v_level_boxed_1924_; uint8_t v_includeDecls_boxed_1925_; lean_object* v_res_1926_; 
v_level_boxed_1924_ = lean_unbox(v_level_1922_);
v_includeDecls_boxed_1925_ = lean_unbox(v_includeDecls_1923_);
v_res_1926_ = lean_get_ir_extra_const_names(v_env_1921_, v_level_boxed_1924_, v_includeDecls_boxed_1925_);
return v_res_1926_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_declMapExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_declMapExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_CompilerM(builtin);
}
#ifdef __cplusplus
}
#endif
