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
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_OLeanLevel_ctorIdx(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)}};
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0;
static const lean_array_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__1_value;
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_IR_LogEntry_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_cls_8_; lean_object* v_decls_9_; lean_object* v___x_10_; 
v_cls_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_cls_8_);
v_decls_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_decls_9_);
lean_dec_ref_known(v_t_6_, 2);
v___x_10_ = lean_apply_2(v_k_7_, v_cls_8_, v_decls_9_);
return v___x_10_;
}
else
{
lean_object* v_msg_11_; lean_object* v___x_12_; 
v_msg_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_msg_11_);
lean_dec_ref_known(v_t_6_, 1);
v___x_12_ = lean_apply_1(v_k_7_, v_msg_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_IR_LogEntry_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim___redArg(lean_object* v_t_25_, lean_object* v_step_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_25_, v_step_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_step_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_29_, v_step_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim___redArg(lean_object* v_t_33_, lean_object* v_message_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_33_, v_message_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_message_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_37_, v_message_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_LogEntry_fmt_spec__0(lean_object* v_a_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_nat_to_int(v_a_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(lean_object* v_as_43_, size_t v_i_44_, size_t v_stop_45_, lean_object* v_b_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = lean_usize_dec_eq(v_i_44_, v_stop_45_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; size_t v___x_54_; size_t v___x_55_; 
v___x_48_ = lean_array_uget_borrowed(v_as_43_, v_i_44_);
v___x_49_ = lean_box(1);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v_b_46_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_48_);
v___x_52_ = l_Lean_IR_formatDecl(v___x_48_, v___x_51_);
v___x_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_44_, v___x_54_);
v_i_44_ = v___x_55_;
v_b_46_ = v___x_53_;
goto _start;
}
else
{
return v_b_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object* v_as_57_, lean_object* v_i_58_, lean_object* v_stop_59_, lean_object* v_b_60_){
_start:
{
size_t v_i_boxed_61_; size_t v_stop_boxed_62_; lean_object* v_res_63_; 
v_i_boxed_61_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_stop_boxed_62_ = lean_unbox_usize(v_stop_59_);
lean_dec(v_stop_59_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_as_57_, v_i_boxed_61_, v_stop_boxed_62_, v_b_60_);
lean_dec_ref(v_as_57_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__2(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__0));
v___x_67_ = lean_string_length(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l_Lean_IR_LogEntry_fmt___closed__2, &l_Lean_IR_LogEntry_fmt___closed__2_once, _init_l_Lean_IR_LogEntry_fmt___closed__2);
v___x_69_ = lean_nat_to_int(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_cls_75_; lean_object* v_decls_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_108_; 
v_cls_75_ = lean_ctor_get(v_x_74_, 0);
v_decls_76_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_108_ == 0)
{
v___x_78_ = v_x_74_;
v_isShared_79_ = v_isSharedCheck_108_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_decls_76_);
lean_inc(v_cls_75_);
lean_dec(v_x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_108_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_80_ = 1;
v___x_81_ = l_Lean_Name_toString(v_cls_75_, v___x_80_);
v___x_82_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
v___x_83_ = lean_obj_once(&l_Lean_IR_LogEntry_fmt___closed__3, &l_Lean_IR_LogEntry_fmt___closed__3_once, _init_l_Lean_IR_LogEntry_fmt___closed__3);
v___x_84_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__4));
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 5);
lean_ctor_set(v___x_78_, 1, v___x_82_);
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_82_);
v___x_86_ = v_reuseFailAlloc_107_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_87_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__5));
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_83_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v_decls_76_);
v___x_95_ = lean_nat_dec_lt(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v_decls_76_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_92_);
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_le(v___x_94_, v___x_94_);
if (v___x_97_ == 0)
{
if (v___x_95_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v_decls_76_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_91_);
lean_ctor_set(v___x_98_, 1, v___x_92_);
return v___x_98_;
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_94_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_76_, v___x_99_, v___x_100_, v___x_92_);
lean_dec_ref(v_decls_76_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_91_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
return v___x_102_;
}
}
else
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = ((size_t)0ULL);
v___x_104_ = lean_usize_of_nat(v___x_94_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_76_, v___x_103_, v___x_104_, v___x_92_);
lean_dec_ref(v_decls_76_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_91_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
return v___x_106_;
}
}
}
}
}
else
{
lean_object* v_msg_109_; 
v_msg_109_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_msg_109_);
lean_dec_ref_known(v_x_74_, 1);
return v_msg_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_, lean_object* v_b_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; size_t v___x_122_; size_t v___x_123_; 
v___x_117_ = lean_array_uget_borrowed(v_as_112_, v_i_113_);
v___x_118_ = lean_box(1);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v_b_115_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_inc(v___x_117_);
v___x_120_ = l_Lean_IR_LogEntry_fmt(v___x_117_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_add(v_i_113_, v___x_122_);
v_i_113_ = v___x_123_;
v_b_115_ = v___x_121_;
goto _start;
}
else
{
return v_b_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(lean_object* v_as_125_, lean_object* v_i_126_, lean_object* v_stop_127_, lean_object* v_b_128_){
_start:
{
size_t v_i_boxed_129_; size_t v_stop_boxed_130_; lean_object* v_res_131_; 
v_i_boxed_129_ = lean_unbox_usize(v_i_126_);
lean_dec(v_i_126_);
v_stop_boxed_130_ = lean_unbox_usize(v_stop_127_);
lean_dec(v_stop_127_);
v_res_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_as_125_, v_i_boxed_129_, v_stop_boxed_130_, v_b_128_);
lean_dec_ref(v_as_125_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object* v_log_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = lean_box(0);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_log_132_);
v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
return v___x_133_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_le(v___x_135_, v___x_135_);
if (v___x_137_ == 0)
{
if (v___x_136_ == 0)
{
return v___x_133_;
}
else
{
size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_135_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_132_, v___x_138_, v___x_139_, v___x_133_);
return v___x_140_;
}
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_135_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_132_, v___x_141_, v___x_142_, v___x_133_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object* v_log_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_IR_Log_format(v_log_144_);
lean_dec_ref(v_log_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object* v_log_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = l_Lean_IR_Log_format(v_log_146_);
v___x_148_ = l_Std_Format_defWidth;
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Std_Format_pretty(v___x_147_, v___x_148_, v___x_149_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object* v_log_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_IR_Log_toString(v_log_151_);
lean_dec_ref(v_log_151_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_alloc_ctor(0, 11, 0);
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
lean_object* v___x_176_; lean_object* v_toCold_177_; lean_object* v_env_178_; lean_object* v_options_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_toCold_177_ = lean_ctor_get(v___y_173_, 0);
v_env_178_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_178_);
lean_dec(v___x_176_);
v_options_179_ = lean_ctor_get(v_toCold_177_, 2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
v___x_181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_179_);
v___x_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_182_, 0, v_env_178_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_ctor_set(v___x_182_, 3, v_options_179_);
v___x_183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_msgData_172_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object* v_msgData_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msgData_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_189_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0(void){
_start:
{
lean_object* v___x_190_; double v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_float_of_nat(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object* v_cls_195_, lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_247_; 
v_ref_200_ = lean_ctor_get(v___y_197_, 2);
v___x_201_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_196_, v___y_197_, v___y_198_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_247_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_247_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_247_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v_traceState_207_; lean_object* v_env_208_; lean_object* v_nextMacroScope_209_; lean_object* v_ngen_210_; lean_object* v_auxDeclNGen_211_; lean_object* v_cache_212_; lean_object* v_recordedDeps_213_; lean_object* v_messages_214_; lean_object* v_infoState_215_; lean_object* v_snapshotTasks_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_246_; 
v___x_206_ = lean_st_ref_take(v___y_198_);
v_traceState_207_ = lean_ctor_get(v___x_206_, 4);
v_env_208_ = lean_ctor_get(v___x_206_, 0);
v_nextMacroScope_209_ = lean_ctor_get(v___x_206_, 1);
v_ngen_210_ = lean_ctor_get(v___x_206_, 2);
v_auxDeclNGen_211_ = lean_ctor_get(v___x_206_, 3);
v_cache_212_ = lean_ctor_get(v___x_206_, 5);
v_recordedDeps_213_ = lean_ctor_get(v___x_206_, 6);
v_messages_214_ = lean_ctor_get(v___x_206_, 7);
v_infoState_215_ = lean_ctor_get(v___x_206_, 8);
v_snapshotTasks_216_ = lean_ctor_get(v___x_206_, 9);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_246_ == 0)
{
v___x_218_ = v___x_206_;
v_isShared_219_ = v_isSharedCheck_246_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_snapshotTasks_216_);
lean_inc(v_infoState_215_);
lean_inc(v_messages_214_);
lean_inc(v_recordedDeps_213_);
lean_inc(v_cache_212_);
lean_inc(v_traceState_207_);
lean_inc(v_auxDeclNGen_211_);
lean_inc(v_ngen_210_);
lean_inc(v_nextMacroScope_209_);
lean_inc(v_env_208_);
lean_dec(v___x_206_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_246_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint64_t v_tid_220_; lean_object* v_traces_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_245_; 
v_tid_220_ = lean_ctor_get_uint64(v_traceState_207_, sizeof(void*)*1);
v_traces_221_ = lean_ctor_get(v_traceState_207_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_traceState_207_);
if (v_isSharedCheck_245_ == 0)
{
v___x_223_ = v_traceState_207_;
v_isShared_224_ = v_isSharedCheck_245_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_traces_221_);
lean_dec(v_traceState_207_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_245_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; double v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_225_ = lean_box(0);
v___x_226_ = lean_box(0);
v___x_227_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_228_ = 0;
v___x_229_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_230_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_230_, 0, v_cls_195_);
lean_ctor_set(v___x_230_, 1, v___x_226_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_ctor_set_float(v___x_230_, sizeof(void*)*3, v___x_227_);
lean_ctor_set_float(v___x_230_, sizeof(void*)*3 + 8, v___x_227_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*3 + 16, v___x_228_);
v___x_231_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_232_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v_a_202_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
lean_inc(v_ref_200_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_ref_200_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = l_Lean_PersistentArray_push___redArg(v_traces_221_, v___x_233_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_234_);
v___x_236_ = v___x_223_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_234_);
lean_ctor_set_uint64(v_reuseFailAlloc_244_, sizeof(void*)*1, v_tid_220_);
v___x_236_ = v_reuseFailAlloc_244_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 4, v___x_236_);
v___x_238_ = v___x_218_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_env_208_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_nextMacroScope_209_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_ngen_210_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_auxDeclNGen_211_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_recordedDeps_213_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v_messages_214_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v_infoState_215_);
lean_ctor_set(v_reuseFailAlloc_243_, 9, v_snapshotTasks_216_);
v___x_238_ = v_reuseFailAlloc_243_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_st_ref_put(v___y_198_, v___x_238_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_225_);
v___x_241_ = v___x_204_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_225_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_248_, v_msg_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_263_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_264_ = l_Lean_IR_LogEntry_fmt(v_entry_259_);
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
v___x_266_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_263_, v___x_265_, v_a_260_, v_a_261_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_IR_log(v_entry_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
return v_res_271_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_280_, lean_object* v_optName_281_){
_start:
{
lean_object* v_map_282_; lean_object* v___x_289_; 
v_map_282_ = lean_ctor_get(v_opts_280_, 0);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_282_, v_optName_281_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; 
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v___x_289_, 1);
if (lean_obj_tag(v_val_290_) == 1)
{
uint8_t v_v_291_; 
v_v_291_ = lean_ctor_get_uint8(v_val_290_, 0);
lean_dec_ref_known(v_val_290_, 0);
return v_v_291_;
}
else
{
lean_dec(v_val_290_);
goto v___jp_283_;
}
}
else
{
lean_dec(v___x_289_);
goto v___jp_283_;
}
v___jp_283_:
{
lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_285_ = 0;
v___x_286_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_282_, v___x_284_);
if (lean_obj_tag(v___x_286_) == 0)
{
return v___x_285_;
}
else
{
lean_object* v_val_287_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_286_, 1);
if (lean_obj_tag(v_val_287_) == 1)
{
uint8_t v_v_288_; 
v_v_288_ = lean_ctor_get_uint8(v_val_287_, 0);
lean_dec_ref_known(v_val_287_, 0);
return v_v_288_;
}
else
{
lean_dec(v_val_287_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_292_, lean_object* v_optName_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_292_, v_optName_293_);
lean_dec(v_optName_293_);
lean_dec_ref(v_opts_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_296_, lean_object* v_cls_297_, lean_object* v_decls_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_299_);
v___x_303_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_302_, v_optName_296_);
lean_dec_ref(v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_decls_298_);
lean_dec(v_cls_297_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_cls_297_);
lean_ctor_set(v___x_306_, 1, v_decls_298_);
v___x_307_ = l_Lean_IR_log(v___x_306_, v_a_299_, v_a_300_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_308_, lean_object* v_cls_309_, lean_object* v_decls_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_308_, v_cls_309_, v_decls_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_optName_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_315_, lean_object* v_decl_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_315_);
v___x_321_ = l_Lean_Name_append(v___x_320_, v_cls_315_);
v___x_322_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_321_, v_cls_315_, v_decl_316_, v_a_317_, v_a_318_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_323_, lean_object* v_decl_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_IR_logDecls(v_cls_323_, v_decl_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_329_, lean_object* v_optName_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_332_);
v___x_336_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_335_, v_optName_330_);
lean_dec_ref(v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_a_331_);
lean_dec_ref(v_inst_329_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_apply_1(v_inst_329_, v_a_331_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = l_Lean_IR_log(v___x_340_, v_a_332_, v_a_333_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_342_, lean_object* v_optName_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_342_, v_optName_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_optName_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_optName_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_350_, v_optName_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_357_, lean_object* v_inst_358_, lean_object* v_optName_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_357_, v_inst_358_, v_optName_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_optName_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_365_, lean_object* v_cls_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_372_ = l_Lean_Name_append(v___x_371_, v_cls_366_);
v___x_373_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_365_, v___x_372_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_374_, lean_object* v_cls_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_IR_logMessageIf___redArg(v_inst_374_, v_cls_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_381_, lean_object* v_inst_382_, lean_object* v_cls_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_389_ = l_Lean_Name_append(v___x_388_, v_cls_383_);
v___x_390_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_382_, v___x_389_, v_a_384_, v_a_385_, v_a_386_);
lean_dec(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_391_, lean_object* v_inst_392_, lean_object* v_cls_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_IR_logMessageIf(v_00_u03b1_391_, v_inst_392_, v_cls_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_405_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_399_, v___x_404_, v_a_400_, v_a_401_, v_a_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_IR_logMessage___redArg(v_inst_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_412_, lean_object* v_inst_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_419_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_413_, v___x_418_, v_a_414_, v_a_415_, v_a_416_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_420_, lean_object* v_inst_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_IR_logMessage(v_00_u03b1_420_, v_inst_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_427_, lean_object* v_b_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = l_Lean_IR_Decl_name(v_a_427_);
v___x_430_ = l_Lean_IR_Decl_name(v_b_428_);
v___x_431_ = l_Lean_Name_quickLt(v___x_429_, v___x_430_);
lean_dec(v___x_430_);
lean_dec(v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_432_, lean_object* v_b_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_432_, v_b_433_);
lean_dec_ref(v_b_433_);
lean_dec_ref(v_a_432_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_array_get_size(v_decls_437_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_nat_dec_eq(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___y_445_; uint8_t v___x_449_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_sub(v___x_438_, v___x_442_);
v___x_449_ = lean_nat_dec_le(v___x_439_, v___x_443_);
if (v___x_449_ == 0)
{
lean_inc(v___x_443_);
v___y_445_ = v___x_443_;
goto v___jp_444_;
}
else
{
v___y_445_ = v___x_439_;
goto v___jp_444_;
}
v___jp_444_:
{
uint8_t v___x_446_; 
v___x_446_ = lean_nat_dec_le(v___y_445_, v___x_443_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v___x_443_);
lean_inc(v___y_445_);
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_441_, v___x_438_, v_decls_437_, v___y_445_, v___y_445_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_445_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_441_, v___x_438_, v_decls_437_, v___y_445_, v___x_443_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_443_);
return v___x_448_;
}
}
}
else
{
return v_decls_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_453_, lean_object* v_declName_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_array_get_size(v_decls_453_);
v___x_457_ = lean_nat_dec_lt(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v_declName_454_);
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v___x_456_, v___x_459_);
v___x_461_ = lean_nat_dec_le(v___x_455_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v___x_460_);
lean_dec(v_declName_454_);
v___x_462_ = lean_box(0);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_tmpDecl_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_464_ = lean_box(0);
v___x_465_ = lean_box(0);
v_tmpDecl_466_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_466_, 0, v_declName_454_);
lean_ctor_set(v_tmpDecl_466_, 1, v___x_463_);
lean_ctor_set(v_tmpDecl_466_, 2, v___x_464_);
lean_ctor_set(v_tmpDecl_466_, 3, v___x_465_);
v___x_467_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_468_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_469_ = l_Array_binSearchAux___redArg(v___x_467_, v___x_468_, v_decls_453_, v_tmpDecl_466_, v___x_455_, v___x_460_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_470_, lean_object* v_declName_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_470_, v_declName_471_);
lean_dec_ref(v_decls_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_473_, lean_object* v_pivot_474_, lean_object* v_as_475_, lean_object* v_i_476_, lean_object* v_k_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_lt(v_k_477_, v_hi_473_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_k_477_);
v___x_479_ = lean_array_fswap(v_as_475_, v_i_476_, v_hi_473_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_i_476_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_481_ = lean_array_fget_borrowed(v_as_475_, v_k_477_);
v___x_482_ = l_Lean_IR_Decl_name(v___x_481_);
v___x_483_ = l_Lean_IR_Decl_name(v_pivot_474_);
v___x_484_ = l_Lean_Name_quickLt(v___x_482_, v___x_483_);
lean_dec(v___x_483_);
lean_dec(v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_k_477_, v___x_485_);
lean_dec(v_k_477_);
v_k_477_ = v___x_486_;
goto _start;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_array_fswap(v_as_475_, v_i_476_, v_k_477_);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_i_476_, v___x_489_);
lean_dec(v_i_476_);
v___x_491_ = lean_nat_add(v_k_477_, v___x_489_);
lean_dec(v_k_477_);
v_as_475_ = v___x_488_;
v_i_476_ = v___x_490_;
v_k_477_ = v___x_491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_493_, lean_object* v_pivot_494_, lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_k_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_493_, v_pivot_494_, v_as_495_, v_i_496_, v_k_497_);
lean_dec_ref(v_pivot_494_);
lean_dec(v_hi_493_);
return v_res_498_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = l_Lean_IR_Decl_name(v___y_499_);
v___x_502_ = l_Lean_IR_Decl_name(v___y_500_);
v___x_503_ = l_Lean_Name_quickLt(v___x_501_, v___x_502_);
lean_dec(v___x_502_);
lean_dec(v___x_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_504_, v___y_505_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v___y_504_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_508_, lean_object* v_as_509_, lean_object* v_lo_510_, lean_object* v_hi_511_){
_start:
{
lean_object* v___y_513_; uint8_t v___x_523_; 
v___x_523_ = lean_nat_dec_lt(v_lo_510_, v_hi_511_);
if (v___x_523_ == 0)
{
lean_dec(v_lo_510_);
return v_as_509_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_mid_526_; lean_object* v___y_528_; lean_object* v___y_534_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_524_ = lean_nat_add(v_lo_510_, v_hi_511_);
v___x_525_ = lean_unsigned_to_nat(1u);
v_mid_526_ = lean_nat_shiftr(v___x_524_, v___x_525_);
lean_dec(v___x_524_);
v___x_539_ = lean_array_fget_borrowed(v_as_509_, v_mid_526_);
v___x_540_ = lean_array_fget_borrowed(v_as_509_, v_lo_510_);
v___x_541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
v___y_534_ = v_as_509_;
goto v___jp_533_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_array_fswap(v_as_509_, v_lo_510_, v_mid_526_);
v___y_534_ = v___x_542_;
goto v___jp_533_;
}
v___jp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_529_ = lean_array_fget_borrowed(v___y_528_, v_mid_526_);
v___x_530_ = lean_array_fget_borrowed(v___y_528_, v_hi_511_);
v___x_531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec(v_mid_526_);
v___y_513_ = v___y_528_;
goto v___jp_512_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_array_fswap(v___y_528_, v_mid_526_, v_hi_511_);
lean_dec(v_mid_526_);
v___y_513_ = v___x_532_;
goto v___jp_512_;
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_array_fget_borrowed(v___y_534_, v_hi_511_);
v___x_536_ = lean_array_fget_borrowed(v___y_534_, v_lo_510_);
v___x_537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
v___y_528_ = v___y_534_;
goto v___jp_527_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_array_fswap(v___y_534_, v_lo_510_, v_hi_511_);
v___y_528_ = v___x_538_;
goto v___jp_527_;
}
}
}
v___jp_512_:
{
lean_object* v_pivot_514_; lean_object* v___x_515_; lean_object* v_fst_516_; lean_object* v_snd_517_; uint8_t v___x_518_; 
v_pivot_514_ = lean_array_fget(v___y_513_, v_hi_511_);
lean_inc_n(v_lo_510_, 2);
v___x_515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_511_, v_pivot_514_, v___y_513_, v_lo_510_, v_lo_510_);
lean_dec(v_pivot_514_);
v_fst_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_fst_516_);
v_snd_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc(v_snd_517_);
lean_dec_ref(v___x_515_);
v___x_518_ = lean_nat_dec_le(v_hi_511_, v_fst_516_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_508_, v_snd_517_, v_lo_510_, v_fst_516_);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v_fst_516_, v___x_520_);
lean_dec(v_fst_516_);
v_as_509_ = v___x_519_;
v_lo_510_ = v___x_521_;
goto _start;
}
else
{
lean_dec(v_fst_516_);
lean_dec(v_lo_510_);
return v_snd_517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_543_, lean_object* v_as_544_, lean_object* v_lo_545_, lean_object* v_hi_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_543_, v_as_544_, v_lo_545_, v_hi_546_);
lean_dec(v_hi_546_);
lean_dec(v_n_543_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_554_, lean_object* v_as_555_, size_t v_i_556_, size_t v_stop_557_, lean_object* v_b_558_){
_start:
{
lean_object* v___y_560_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_eq(v_i_556_, v_stop_557_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___y_574_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_572_ = lean_array_uget_borrowed(v_as_555_, v_i_556_);
v___x_589_ = l_Lean_IR_Decl_name(v___x_572_);
lean_inc_ref(v_env_554_);
v___x_590_ = l_Lean_isDeclMeta(v_env_554_, v___x_589_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
lean_inc_ref(v_env_554_);
v___x_591_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_554_, v___x_589_);
if (v___x_591_ == 0)
{
lean_dec(v___x_589_);
v___y_560_ = v_b_558_;
goto v___jp_559_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_589_);
if (v___x_592_ == 0)
{
lean_dec(v___x_589_);
v___y_574_ = v___x_590_;
goto v___jp_573_;
}
else
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = l_Lean_Name_getPrefix(v___x_589_);
lean_dec(v___x_589_);
lean_inc_ref(v_env_554_);
v___x_594_ = l_Lean_isExtern(v_env_554_, v___x_593_);
v___y_574_ = v___x_594_;
goto v___jp_573_;
}
}
}
else
{
lean_object* v___x_595_; 
lean_dec(v___x_589_);
lean_inc(v___x_572_);
v___x_595_ = lean_array_push(v_b_558_, v___x_572_);
v___y_560_ = v___x_595_;
goto v___jp_559_;
}
v___jp_573_:
{
if (v___y_574_ == 0)
{
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_f_575_; lean_object* v_xs_576_; lean_object* v_type_577_; lean_object* v___x_578_; 
v_f_575_ = lean_ctor_get(v___x_572_, 0);
v_xs_576_ = lean_ctor_get(v___x_572_, 1);
v_type_577_ = lean_ctor_get(v___x_572_, 2);
lean_inc(v_f_575_);
lean_inc_ref(v_env_554_);
v___x_578_ = lean_get_export_name_for(v_env_554_, v_f_575_);
if (lean_obj_tag(v___x_578_) == 1)
{
lean_object* v_val_579_; 
v_val_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_578_, 1);
if (lean_obj_tag(v_val_579_) == 1)
{
lean_object* v_str_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_str_580_ = lean_ctor_get(v_val_579_, 1);
lean_inc_ref(v_str_580_);
lean_dec_ref_known(v_val_579_, 2);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v_str_580_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_inc(v_type_577_);
lean_inc_ref(v_xs_576_);
lean_inc(v_f_575_);
v___x_585_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_585_, 0, v_f_575_);
lean_ctor_set(v___x_585_, 1, v_xs_576_);
lean_ctor_set(v___x_585_, 2, v_type_577_);
lean_ctor_set(v___x_585_, 3, v___x_584_);
v___x_586_ = lean_array_push(v_b_558_, v___x_585_);
v___y_560_ = v___x_586_;
goto v___jp_559_;
}
else
{
lean_dec(v_val_579_);
lean_inc_ref(v_xs_576_);
lean_inc(v_f_575_);
lean_inc(v_type_577_);
v___y_565_ = v_type_577_;
v___y_566_ = v_f_575_;
v___y_567_ = v_xs_576_;
goto v___jp_564_;
}
}
else
{
lean_dec(v___x_578_);
lean_inc_ref(v_xs_576_);
lean_inc(v_f_575_);
lean_inc(v_type_577_);
v___y_565_ = v_type_577_;
v___y_566_ = v_f_575_;
v___y_567_ = v_xs_576_;
goto v___jp_564_;
}
}
else
{
lean_object* v___x_587_; 
lean_inc(v___x_572_);
v___x_587_ = lean_array_push(v_b_558_, v___x_572_);
v___y_560_ = v___x_587_;
goto v___jp_559_;
}
}
else
{
lean_object* v___x_588_; 
lean_inc(v___x_572_);
v___x_588_ = lean_array_push(v_b_558_, v___x_572_);
v___y_560_ = v___x_588_;
goto v___jp_559_;
}
}
}
else
{
lean_dec_ref(v_env_554_);
return v_b_558_;
}
v___jp_559_:
{
size_t v___x_561_; size_t v___x_562_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_556_, v___x_561_);
v_i_556_ = v___x_562_;
v_b_558_ = v___y_560_;
goto _start;
}
v___jp_564_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_569_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_569_, 0, v___y_566_);
lean_ctor_set(v___x_569_, 1, v___y_567_);
lean_ctor_set(v___x_569_, 2, v___y_565_);
lean_ctor_set(v___x_569_, 3, v___x_568_);
v___x_570_ = lean_array_push(v_b_558_, v___x_569_);
v___y_560_ = v___x_570_;
goto v___jp_559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_596_, lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_stop_599_, lean_object* v_b_600_){
_start:
{
size_t v_i_boxed_601_; size_t v_stop_boxed_602_; lean_object* v_res_603_; 
v_i_boxed_601_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_stop_boxed_602_ = lean_unbox_usize(v_stop_599_);
lean_dec(v_stop_599_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_596_, v_as_597_, v_i_boxed_601_, v_stop_boxed_602_, v_b_600_);
lean_dec_ref(v_as_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_606_, lean_object* v_as_607_, lean_object* v_start_608_, lean_object* v_stop_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_611_ = lean_nat_dec_lt(v_start_608_, v_stop_609_);
if (v___x_611_ == 0)
{
lean_dec_ref(v_env_606_);
return v___x_610_;
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_get_size(v_as_607_);
v___x_613_ = lean_nat_dec_le(v_stop_609_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_lt(v_start_608_, v___x_612_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_env_606_);
return v___x_610_;
}
else
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_usize_of_nat(v_start_608_);
v___x_616_ = lean_usize_of_nat(v___x_612_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_606_, v_as_607_, v___x_615_, v___x_616_, v___x_610_);
return v___x_617_;
}
}
else
{
size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_usize_of_nat(v_start_608_);
v___x_619_ = lean_usize_of_nat(v_stop_609_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_606_, v_as_607_, v___x_618_, v___x_619_, v___x_610_);
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_621_, lean_object* v_as_622_, lean_object* v_start_623_, lean_object* v_stop_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_621_, v_as_622_, v_start_623_, v_stop_624_);
lean_dec(v_stop_624_);
lean_dec(v_start_623_);
lean_dec_ref(v_as_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
return v_x_626_;
}
else
{
lean_object* v_head_628_; lean_object* v_tail_629_; lean_object* v___x_630_; 
v_head_628_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_head_628_);
v_tail_629_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_tail_629_);
lean_dec_ref_known(v_x_627_, 2);
v___x_630_ = lean_array_push(v_x_626_, v_head_628_);
v_x_626_ = v___x_630_;
v_x_627_ = v_tail_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_632_, lean_object* v_s_633_, lean_object* v_entries_634_){
_start:
{
lean_object* v___y_636_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_decls_646_; lean_object* v___x_647_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___x_652_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_646_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_645_, v_entries_634_);
v___x_647_ = lean_array_get_size(v_decls_646_);
v___x_652_ = lean_nat_dec_eq(v___x_647_, v___x_644_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; uint8_t v___x_658_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_sub(v___x_647_, v___x_653_);
v___x_658_ = lean_nat_dec_le(v___x_644_, v___x_654_);
if (v___x_658_ == 0)
{
lean_inc(v___x_654_);
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
else
{
v___y_656_ = v___x_644_;
goto v___jp_655_;
}
v___jp_655_:
{
uint8_t v___x_657_; 
v___x_657_ = lean_nat_dec_le(v___y_656_, v___x_654_);
if (v___x_657_ == 0)
{
lean_dec(v___x_654_);
lean_inc(v___y_656_);
v___y_649_ = v___y_656_;
v___y_650_ = v___y_656_;
goto v___jp_648_;
}
else
{
v___y_649_ = v___y_656_;
v___y_650_ = v___x_654_;
goto v___jp_648_;
}
}
}
else
{
v___y_636_ = v_decls_646_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v___x_637_; uint8_t v_isModule_638_; 
v___x_637_ = l_Lean_Environment_header(v_env_632_);
v_isModule_638_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_637_);
if (v_isModule_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v_env_632_);
lean_inc_ref_n(v___y_636_, 2);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v___y_636_);
lean_ctor_set(v___x_639_, 1, v___y_636_);
lean_ctor_set(v___x_639_, 2, v___y_636_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_array_get_size(v___y_636_);
v___x_642_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_632_, v___y_636_, v___x_640_, v___x_641_);
lean_dec_ref(v___y_636_);
lean_inc_ref_n(v___x_642_, 2);
v___x_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
return v___x_643_;
}
}
v___jp_648_:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_647_, v_decls_646_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
v___y_636_ = v___x_651_;
goto v___jp_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_659_, lean_object* v_s_660_, lean_object* v_entries_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_659_, v_s_660_, v_entries_661_);
lean_dec_ref(v_s_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_array_mk(v_es_663_);
return v___x_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object* v_keys_665_, lean_object* v_i_666_, lean_object* v_k_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_keys_665_);
v___x_669_ = lean_nat_dec_lt(v_i_666_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_i_666_);
return v___x_669_;
}
else
{
lean_object* v_k_x27_670_; uint8_t v___x_671_; 
v_k_x27_670_ = lean_array_fget_borrowed(v_keys_665_, v_i_666_);
v___x_671_ = lean_name_eq(v_k_667_, v_k_x27_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v_i_666_, v___x_672_);
lean_dec(v_i_666_);
v_i_666_ = v___x_673_;
goto _start;
}
else
{
lean_dec(v_i_666_);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_675_, lean_object* v_i_676_, lean_object* v_k_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_675_, v_i_676_, v_k_677_);
lean_dec(v_k_677_);
lean_dec_ref(v_keys_675_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_680_, size_t v_x_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_object* v_es_683_; lean_object* v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v_j_687_; lean_object* v___x_688_; 
v_es_683_ = lean_ctor_get(v_x_680_, 0);
v___x_684_ = lean_box(2);
v___x_685_ = ((size_t)31ULL);
v___x_686_ = lean_usize_land(v_x_681_, v___x_685_);
v_j_687_ = lean_usize_to_nat(v___x_686_);
v___x_688_ = lean_array_get_borrowed(v___x_684_, v_es_683_, v_j_687_);
lean_dec(v_j_687_);
switch(lean_obj_tag(v___x_688_))
{
case 0:
{
lean_object* v_key_689_; uint8_t v___x_690_; 
v_key_689_ = lean_ctor_get(v___x_688_, 0);
v___x_690_ = lean_name_eq(v_x_682_, v_key_689_);
return v___x_690_;
}
case 1:
{
lean_object* v_node_691_; size_t v___x_692_; size_t v___x_693_; 
v_node_691_ = lean_ctor_get(v___x_688_, 0);
v___x_692_ = ((size_t)5ULL);
v___x_693_ = lean_usize_shift_right(v_x_681_, v___x_692_);
v_x_680_ = v_node_691_;
v_x_681_ = v___x_693_;
goto _start;
}
default: 
{
uint8_t v___x_695_; 
v___x_695_ = 0;
return v___x_695_;
}
}
}
else
{
lean_object* v_ks_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_ks_696_ = lean_ctor_get(v_x_680_, 0);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_696_, v___x_697_, v_x_682_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
size_t v_x_2170__boxed_702_; uint8_t v_res_703_; lean_object* v_r_704_; 
v_x_2170__boxed_702_ = lean_unbox_usize(v_x_700_);
lean_dec(v_x_700_);
v_res_703_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_699_, v_x_2170__boxed_702_, v_x_701_);
lean_dec(v_x_701_);
lean_dec_ref(v_x_699_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
uint64_t v___y_708_; 
if (lean_obj_tag(v_x_706_) == 0)
{
uint64_t v___x_711_; 
v___x_711_ = 1723ULL;
v___y_708_ = v___x_711_;
goto v___jp_707_;
}
else
{
uint64_t v_hash_712_; 
v_hash_712_ = lean_ctor_get_uint64(v_x_706_, sizeof(void*)*2);
v___y_708_ = v_hash_712_;
goto v___jp_707_;
}
v___jp_707_:
{
size_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_uint64_to_usize(v___y_708_);
v___x_710_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_705_, v___x_709_, v_x_706_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_713_, v_x_714_);
lean_dec(v_x_714_);
lean_dec_ref(v_x_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_717_, lean_object* v_x2_718_){
_start:
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = l_Lean_IR_Decl_name(v_x2_718_);
v___x_720_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_717_, v___x_719_);
lean_dec(v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = 1;
return v___x_721_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = 0;
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_723_, lean_object* v_x2_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_723_, v_x2_724_);
lean_dec_ref(v_x2_724_);
lean_dec_ref(v_x1_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_731_);
lean_dec_ref(v_x_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
lean_object* v_ks_737_; lean_object* v_vs_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_762_; 
v_ks_737_ = lean_ctor_get(v_x_733_, 0);
v_vs_738_ = lean_ctor_get(v_x_733_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_762_ == 0)
{
v___x_740_ = v_x_733_;
v_isShared_741_ = v_isSharedCheck_762_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_vs_738_);
lean_inc(v_ks_737_);
lean_dec(v_x_733_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_762_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_array_get_size(v_ks_737_);
v___x_743_ = lean_nat_dec_lt(v_x_734_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec(v_x_734_);
v___x_744_ = lean_array_push(v_ks_737_, v_x_735_);
v___x_745_ = lean_array_push(v_vs_738_, v_x_736_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_745_);
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_747_ = v___x_740_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v_k_x27_749_; uint8_t v___x_750_; 
v_k_x27_749_ = lean_array_fget_borrowed(v_ks_737_, v_x_734_);
v___x_750_ = lean_name_eq(v_x_735_, v_k_x27_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_752_; 
if (v_isShared_741_ == 0)
{
v___x_752_ = v___x_740_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_ks_737_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_vs_738_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_x_734_, v___x_753_);
lean_dec(v_x_734_);
v_x_733_ = v___x_752_;
v_x_734_ = v___x_754_;
goto _start;
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = lean_array_fset(v_ks_737_, v_x_734_, v_x_735_);
v___x_758_ = lean_array_fset(v_vs_738_, v_x_734_, v_x_736_);
lean_dec(v_x_734_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_758_);
lean_ctor_set(v___x_740_, 0, v___x_757_);
v___x_760_ = v___x_740_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_763_, lean_object* v_k_764_, lean_object* v_v_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_763_, v___x_766_, v_k_764_, v_v_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_769_, size_t v_x_770_, size_t v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
lean_object* v_es_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v_j_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_es_774_ = lean_ctor_get(v_x_769_, 0);
v___x_775_ = ((size_t)31ULL);
v___x_776_ = lean_usize_land(v_x_770_, v___x_775_);
v_j_777_ = lean_usize_to_nat(v___x_776_);
v___x_778_ = lean_array_get_size(v_es_774_);
v___x_779_ = lean_nat_dec_lt(v_j_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_dec(v_j_777_);
lean_dec(v_x_773_);
lean_dec(v_x_772_);
return v_x_769_;
}
else
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_818_; 
lean_inc_ref(v_es_774_);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_x_769_, 0);
lean_dec(v_unused_819_);
v___x_781_ = v_x_769_;
v_isShared_782_ = v_isSharedCheck_818_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_x_769_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_818_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_v_783_; lean_object* v___x_784_; lean_object* v_xs_x27_785_; lean_object* v___y_787_; 
v_v_783_ = lean_array_fget(v_es_774_, v_j_777_);
v___x_784_ = lean_box(0);
v_xs_x27_785_ = lean_array_fset(v_es_774_, v_j_777_, v___x_784_);
switch(lean_obj_tag(v_v_783_))
{
case 0:
{
lean_object* v_key_792_; lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v_key_792_ = lean_ctor_get(v_v_783_, 0);
v_val_793_ = lean_ctor_get(v_v_783_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_v_783_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v_v_783_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_inc(v_key_792_);
lean_dec(v_v_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
uint8_t v___x_797_; 
v___x_797_ = lean_name_eq(v_x_772_, v_key_792_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_795_);
v___x_798_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_792_, v_val_793_, v_x_772_, v_x_773_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___y_787_ = v___x_799_;
goto v___jp_786_;
}
else
{
lean_object* v___x_801_; 
lean_dec(v_val_793_);
lean_dec(v_key_792_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_x_773_);
lean_ctor_set(v___x_795_, 0, v_x_772_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_x_772_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_x_773_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v___y_787_ = v___x_801_;
goto v___jp_786_;
}
}
}
}
case 1:
{
lean_object* v_node_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_816_; 
v_node_804_ = lean_ctor_get(v_v_783_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_v_783_);
if (v_isSharedCheck_816_ == 0)
{
v___x_806_ = v_v_783_;
v_isShared_807_ = v_isSharedCheck_816_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_node_804_);
lean_dec(v_v_783_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_816_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_808_ = ((size_t)5ULL);
v___x_809_ = lean_usize_shift_right(v_x_770_, v___x_808_);
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_x_771_, v___x_810_);
v___x_812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_804_, v___x_809_, v___x_811_, v_x_772_, v_x_773_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_812_);
v___x_814_ = v___x_806_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
v___y_787_ = v___x_814_;
goto v___jp_786_;
}
}
}
default: 
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_x_772_);
lean_ctor_set(v___x_817_, 1, v_x_773_);
v___y_787_ = v___x_817_;
goto v___jp_786_;
}
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_array_fset(v_xs_x27_785_, v_j_777_, v___y_787_);
lean_dec(v_j_777_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_788_);
v___x_790_ = v___x_781_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
else
{
lean_object* v_ks_820_; lean_object* v_vs_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_839_; 
v_ks_820_ = lean_ctor_get(v_x_769_, 0);
v_vs_821_ = lean_ctor_get(v_x_769_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_839_ == 0)
{
v___x_823_ = v_x_769_;
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_vs_821_);
lean_inc(v_ks_820_);
lean_dec(v_x_769_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_ks_820_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_vs_821_);
v___x_826_ = v_reuseFailAlloc_838_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v_newNode_827_; size_t v___x_828_; uint8_t v___x_829_; 
v_newNode_827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_826_, v_x_772_, v_x_773_);
v___x_828_ = ((size_t)7ULL);
v___x_829_ = lean_usize_dec_le(v___x_828_, v_x_771_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_827_);
v___x_831_ = lean_unsigned_to_nat(4u);
v___x_832_ = lean_nat_dec_lt(v___x_830_, v___x_831_);
lean_dec(v___x_830_);
if (v___x_832_ == 0)
{
lean_object* v_ks_833_; lean_object* v_vs_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_ks_833_ = lean_ctor_get(v_newNode_827_, 0);
lean_inc_ref(v_ks_833_);
v_vs_834_ = lean_ctor_get(v_newNode_827_, 1);
lean_inc_ref(v_vs_834_);
lean_dec_ref(v_newNode_827_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_771_, v_ks_833_, v_vs_834_, v___x_835_, v___x_836_);
lean_dec_ref(v_vs_834_);
lean_dec_ref(v_ks_833_);
return v___x_837_;
}
else
{
return v_newNode_827_;
}
}
else
{
return v_newNode_827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t v_depth_840_, lean_object* v_keys_841_, lean_object* v_vals_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_array_get_size(v_keys_841_);
v___x_846_ = lean_nat_dec_lt(v_i_843_, v___x_845_);
if (v___x_846_ == 0)
{
lean_dec(v_i_843_);
return v_entries_844_;
}
else
{
lean_object* v_k_847_; lean_object* v_v_848_; uint64_t v___y_850_; 
v_k_847_ = lean_array_fget_borrowed(v_keys_841_, v_i_843_);
v_v_848_ = lean_array_fget_borrowed(v_vals_842_, v_i_843_);
if (lean_obj_tag(v_k_847_) == 0)
{
uint64_t v___x_861_; 
v___x_861_ = 1723ULL;
v___y_850_ = v___x_861_;
goto v___jp_849_;
}
else
{
uint64_t v_hash_862_; 
v_hash_862_ = lean_ctor_get_uint64(v_k_847_, sizeof(void*)*2);
v___y_850_ = v_hash_862_;
goto v___jp_849_;
}
v___jp_849_:
{
size_t v_h_851_; size_t v___x_852_; lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v_h_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_h_851_ = lean_uint64_to_usize(v___y_850_);
v___x_852_ = ((size_t)5ULL);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_sub(v_depth_840_, v___x_854_);
v___x_856_ = lean_usize_mul(v___x_852_, v___x_855_);
v_h_857_ = lean_usize_shift_right(v_h_851_, v___x_856_);
v___x_858_ = lean_nat_add(v_i_843_, v___x_853_);
lean_dec(v_i_843_);
lean_inc(v_v_848_);
lean_inc(v_k_847_);
v___x_859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_844_, v_h_857_, v_depth_840_, v_k_847_, v_v_848_);
v_i_843_ = v___x_858_;
v_entries_844_ = v___x_859_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_863_, lean_object* v_keys_864_, lean_object* v_vals_865_, lean_object* v_i_866_, lean_object* v_entries_867_){
_start:
{
size_t v_depth_boxed_868_; lean_object* v_res_869_; 
v_depth_boxed_868_ = lean_unbox_usize(v_depth_863_);
lean_dec(v_depth_863_);
v_res_869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_868_, v_keys_864_, v_vals_865_, v_i_866_, v_entries_867_);
lean_dec_ref(v_vals_865_);
lean_dec_ref(v_keys_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
size_t v_x_2331__boxed_875_; size_t v_x_2332__boxed_876_; lean_object* v_res_877_; 
v_x_2331__boxed_875_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_x_2332__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_res_877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_870_, v_x_2331__boxed_875_, v_x_2332__boxed_876_, v_x_873_, v_x_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
uint64_t v___y_882_; 
if (lean_obj_tag(v_x_879_) == 0)
{
uint64_t v___x_886_; 
v___x_886_ = 1723ULL;
v___y_882_ = v___x_886_;
goto v___jp_881_;
}
else
{
uint64_t v_hash_887_; 
v_hash_887_ = lean_ctor_get_uint64(v_x_879_, sizeof(void*)*2);
v___y_882_ = v_hash_887_;
goto v___jp_881_;
}
v___jp_881_:
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_uint64_to_usize(v___y_882_);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_878_, v___x_883_, v___x_884_, v_x_879_, v_x_880_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_888_, lean_object* v_d_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = l_Lean_IR_Decl_name(v_d_889_);
v___x_891_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_888_, v___x_890_, v_d_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_920_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_923_, lean_object* v_as_924_, lean_object* v_lo_925_, lean_object* v_hi_926_, lean_object* v_w_927_, lean_object* v_hlo_928_, lean_object* v_hhi_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_923_, v_as_924_, v_lo_925_, v_hi_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_931_, lean_object* v_as_932_, lean_object* v_lo_933_, lean_object* v_hi_934_, lean_object* v_w_935_, lean_object* v_hlo_936_, lean_object* v_hhi_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_931_, v_as_932_, v_lo_933_, v_hi_934_, v_w_935_, v_hlo_936_, v_hhi_937_);
lean_dec(v_hi_934_);
lean_dec(v_n_931_);
return v_res_938_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_943_, v_x_944_, v_x_945_);
lean_dec(v_x_945_);
lean_dec_ref(v_x_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_949_, v_x_950_, v_x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_953_, lean_object* v_lo_954_, lean_object* v_hi_955_, lean_object* v_hhi_956_, lean_object* v_pivot_957_, lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_k_960_, lean_object* v_ilo_961_, lean_object* v_ik_962_, lean_object* v_w_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_955_, v_pivot_957_, v_as_958_, v_i_959_, v_k_960_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_965_, lean_object* v_lo_966_, lean_object* v_hi_967_, lean_object* v_hhi_968_, lean_object* v_pivot_969_, lean_object* v_as_970_, lean_object* v_i_971_, lean_object* v_k_972_, lean_object* v_ilo_973_, lean_object* v_ik_974_, lean_object* v_w_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_965_, v_lo_966_, v_hi_967_, v_hhi_968_, v_pivot_969_, v_as_970_, v_i_971_, v_k_972_, v_ilo_973_, v_ik_974_, v_w_975_);
lean_dec_ref(v_pivot_969_);
lean_dec(v_hi_967_);
lean_dec(v_lo_966_);
lean_dec(v_n_965_);
return v_res_976_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_977_, lean_object* v_x_978_, size_t v_x_979_, lean_object* v_x_980_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_978_, v_x_979_, v_x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
size_t v_x_2613__boxed_986_; uint8_t v_res_987_; lean_object* v_r_988_; 
v_x_2613__boxed_986_ = lean_unbox_usize(v_x_984_);
lean_dec(v_x_984_);
v_res_987_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_982_, v_x_983_, v_x_2613__boxed_986_, v_x_985_);
lean_dec(v_x_985_);
lean_dec_ref(v_x_983_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, size_t v_x_991_, size_t v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_990_, v_x_991_, v_x_992_, v_x_993_, v_x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
size_t v_x_2624__boxed_1002_; size_t v_x_2625__boxed_1003_; lean_object* v_res_1004_; 
v_x_2624__boxed_1002_ = lean_unbox_usize(v_x_998_);
lean_dec(v_x_998_);
v_x_2625__boxed_1003_ = lean_unbox_usize(v_x_999_);
lean_dec(v_x_999_);
v_res_1004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_996_, v_x_997_, v_x_2624__boxed_1002_, v_x_2625__boxed_1003_, v_x_1000_, v_x_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1005_, lean_object* v_keys_1006_, lean_object* v_vals_1007_, lean_object* v_heq_1008_, lean_object* v_i_1009_, lean_object* v_k_1010_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_1006_, v_i_1009_, v_k_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1012_, lean_object* v_keys_1013_, lean_object* v_vals_1014_, lean_object* v_heq_1015_, lean_object* v_i_1016_, lean_object* v_k_1017_){
_start:
{
uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_res_1018_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1012_, v_keys_1013_, v_vals_1014_, v_heq_1015_, v_i_1016_, v_k_1017_);
lean_dec(v_k_1017_);
lean_dec_ref(v_vals_1014_);
lean_dec_ref(v_keys_1013_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1020_, lean_object* v_n_1021_, lean_object* v_k_1022_, lean_object* v_v_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1021_, v_k_1022_, v_v_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1025_, size_t v_depth_1026_, lean_object* v_keys_1027_, lean_object* v_vals_1028_, lean_object* v_heq_1029_, lean_object* v_i_1030_, lean_object* v_entries_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1026_, v_keys_1027_, v_vals_1028_, v_i_1030_, v_entries_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_depth_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_heq_1037_, lean_object* v_i_1038_, lean_object* v_entries_1039_){
_start:
{
size_t v_depth_boxed_1040_; lean_object* v_res_1041_; 
v_depth_boxed_1040_ = lean_unbox_usize(v_depth_1034_);
lean_dec(v_depth_1034_);
v_res_1041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1033_, v_depth_boxed_1040_, v_keys_1035_, v_vals_1036_, v_heq_1037_, v_i_1038_, v_entries_1039_);
lean_dec_ref(v_vals_1036_);
lean_dec_ref(v_keys_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1043_, v_x_1044_, v_x_1045_, v_x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = lean_array_get_size(v_irDecls_1048_);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_nat_dec_eq(v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___y_1056_; uint8_t v___x_1060_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_1053_ = lean_unsigned_to_nat(1u);
v___x_1054_ = lean_nat_sub(v___x_1049_, v___x_1053_);
v___x_1060_ = lean_nat_dec_le(v___x_1050_, v___x_1054_);
if (v___x_1060_ == 0)
{
lean_inc(v___x_1054_);
v___y_1056_ = v___x_1054_;
goto v___jp_1055_;
}
else
{
v___y_1056_ = v___x_1050_;
goto v___jp_1055_;
}
v___jp_1055_:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_nat_dec_le(v___y_1056_, v___x_1054_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec(v___x_1054_);
lean_inc(v___y_1056_);
v___x_1058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1052_, v___x_1049_, v_irDecls_1048_, v___y_1056_, v___y_1056_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1056_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1052_, v___x_1049_, v_irDecls_1048_, v___y_1056_, v___x_1054_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_1054_);
return v___x_1059_;
}
}
}
else
{
return v_irDecls_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1061_){
_start:
{
lean_inc_ref(v_initDecls_1061_);
return v_initDecls_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1062_);
lean_dec_ref(v_initDecls_1062_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1064_){
_start:
{
lean_inc_ref(v_modPkg_1064_);
return v_modPkg_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1065_);
lean_dec_ref(v_modPkg_1065_);
return v_res_1066_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0(void){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v_toEnvExtension_1073_; lean_object* v_name_1074_; lean_object* v_asyncMode_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___y_1080_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_irDecls_1110_; lean_object* v___x_1111_; lean_object* v___y_1113_; lean_object* v___y_1114_; uint8_t v___x_1116_; 
v___x_1072_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1073_ = lean_ctor_get(v___x_1072_, 0);
v_name_1074_ = lean_ctor_get(v___x_1072_, 1);
v_asyncMode_1075_ = lean_ctor_get(v_toEnvExtension_1073_, 2);
v___x_1076_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1077_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1078_ = lean_box(0);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1071_);
v___x_1109_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1076_, v___x_1072_, v_env_1071_, v_asyncMode_1075_);
v_irDecls_1110_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1108_, v___x_1109_);
v___x_1111_ = lean_array_get_size(v_irDecls_1110_);
v___x_1116_ = lean_nat_dec_eq(v___x_1111_, v___x_1107_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___y_1120_; uint8_t v___x_1122_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_sub(v___x_1111_, v___x_1117_);
v___x_1122_ = lean_nat_dec_le(v___x_1107_, v___x_1118_);
if (v___x_1122_ == 0)
{
lean_inc(v___x_1118_);
v___y_1120_ = v___x_1118_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v___x_1107_;
goto v___jp_1119_;
}
v___jp_1119_:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_nat_dec_le(v___y_1120_, v___x_1118_);
if (v___x_1121_ == 0)
{
lean_dec(v___x_1118_);
lean_inc(v___y_1120_);
v___y_1113_ = v___y_1120_;
v___y_1114_ = v___y_1120_;
goto v___jp_1112_;
}
else
{
v___y_1113_ = v___y_1120_;
v___y_1114_ = v___x_1118_;
goto v___jp_1112_;
}
}
}
else
{
v___y_1080_ = v_irDecls_1110_;
goto v___jp_1079_;
}
v___jp_1079_:
{
lean_object* v___x_1081_; lean_object* v_ext_1082_; lean_object* v_toEnvExtension_1083_; lean_object* v_name_1084_; lean_object* v_exportEntriesFn_1085_; lean_object* v_asyncMode_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_private_1090_; lean_object* v___x_1091_; lean_object* v_toEnvExtension_1092_; lean_object* v_name_1093_; lean_object* v_exportEntriesFn_1094_; lean_object* v_asyncMode_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_private_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1081_ = l_Lean_regularInitAttr;
v_ext_1082_ = lean_ctor_get(v___x_1081_, 1);
v_toEnvExtension_1083_ = lean_ctor_get(v_ext_1082_, 0);
v_name_1084_ = lean_ctor_get(v_ext_1082_, 1);
v_exportEntriesFn_1085_ = lean_ctor_get(v_ext_1082_, 4);
v_asyncMode_1086_ = lean_ctor_get(v_toEnvExtension_1083_, 2);
v___x_1087_ = lean_box(0);
lean_inc_ref_n(v_env_1071_, 3);
v___x_1088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1077_, v_ext_1082_, v_env_1071_, v_asyncMode_1086_, v___x_1087_);
lean_inc_ref(v_exportEntriesFn_1085_);
v___x_1089_ = lean_apply_2(v_exportEntriesFn_1085_, v_env_1071_, v___x_1088_);
v_private_1090_ = lean_ctor_get(v___x_1089_, 2);
lean_inc(v_private_1090_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1092_ = lean_ctor_get(v___x_1091_, 0);
v_name_1093_ = lean_ctor_get(v___x_1091_, 1);
v_exportEntriesFn_1094_ = lean_ctor_get(v___x_1091_, 4);
v_asyncMode_1095_ = lean_ctor_get(v_toEnvExtension_1092_, 2);
v___x_1096_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1078_, v___x_1091_, v_env_1071_, v_asyncMode_1095_, v___x_1087_);
lean_inc_ref(v_exportEntriesFn_1094_);
v___x_1097_ = lean_apply_2(v_exportEntriesFn_1094_, v_env_1071_, v___x_1096_);
v_private_1098_ = lean_ctor_get(v___x_1097_, 2);
lean_inc(v_private_1098_);
lean_dec_ref(v___x_1097_);
lean_inc(v_name_1074_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_name_1074_);
lean_ctor_set(v___x_1099_, 1, v___y_1080_);
lean_inc(v_name_1084_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_name_1084_);
lean_ctor_set(v___x_1100_, 1, v_private_1090_);
lean_inc(v_name_1093_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_name_1093_);
lean_ctor_set(v___x_1101_, 1, v_private_1098_);
v___x_1102_ = lean_unsigned_to_nat(3u);
v___x_1103_ = lean_mk_empty_array_with_capacity(v___x_1102_);
v___x_1104_ = lean_array_push(v___x_1103_, v___x_1099_);
v___x_1105_ = lean_array_push(v___x_1104_, v___x_1100_);
v___x_1106_ = lean_array_push(v___x_1105_, v___x_1101_);
return v___x_1106_;
}
v___jp_1112_:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1111_, v_irDecls_1110_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
v___y_1080_ = v___x_1115_;
goto v___jp_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1123_, lean_object* v_k_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_m_1129_; lean_object* v_a_1130_; uint8_t v___x_1131_; 
v___x_1127_ = lean_nat_add(v_x_1125_, v_x_1126_);
v___x_1128_ = lean_unsigned_to_nat(1u);
v_m_1129_ = lean_nat_shiftr(v___x_1127_, v___x_1128_);
lean_dec(v___x_1127_);
v_a_1130_ = lean_array_fget_borrowed(v_as_1123_, v_m_1129_);
v___x_1131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1130_, v_k_1124_);
if (v___x_1131_ == 0)
{
uint8_t v___x_1132_; 
lean_dec(v_x_1126_);
v___x_1132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1124_, v_a_1130_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_m_1129_);
lean_dec(v_x_1125_);
lean_inc(v_a_1130_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_a_1130_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; uint8_t v___y_1138_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_nat_dec_eq(v_m_1129_, v___x_1134_);
v___x_1136_ = lean_nat_sub(v_m_1129_, v___x_1128_);
lean_dec(v_m_1129_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_nat_dec_lt(v___x_1136_, v_x_1125_);
v___y_1138_ = v___x_1141_;
goto v___jp_1137_;
}
else
{
v___y_1138_ = v___x_1135_;
goto v___jp_1137_;
}
v___jp_1137_:
{
if (v___y_1138_ == 0)
{
v_x_1126_ = v___x_1136_;
goto _start;
}
else
{
lean_object* v___x_1140_; 
lean_dec(v___x_1136_);
lean_dec(v_x_1125_);
v___x_1140_ = lean_box(0);
return v___x_1140_;
}
}
}
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
lean_dec(v_x_1125_);
v___x_1142_ = lean_nat_add(v_m_1129_, v___x_1128_);
lean_dec(v_m_1129_);
v___x_1143_ = lean_nat_dec_le(v___x_1142_, v_x_1126_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec(v___x_1142_);
lean_dec(v_x_1126_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
else
{
v_x_1125_ = v___x_1142_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1146_, lean_object* v_k_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1146_, v_k_1147_, v_x_1148_, v_x_1149_);
lean_dec_ref(v_k_1147_);
lean_dec_ref(v_as_1146_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1151_, lean_object* v_vals_1152_, lean_object* v_i_1153_, lean_object* v_k_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_array_get_size(v_keys_1151_);
v___x_1156_ = lean_nat_dec_lt(v_i_1153_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v_i_1153_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
lean_object* v_k_x27_1158_; uint8_t v___x_1159_; 
v_k_x27_1158_ = lean_array_fget_borrowed(v_keys_1151_, v_i_1153_);
v___x_1159_ = lean_name_eq(v_k_1154_, v_k_x27_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_i_1153_, v___x_1160_);
lean_dec(v_i_1153_);
v_i_1153_ = v___x_1161_;
goto _start;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_array_fget_borrowed(v_vals_1152_, v_i_1153_);
lean_dec(v_i_1153_);
lean_inc(v___x_1163_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_i_1167_, lean_object* v_k_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1165_, v_vals_1166_, v_i_1167_, v_k_1168_);
lean_dec(v_k_1168_);
lean_dec_ref(v_vals_1166_);
lean_dec_ref(v_keys_1165_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1170_, size_t v_x_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1170_) == 0)
{
lean_object* v_es_1173_; lean_object* v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v_j_1177_; lean_object* v___x_1178_; 
v_es_1173_ = lean_ctor_get(v_x_1170_, 0);
v___x_1174_ = lean_box(2);
v___x_1175_ = ((size_t)31ULL);
v___x_1176_ = lean_usize_land(v_x_1171_, v___x_1175_);
v_j_1177_ = lean_usize_to_nat(v___x_1176_);
v___x_1178_ = lean_array_get_borrowed(v___x_1174_, v_es_1173_, v_j_1177_);
lean_dec(v_j_1177_);
switch(lean_obj_tag(v___x_1178_))
{
case 0:
{
lean_object* v_key_1179_; lean_object* v_val_1180_; uint8_t v___x_1181_; 
v_key_1179_ = lean_ctor_get(v___x_1178_, 0);
v_val_1180_ = lean_ctor_get(v___x_1178_, 1);
v___x_1181_ = lean_name_eq(v_x_1172_, v_key_1179_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
lean_inc(v_val_1180_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_val_1180_);
return v___x_1183_;
}
}
case 1:
{
lean_object* v_node_1184_; size_t v___x_1185_; size_t v___x_1186_; 
v_node_1184_ = lean_ctor_get(v___x_1178_, 0);
v___x_1185_ = ((size_t)5ULL);
v___x_1186_ = lean_usize_shift_right(v_x_1171_, v___x_1185_);
v_x_1170_ = v_node_1184_;
v_x_1171_ = v___x_1186_;
goto _start;
}
default: 
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
}
}
else
{
lean_object* v_ks_1189_; lean_object* v_vs_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_ks_1189_ = lean_ctor_get(v_x_1170_, 0);
v_vs_1190_ = lean_ctor_get(v_x_1170_, 1);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1189_, v_vs_1190_, v___x_1191_, v_x_1172_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
size_t v_x_439__boxed_1196_; lean_object* v_res_1197_; 
v_x_439__boxed_1196_ = lean_unbox_usize(v_x_1194_);
lean_dec(v_x_1194_);
v_res_1197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1193_, v_x_439__boxed_1196_, v_x_1195_);
lean_dec(v_x_1195_);
lean_dec_ref(v_x_1193_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
uint64_t v___y_1201_; 
if (lean_obj_tag(v_x_1199_) == 0)
{
uint64_t v___x_1204_; 
v___x_1204_ = 1723ULL;
v___y_1201_ = v___x_1204_;
goto v___jp_1200_;
}
else
{
uint64_t v_hash_1205_; 
v_hash_1205_ = lean_ctor_get_uint64(v_x_1199_, sizeof(void*)*2);
v___y_1201_ = v_hash_1205_;
goto v___jp_1200_;
}
v___jp_1200_:
{
size_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_uint64_to_usize(v___y_1201_);
v___x_1203_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1198_, v___x_1202_, v_x_1199_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1206_, v_x_1207_);
lean_dec(v_x_1207_);
lean_dec_ref(v_x_1206_);
return v_res_1208_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1212_, lean_object* v_declName_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1224_; 
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1216_ = l_Lean_IR_declMapExt;
v___x_1224_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1212_, v_declName_1213_);
if (lean_obj_tag(v___x_1224_) == 0)
{
goto v___jp_1217_;
}
else
{
lean_object* v_val_1225_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1239_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1215_, v___x_1216_, v_env_1212_, v_val_1225_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_array_get_size(v___x_1239_);
v___x_1242_ = lean_nat_dec_lt(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v___x_1239_);
goto v___jp_1226_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_sub(v___x_1241_, v___x_1243_);
v___x_1245_ = lean_nat_dec_le(v___x_1240_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec(v___x_1244_);
lean_dec_ref(v___x_1239_);
goto v___jp_1226_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_tmpDecl_1248_; lean_object* v___x_1249_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1247_ = lean_box(0);
lean_inc(v_declName_1213_);
v_tmpDecl_1248_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1248_, 0, v_declName_1213_);
lean_ctor_set(v_tmpDecl_1248_, 1, v___x_1246_);
lean_ctor_set(v_tmpDecl_1248_, 2, v___x_1247_);
lean_ctor_set(v_tmpDecl_1248_, 3, v___x_1214_);
v___x_1249_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1239_, v_tmpDecl_1248_, v___x_1240_, v___x_1244_);
lean_dec_ref_known(v_tmpDecl_1248_, 4);
lean_dec_ref(v___x_1239_);
if (lean_obj_tag(v___x_1249_) == 0)
{
goto v___jp_1226_;
}
else
{
lean_dec(v_val_1225_);
lean_dec(v_declName_1213_);
lean_dec_ref(v_env_1212_);
return v___x_1249_;
}
}
}
v___jp_1226_:
{
uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1227_ = 0;
v___x_1228_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1215_, v___x_1216_, v_env_1212_, v_val_1225_, v___x_1227_);
lean_dec(v_val_1225_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_array_get_size(v___x_1228_);
v___x_1231_ = lean_nat_dec_lt(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec_ref(v___x_1228_);
goto v___jp_1217_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_sub(v___x_1230_, v___x_1232_);
v___x_1234_ = lean_nat_dec_le(v___x_1229_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v___x_1233_);
lean_dec_ref(v___x_1228_);
goto v___jp_1217_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_tmpDecl_1237_; lean_object* v___x_1238_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1236_ = lean_box(0);
lean_inc(v_declName_1213_);
v_tmpDecl_1237_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1237_, 0, v_declName_1213_);
lean_ctor_set(v_tmpDecl_1237_, 1, v___x_1235_);
lean_ctor_set(v_tmpDecl_1237_, 2, v___x_1236_);
lean_ctor_set(v_tmpDecl_1237_, 3, v___x_1214_);
v___x_1238_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1228_, v_tmpDecl_1237_, v___x_1229_, v___x_1233_);
lean_dec_ref_known(v_tmpDecl_1237_, 4);
lean_dec_ref(v___x_1228_);
if (lean_obj_tag(v___x_1238_) == 0)
{
goto v___jp_1217_;
}
else
{
lean_dec(v_declName_1213_);
lean_dec_ref(v_env_1212_);
return v___x_1238_;
}
}
}
}
}
v___jp_1217_:
{
lean_object* v_toEnvExtension_1218_; lean_object* v_asyncMode_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_snd_1222_; lean_object* v___x_1223_; 
v_toEnvExtension_1218_ = lean_ctor_get(v___x_1216_, 0);
v_asyncMode_1219_ = lean_ctor_get(v_toEnvExtension_1218_, 2);
v___x_1220_ = lean_box(0);
v___x_1221_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1215_, v___x_1216_, v_env_1212_, v_asyncMode_1219_, v___x_1220_);
v_snd_1222_ = lean_ctor_get(v___x_1221_, 1);
lean_inc(v_snd_1222_);
lean_dec(v___x_1221_);
v___x_1223_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1222_, v_declName_1213_);
lean_dec(v_declName_1213_);
lean_dec(v_snd_1222_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1251_, v_x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1254_, v_x_1255_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec_ref(v_x_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1258_, lean_object* v_k_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1258_, v_k_1259_, v_x_1260_, v_x_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1264_, lean_object* v_k_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1264_, v_k_1265_, v_x_1266_, v_x_1267_, v_x_1268_);
lean_dec_ref(v_k_1265_);
lean_dec_ref(v_as_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1270_, lean_object* v_x_1271_, size_t v_x_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1271_, v_x_1272_, v_x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
size_t v_x_599__boxed_1279_; lean_object* v_res_1280_; 
v_x_599__boxed_1279_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_res_1280_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1275_, v_x_1276_, v_x_599__boxed_1279_, v_x_1278_);
lean_dec(v_x_1278_);
lean_dec_ref(v_x_1276_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1281_, lean_object* v_keys_1282_, lean_object* v_vals_1283_, lean_object* v_heq_1284_, lean_object* v_i_1285_, lean_object* v_k_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1282_, v_vals_1283_, v_i_1285_, v_k_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1288_, lean_object* v_keys_1289_, lean_object* v_vals_1290_, lean_object* v_heq_1291_, lean_object* v_i_1292_, lean_object* v_k_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1288_, v_keys_1289_, v_vals_1290_, v_heq_1291_, v_i_1292_, v_k_1293_);
lean_dec(v_k_1293_);
lean_dec_ref(v_vals_1290_);
lean_dec_ref(v_keys_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1295_, lean_object* v_declName_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1298_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1295_, v_declName_1296_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; lean_object* v_toEnvExtension_1300_; lean_object* v_asyncMode_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1299_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1300_ = lean_ctor_get(v___x_1299_, 0);
v_asyncMode_1301_ = lean_ctor_get(v_toEnvExtension_1300_, 2);
v___x_1302_ = lean_box(0);
v___x_1303_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1297_, v___x_1299_, v_env_1295_, v_asyncMode_1301_, v___x_1302_);
v___x_1304_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1303_, v_declName_1296_);
lean_dec(v_declName_1296_);
lean_dec(v___x_1303_);
return v___x_1304_;
}
else
{
lean_object* v_val_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___y_1310_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_val_1305_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1305_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1308_ = l_Lean_IR_declMapExt;
v___x_1323_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1307_, v___x_1308_, v_env_1295_, v_val_1305_);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v___x_1323_);
v___x_1326_ = lean_nat_dec_lt(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec_ref(v___x_1323_);
v___x_1327_ = lean_box(0);
v___y_1310_ = v___x_1327_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_sub(v___x_1325_, v___x_1328_);
v___x_1330_ = lean_nat_dec_le(v___x_1324_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1323_);
v___x_1331_ = lean_box(0);
v___y_1310_ = v___x_1331_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_tmpDecl_1334_; lean_object* v___x_1335_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1333_ = lean_box(0);
lean_inc(v_declName_1296_);
v_tmpDecl_1334_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1334_, 0, v_declName_1296_);
lean_ctor_set(v_tmpDecl_1334_, 1, v___x_1332_);
lean_ctor_set(v_tmpDecl_1334_, 2, v___x_1333_);
lean_ctor_set(v_tmpDecl_1334_, 3, v___x_1306_);
v___x_1335_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1323_, v_tmpDecl_1334_, v___x_1324_, v___x_1329_);
lean_dec_ref_known(v_tmpDecl_1334_, 4);
lean_dec_ref(v___x_1323_);
if (lean_obj_tag(v___x_1335_) == 0)
{
v___y_1310_ = v___x_1335_;
goto v___jp_1309_;
}
else
{
lean_dec(v_val_1305_);
lean_dec(v_declName_1296_);
lean_dec_ref(v_env_1295_);
return v___x_1335_;
}
}
}
v___jp_1309_:
{
uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1311_ = 0;
v___x_1312_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1307_, v___x_1308_, v_env_1295_, v_val_1305_, v___x_1311_);
lean_dec(v_val_1305_);
lean_dec_ref(v_env_1295_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_array_get_size(v___x_1312_);
v___x_1315_ = lean_nat_dec_lt(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v___x_1312_);
lean_dec(v_declName_1296_);
return v___y_1310_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_sub(v___x_1314_, v___x_1316_);
v___x_1318_ = lean_nat_dec_le(v___x_1313_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1312_);
lean_dec(v_declName_1296_);
return v___y_1310_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_tmpDecl_1321_; lean_object* v___x_1322_; 
lean_dec(v___y_1310_);
v___x_1319_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1320_ = lean_box(0);
v_tmpDecl_1321_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1321_, 0, v_declName_1296_);
lean_ctor_set(v_tmpDecl_1321_, 1, v___x_1319_);
lean_ctor_set(v_tmpDecl_1321_, 2, v___x_1320_);
lean_ctor_set(v_tmpDecl_1321_, 3, v___x_1306_);
v___x_1322_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1312_, v_tmpDecl_1321_, v___x_1313_, v___x_1317_);
lean_dec_ref_known(v_tmpDecl_1321_, 4);
lean_dec_ref(v___x_1312_);
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1336_, lean_object* v_declName_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v_boxed_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
lean_inc(v_declName_1337_);
v_boxed_1339_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1337_);
v___x_1340_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1336_, v_declName_1337_);
lean_dec(v_declName_1337_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1341_; lean_object* v_toEnvExtension_1342_; lean_object* v_asyncMode_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1342_ = lean_ctor_get(v___x_1341_, 0);
v_asyncMode_1343_ = lean_ctor_get(v_toEnvExtension_1342_, 2);
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1338_, v___x_1341_, v_env_1336_, v_asyncMode_1343_, v___x_1344_);
v___x_1346_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1345_, v_boxed_1339_);
lean_dec(v_boxed_1339_);
lean_dec(v___x_1345_);
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___y_1352_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_val_1347_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_val_1347_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1350_ = l_Lean_IR_declMapExt;
v___x_1365_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1349_, v___x_1350_, v_env_1336_, v_val_1347_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_get_size(v___x_1365_);
v___x_1368_ = lean_nat_dec_lt(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec_ref(v___x_1365_);
v___x_1369_ = lean_box(0);
v___y_1352_ = v___x_1369_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_sub(v___x_1367_, v___x_1370_);
v___x_1372_ = lean_nat_dec_le(v___x_1366_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_dec(v___x_1371_);
lean_dec_ref(v___x_1365_);
v___x_1373_ = lean_box(0);
v___y_1352_ = v___x_1373_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_tmpDecl_1376_; lean_object* v___x_1377_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1375_ = lean_box(0);
lean_inc(v_boxed_1339_);
v_tmpDecl_1376_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1376_, 0, v_boxed_1339_);
lean_ctor_set(v_tmpDecl_1376_, 1, v___x_1374_);
lean_ctor_set(v_tmpDecl_1376_, 2, v___x_1375_);
lean_ctor_set(v_tmpDecl_1376_, 3, v___x_1348_);
v___x_1377_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1365_, v_tmpDecl_1376_, v___x_1366_, v___x_1371_);
lean_dec_ref_known(v_tmpDecl_1376_, 4);
lean_dec_ref(v___x_1365_);
if (lean_obj_tag(v___x_1377_) == 0)
{
v___y_1352_ = v___x_1377_;
goto v___jp_1351_;
}
else
{
lean_dec(v_val_1347_);
lean_dec(v_boxed_1339_);
lean_dec_ref(v_env_1336_);
return v___x_1377_;
}
}
}
v___jp_1351_:
{
uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1353_ = 0;
v___x_1354_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1349_, v___x_1350_, v_env_1336_, v_val_1347_, v___x_1353_);
lean_dec(v_val_1347_);
lean_dec_ref(v_env_1336_);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_array_get_size(v___x_1354_);
v___x_1357_ = lean_nat_dec_lt(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec_ref(v___x_1354_);
lean_dec(v_boxed_1339_);
return v___y_1352_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_sub(v___x_1356_, v___x_1358_);
v___x_1360_ = lean_nat_dec_le(v___x_1355_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_dec(v___x_1359_);
lean_dec_ref(v___x_1354_);
lean_dec(v_boxed_1339_);
return v___y_1352_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_tmpDecl_1363_; lean_object* v___x_1364_; 
lean_dec(v___y_1352_);
v___x_1361_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1362_ = lean_box(0);
v_tmpDecl_1363_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1363_, 0, v_boxed_1339_);
lean_ctor_set(v_tmpDecl_1363_, 1, v___x_1361_);
lean_ctor_set(v_tmpDecl_1363_, 2, v___x_1362_);
lean_ctor_set(v_tmpDecl_1363_, 3, v___x_1348_);
v___x_1364_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1354_, v_tmpDecl_1363_, v___x_1355_, v___x_1359_);
lean_dec_ref_known(v_tmpDecl_1363_, 4);
lean_dec_ref(v___x_1354_);
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1378_, lean_object* v_constName_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1378_, v_constName_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; lean_object* v_toEnvExtension_1382_; lean_object* v_asyncMode_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1381_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1382_ = lean_ctor_get(v___x_1381_, 0);
v_asyncMode_1383_ = lean_ctor_get(v_toEnvExtension_1382_, 2);
v___x_1384_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1384_, v___x_1381_, v_env_1378_, v_asyncMode_1383_, v___x_1385_);
v___x_1387_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1386_, v_constName_1379_);
lean_dec(v_constName_1379_);
lean_dec(v___x_1386_);
if (v___x_1387_ == 0)
{
uint8_t v___x_1388_; 
v___x_1388_ = 1;
return v___x_1388_;
}
else
{
uint8_t v___x_1389_; 
v___x_1389_ = 0;
return v___x_1389_;
}
}
else
{
uint8_t v___x_1390_; 
lean_dec_ref_known(v___x_1380_, 1);
lean_dec(v_constName_1379_);
lean_dec_ref(v_env_1378_);
v___x_1390_ = 0;
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1391_, lean_object* v_constName_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = lean_has_compile_error(v_env_1391_, v_constName_1392_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v_env_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_st_ref_get(v_a_1396_);
v_env_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc_ref(v_env_1399_);
lean_dec(v___x_1398_);
v___x_1400_ = l_Lean_IR_findEnvDecl(v_env_1399_, v_n_1395_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_IR_findDecl___redArg(v_n_1402_, v_a_1403_);
lean_dec(v_a_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_IR_findDecl___redArg(v_n_1406_, v_a_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_IR_findDecl(v_n_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1434_; 
v___x_1419_ = l_Lean_IR_findDecl___redArg(v_n_1416_, v_a_1417_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1434_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1434_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
if (lean_obj_tag(v_a_1420_) == 0)
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = 0;
v___x_1425_ = lean_box(v___x_1424_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1425_);
v___x_1427_ = v___x_1422_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec_ref_known(v_a_1420_, 1);
v___x_1429_ = 1;
v___x_1430_ = lean_box(v___x_1429_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1430_);
v___x_1432_ = v___x_1422_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_IR_containsDecl___redArg(v_n_1435_, v_a_1436_);
lean_dec(v_a_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_IR_containsDecl___redArg(v_n_1439_, v_a_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_IR_containsDecl(v_n_1444_, v_a_1445_, v_a_1446_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_ref_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_ref_1453_ = lean_ctor_get(v___y_1450_, 2);
v___x_1454_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1449_, v___y_1450_, v___y_1451_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_inc(v_ref_1453_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_ref_1453_);
lean_ctor_set(v___x_1459_, 1, v_a_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 1);
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1493_; 
lean_inc(v_n_1471_);
v___x_1475_ = l_Lean_IR_findDecl___redArg(v_n_1471_, v_a_1473_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1493_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1493_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
if (lean_obj_tag(v_a_1476_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1482_; 
lean_dec(v_n_1471_);
v_val_1480_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v_a_1476_, 1);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v_val_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_val_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_del_object(v___x_1478_);
lean_dec(v_a_1476_);
v___x_1484_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1485_ = 1;
v___x_1486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1471_, v___x_1485_);
v___x_1487_ = lean_string_append(v___x_1484_, v___x_1486_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1489_ = lean_string_append(v___x_1487_, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
v___x_1491_ = l_Lean_MessageData_ofFormat(v___x_1490_);
v___x_1492_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1491_, v_a_1472_, v_a_1473_);
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_IR_getDecl(v_n_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1500_, v___y_1501_, v___y_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1505_, v_msg_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_env_1516_; lean_object* v___x_1517_; lean_object* v_toEnvExtension_1518_; lean_object* v_asyncMode_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1514_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1515_ = lean_st_ref_get(v_a_1512_);
v_env_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc_ref(v_env_1516_);
lean_dec(v___x_1515_);
v___x_1517_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1518_ = lean_ctor_get(v___x_1517_, 0);
v_asyncMode_1519_ = lean_ctor_get(v_toEnvExtension_1518_, 2);
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1514_, v___x_1517_, v_env_1516_, v_asyncMode_1519_, v___x_1520_);
v___x_1522_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1521_, v_n_1511_);
lean_dec(v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_IR_findLocalDecl___redArg(v_n_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec(v_n_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_IR_findLocalDecl___redArg(v_n_1528_, v_a_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_IR_findLocalDecl(v_n_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_n_1533_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v_toEnvExtension_1540_; lean_object* v_asyncMode_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1539_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1540_ = lean_ctor_get(v___x_1539_, 0);
v_asyncMode_1541_ = lean_ctor_get(v_toEnvExtension_1540_, 2);
v___x_1542_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1543_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1542_, v___x_1539_, v_env_1538_, v_asyncMode_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v_env_1552_; lean_object* v_nextMacroScope_1553_; lean_object* v_ngen_1554_; lean_object* v_auxDeclNGen_1555_; lean_object* v_traceState_1556_; lean_object* v_recordedDeps_1557_; lean_object* v_messages_1558_; lean_object* v_infoState_1559_; lean_object* v_snapshotTasks_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1576_; 
v___x_1551_ = lean_st_ref_take(v_a_1549_);
v_env_1552_ = lean_ctor_get(v___x_1551_, 0);
v_nextMacroScope_1553_ = lean_ctor_get(v___x_1551_, 1);
v_ngen_1554_ = lean_ctor_get(v___x_1551_, 2);
v_auxDeclNGen_1555_ = lean_ctor_get(v___x_1551_, 3);
v_traceState_1556_ = lean_ctor_get(v___x_1551_, 4);
v_recordedDeps_1557_ = lean_ctor_get(v___x_1551_, 6);
v_messages_1558_ = lean_ctor_get(v___x_1551_, 7);
v_infoState_1559_ = lean_ctor_get(v___x_1551_, 8);
v_snapshotTasks_1560_ = lean_ctor_get(v___x_1551_, 9);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1551_, 5);
lean_dec(v_unused_1577_);
v___x_1562_ = v___x_1551_;
v_isShared_1563_ = v_isSharedCheck_1576_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snapshotTasks_1560_);
lean_inc(v_infoState_1559_);
lean_inc(v_messages_1558_);
lean_inc(v_recordedDeps_1557_);
lean_inc(v_traceState_1556_);
lean_inc(v_auxDeclNGen_1555_);
lean_inc(v_ngen_1554_);
lean_inc(v_nextMacroScope_1553_);
lean_inc(v_env_1552_);
lean_dec(v___x_1551_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1576_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v_toEnvExtension_1565_; lean_object* v_asyncMode_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1564_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1565_ = lean_ctor_get(v___x_1564_, 0);
v_asyncMode_1566_ = lean_ctor_get(v_toEnvExtension_1565_, 2);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_box(0);
v___x_1569_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1564_, v_env_1552_, v_decl_1548_, v_asyncMode_1566_, v___x_1568_);
v___x_1570_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 5, v___x_1570_);
lean_ctor_set(v___x_1562_, 0, v___x_1569_);
v___x_1572_ = v___x_1562_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_nextMacroScope_1553_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_ngen_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_auxDeclNGen_1555_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_traceState_1556_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_recordedDeps_1557_);
lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_messages_1558_);
lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_infoState_1559_);
lean_ctor_set(v_reuseFailAlloc_1575_, 9, v_snapshotTasks_1560_);
v___x_1572_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_st_ref_put(v_a_1549_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1567_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_IR_addDecl___redArg(v_decl_1578_, v_a_1579_);
lean_dec(v_a_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_IR_addDecl___redArg(v_decl_1582_, v_a_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_IR_addDecl(v_decl_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1592_, size_t v_i_1593_, size_t v_stop_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_eq(v_i_1593_, v_stop_1594_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_array_uget_borrowed(v_as_1592_, v_i_1593_);
lean_inc(v___x_1599_);
v___x_1600_ = l_Lean_IR_addDecl___redArg(v___x_1599_, v___y_1596_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; size_t v___x_1602_; size_t v___x_1603_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = ((size_t)1ULL);
v___x_1603_ = lean_usize_add(v_i_1593_, v___x_1602_);
v_i_1593_ = v___x_1603_;
v_b_1595_ = v_a_1601_;
goto _start;
}
else
{
return v___x_1600_;
}
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_b_1595_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1606_, lean_object* v_i_1607_, lean_object* v_stop_1608_, lean_object* v_b_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
size_t v_i_boxed_1612_; size_t v_stop_boxed_1613_; lean_object* v_res_1614_; 
v_i_boxed_1612_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_stop_boxed_1613_ = lean_unbox_usize(v_stop_1608_);
lean_dec(v_stop_1608_);
v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1606_, v_i_boxed_1612_, v_stop_boxed_1613_, v_b_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v_as_1606_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_array_get_size(v_decls_1615_);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_nat_dec_lt(v___x_1619_, v___x_1620_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
return v___x_1623_;
}
else
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_le(v___x_1620_, v___x_1620_);
if (v___x_1624_ == 0)
{
if (v___x_1622_ == 0)
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1621_);
return v___x_1625_;
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1620_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1615_, v___x_1626_, v___x_1627_, v___x_1621_, v_a_1617_);
return v___x_1628_;
}
}
else
{
size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = lean_usize_of_nat(v___x_1620_);
v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1615_, v___x_1629_, v___x_1630_, v___x_1621_, v_a_1617_);
return v___x_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_IR_addDecls(v_decls_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec_ref(v_decls_1632_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1637_, size_t v_i_1638_, size_t v_stop_1639_, lean_object* v_b_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1637_, v_i_1638_, v_stop_1639_, v_b_1640_, v___y_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1645_, lean_object* v_i_1646_, lean_object* v_stop_1647_, lean_object* v_b_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
size_t v_i_boxed_1652_; size_t v_stop_boxed_1653_; lean_object* v_res_1654_; 
v_i_boxed_1652_ = lean_unbox_usize(v_i_1646_);
lean_dec(v_i_1646_);
v_stop_boxed_1653_ = lean_unbox_usize(v_stop_1647_);
lean_dec(v_stop_1647_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1645_, v_i_boxed_1652_, v_stop_boxed_1653_, v_b_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_as_1645_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1658_, lean_object* v_as_1659_, size_t v_sz_1660_, size_t v_i_1661_, lean_object* v_b_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_usize_dec_lt(v_i_1661_, v_sz_1660_);
if (v___x_1663_ == 0)
{
lean_inc_ref(v_b_1662_);
return v_b_1662_;
}
else
{
lean_object* v___x_1664_; lean_object* v_a_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1664_ = lean_box(0);
v_a_1665_ = lean_array_uget_borrowed(v_as_1659_, v_i_1661_);
v___x_1666_ = l_Lean_IR_Decl_name(v_a_1665_);
v___x_1667_ = lean_name_eq(v___x_1666_, v_n_1658_);
lean_dec(v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; size_t v___x_1669_; size_t v___x_1670_; 
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1669_ = ((size_t)1ULL);
v___x_1670_ = lean_usize_add(v_i_1661_, v___x_1669_);
v_i_1661_ = v___x_1670_;
v_b_1662_ = v___x_1668_;
goto _start;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_inc(v_a_1665_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_a_1665_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v___x_1664_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1675_, lean_object* v_as_1676_, lean_object* v_sz_1677_, lean_object* v_i_1678_, lean_object* v_b_1679_){
_start:
{
size_t v_sz_boxed_1680_; size_t v_i_boxed_1681_; lean_object* v_res_1682_; 
v_sz_boxed_1680_ = lean_unbox_usize(v_sz_1677_);
lean_dec(v_sz_1677_);
v_i_boxed_1681_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1675_, v_as_1676_, v_sz_boxed_1680_, v_i_boxed_1681_, v_b_1679_);
lean_dec_ref(v_b_1679_);
lean_dec_ref(v_as_1676_);
lean_dec(v_n_1675_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1683_, lean_object* v_n_1684_, lean_object* v_decls_1685_){
_start:
{
lean_object* v___x_1686_; size_t v_sz_1687_; size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v_fst_1690_; 
v___x_1686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1687_ = lean_array_size(v_decls_1685_);
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1684_, v_decls_1685_, v_sz_1687_, v___x_1688_, v___x_1686_);
v_fst_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_fst_1690_);
lean_dec_ref(v___x_1689_);
if (lean_obj_tag(v_fst_1690_) == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_IR_findEnvDecl(v_env_1683_, v_n_1684_);
return v___x_1691_;
}
else
{
lean_object* v_val_1692_; 
v_val_1692_ = lean_ctor_get(v_fst_1690_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v_fst_1690_, 1);
if (lean_obj_tag(v_val_1692_) == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_IR_findEnvDecl(v_env_1683_, v_n_1684_);
return v___x_1693_;
}
else
{
lean_dec(v_n_1684_);
lean_dec_ref(v_env_1683_);
return v_val_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1694_, lean_object* v_n_1695_, lean_object* v_decls_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_IR_findEnvDecl_x27(v_env_1694_, v_n_1695_, v_decls_1696_);
lean_dec_ref(v_decls_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1698_, lean_object* v_decls_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v_env_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_st_ref_get(v_a_1700_);
v_env_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_env_1703_);
lean_dec(v___x_1702_);
v___x_1704_ = l_Lean_IR_findEnvDecl_x27(v_env_1703_, v_n_1698_, v_decls_1699_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1706_, lean_object* v_decls_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_IR_findDecl_x27___redArg(v_n_1706_, v_decls_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_decls_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1711_, lean_object* v_decls_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_IR_findDecl_x27___redArg(v_n_1711_, v_decls_1712_, v_a_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1717_, lean_object* v_decls_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_IR_findDecl_x27(v_n_1717_, v_decls_1718_, v_a_1719_, v_a_1720_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec_ref(v_decls_1718_);
return v_res_1722_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1723_, lean_object* v_as_1724_, size_t v_i_1725_, size_t v_stop_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_eq(v_i_1725_, v_stop_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1728_ = lean_array_uget_borrowed(v_as_1724_, v_i_1725_);
v___x_1729_ = l_Lean_IR_Decl_name(v___x_1728_);
v___x_1730_ = lean_name_eq(v___x_1729_, v_n_1723_);
lean_dec(v___x_1729_);
if (v___x_1730_ == 0)
{
size_t v___x_1731_; size_t v___x_1732_; 
v___x_1731_ = ((size_t)1ULL);
v___x_1732_ = lean_usize_add(v_i_1725_, v___x_1731_);
v_i_1725_ = v___x_1732_;
goto _start;
}
else
{
return v___x_1730_;
}
}
else
{
uint8_t v___x_1734_; 
v___x_1734_ = 0;
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1735_, lean_object* v_as_1736_, lean_object* v_i_1737_, lean_object* v_stop_1738_){
_start:
{
size_t v_i_boxed_1739_; size_t v_stop_boxed_1740_; uint8_t v_res_1741_; lean_object* v_r_1742_; 
v_i_boxed_1739_ = lean_unbox_usize(v_i_1737_);
lean_dec(v_i_1737_);
v_stop_boxed_1740_ = lean_unbox_usize(v_stop_1738_);
lean_dec(v_stop_1738_);
v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1735_, v_as_1736_, v_i_boxed_1739_, v_stop_boxed_1740_);
lean_dec_ref(v_as_1736_);
lean_dec(v_n_1735_);
v_r_1742_ = lean_box(v_res_1741_);
return v_r_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1743_, lean_object* v_decls_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_array_get_size(v_decls_1744_);
v___x_1749_ = lean_nat_dec_lt(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_IR_containsDecl___redArg(v_n_1743_, v_a_1745_);
return v___x_1750_;
}
else
{
if (v___x_1749_ == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_IR_containsDecl___redArg(v_n_1743_, v_a_1745_);
return v___x_1751_;
}
else
{
size_t v___x_1752_; size_t v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_of_nat(v___x_1748_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1743_, v_decls_1744_, v___x_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_IR_containsDecl___redArg(v_n_1743_, v_a_1745_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_n_1743_);
v___x_1756_ = lean_box(v___x_1749_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1758_, lean_object* v_decls_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1758_, v_decls_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_decls_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1763_, lean_object* v_decls_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1763_, v_decls_1764_, v_a_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1769_, lean_object* v_decls_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_IR_containsDecl_x27(v_n_1769_, v_decls_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec_ref(v_decls_1770_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1775_, lean_object* v_decls_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___x_1780_; lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1798_; 
lean_inc(v_n_1775_);
v___x_1780_ = l_Lean_IR_findDecl_x27___redArg(v_n_1775_, v_decls_1776_, v_a_1778_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1798_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1798_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
if (lean_obj_tag(v_a_1781_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1787_; 
lean_dec(v_n_1775_);
v_val_1785_ = lean_ctor_get(v_a_1781_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v_a_1781_, 1);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_val_1785_);
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_val_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_del_object(v___x_1783_);
lean_dec(v_a_1781_);
v___x_1789_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1790_ = 1;
v___x_1791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1775_, v___x_1790_);
v___x_1792_ = lean_string_append(v___x_1789_, v___x_1791_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
v___x_1796_ = l_Lean_MessageData_ofFormat(v___x_1795_);
v___x_1797_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1796_, v_a_1777_, v_a_1778_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1799_, lean_object* v_decls_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_IR_getDecl_x27(v_n_1799_, v_decls_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec_ref(v_decls_1800_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1805_, lean_object* v_declName_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_IR_findEnvDecl(v_env_1805_, v_declName_1806_);
if (lean_obj_tag(v___x_1807_) == 1)
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v___x_1807_, 1);
if (lean_obj_tag(v_val_1808_) == 0)
{
lean_object* v_info_1809_; 
v_info_1809_ = lean_ctor_get(v_val_1808_, 4);
lean_inc(v_info_1809_);
lean_dec_ref_known(v_val_1808_, 5);
return v_info_1809_;
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_val_1808_);
v___x_1810_ = lean_box(0);
return v___x_1810_;
}
}
else
{
lean_object* v___x_1811_; 
lean_dec(v___x_1807_);
v___x_1811_ = lean_box(0);
return v___x_1811_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___closed__0(void){
_start:
{
uint8_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = 2;
v___x_1813_ = l_Lean_OLeanLevel_ctorIdx(v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(uint8_t v_level_1814_, lean_object* v_env_1815_, uint8_t v_includeDecls_1816_, lean_object* v_as_1817_, size_t v_i_1818_, size_t v_stop_1819_, lean_object* v_b_1820_){
_start:
{
lean_object* v___y_1822_; uint8_t v___x_1826_; 
v___x_1826_ = lean_usize_dec_eq(v_i_1818_, v_stop_1819_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___y_1829_; 
v___x_1827_ = lean_array_uget_borrowed(v_as_1817_, v_i_1818_);
if (v_includeDecls_1816_ == 0)
{
uint8_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = 1;
lean_inc(v___x_1827_);
lean_inc_ref(v_env_1815_);
v___x_1839_ = l_Lean_Environment_contains(v_env_1815_, v___x_1827_, v___x_1838_);
if (v___x_1839_ == 0)
{
goto v___jp_1831_;
}
else
{
v___y_1822_ = v_b_1820_;
goto v___jp_1821_;
}
}
else
{
goto v___jp_1831_;
}
v___jp_1828_:
{
if (v___y_1829_ == 0)
{
v___y_1822_ = v_b_1820_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1830_; 
lean_inc(v___x_1827_);
v___x_1830_ = lean_array_push(v_b_1820_, v___x_1827_);
v___y_1822_ = v___x_1830_;
goto v___jp_1821_;
}
}
v___jp_1831_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1832_ = l_Lean_OLeanLevel_ctorIdx(v_level_1814_);
v___x_1833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___closed__0);
v___x_1834_ = lean_nat_dec_eq(v___x_1832_, v___x_1833_);
lean_dec(v___x_1832_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; 
lean_inc_ref(v_env_1815_);
v___x_1835_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1815_, v___x_1827_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; 
lean_inc_ref(v_env_1815_);
v___x_1836_ = l_Lean_isDeclMeta(v_env_1815_, v___x_1827_);
v___y_1829_ = v___x_1836_;
goto v___jp_1828_;
}
else
{
v___y_1829_ = v___x_1835_;
goto v___jp_1828_;
}
}
else
{
lean_object* v___x_1837_; 
lean_inc(v___x_1827_);
v___x_1837_ = lean_array_push(v_b_1820_, v___x_1827_);
v___y_1822_ = v___x_1837_;
goto v___jp_1821_;
}
}
}
else
{
lean_dec_ref(v_env_1815_);
return v_b_1820_;
}
v___jp_1821_:
{
size_t v___x_1823_; size_t v___x_1824_; 
v___x_1823_ = ((size_t)1ULL);
v___x_1824_ = lean_usize_add(v_i_1818_, v___x_1823_);
v_i_1818_ = v___x_1824_;
v_b_1820_ = v___y_1822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_level_1840_, lean_object* v_env_1841_, lean_object* v_includeDecls_1842_, lean_object* v_as_1843_, lean_object* v_i_1844_, lean_object* v_stop_1845_, lean_object* v_b_1846_){
_start:
{
uint8_t v_level_boxed_1847_; uint8_t v_includeDecls_boxed_1848_; size_t v_i_boxed_1849_; size_t v_stop_boxed_1850_; lean_object* v_res_1851_; 
v_level_boxed_1847_ = lean_unbox(v_level_1840_);
v_includeDecls_boxed_1848_ = lean_unbox(v_includeDecls_1842_);
v_i_boxed_1849_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_stop_boxed_1850_ = lean_unbox_usize(v_stop_1845_);
lean_dec(v_stop_1845_);
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_boxed_1847_, v_env_1841_, v_includeDecls_boxed_1848_, v_as_1843_, v_i_boxed_1849_, v_stop_boxed_1850_, v_b_1846_);
lean_dec_ref(v_as_1843_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_bs_1854_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1855_ == 0)
{
return v_bs_1854_;
}
else
{
lean_object* v_v_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; lean_object* v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; lean_object* v___x_1862_; 
v_v_1856_ = lean_array_uget(v_bs_1854_, v_i_1853_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1854_, v_i_1853_, v___x_1857_);
v___x_1859_ = l_Lean_IR_Decl_name(v_v_1856_);
lean_dec(v_v_1856_);
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_add(v_i_1853_, v___x_1860_);
v___x_1862_ = lean_array_uset(v_bs_x27_1858_, v_i_1853_, v___x_1859_);
v_i_1853_ = v___x_1861_;
v_bs_1854_ = v___x_1862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1864_, lean_object* v_i_1865_, lean_object* v_bs_1866_){
_start:
{
size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1864_);
lean_dec(v_sz_1864_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1867_, v_i_boxed_1868_, v_bs_1866_);
return v_res_1869_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0(void){
_start:
{
uint8_t v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = 0;
v___x_1871_ = l_Lean_OLeanLevel_ctorIdx(v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1874_, uint8_t v_level_1875_, uint8_t v_includeDecls_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v_toEnvExtension_1878_; lean_object* v_asyncMode_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v_env_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; size_t v_sz_1887_; size_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1877_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1878_ = lean_ctor_get(v___x_1877_, 0);
v_asyncMode_1879_ = lean_ctor_get(v_toEnvExtension_1878_, 2);
v___x_1880_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1881_ = l_Lean_OLeanLevel_ctorIdx(v_level_1875_);
v___x_1882_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0);
v___x_1883_ = lean_nat_dec_eq(v___x_1881_, v___x_1882_);
lean_dec(v___x_1881_);
v_env_1884_ = l_Lean_Environment_setExporting(v_env_1874_, v___x_1883_);
lean_inc_ref(v_env_1884_);
v___x_1885_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1880_, v___x_1877_, v_env_1884_, v_asyncMode_1879_);
v___x_1886_ = lean_array_mk(v___x_1885_);
v_sz_1887_ = lean_array_size(v___x_1886_);
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1887_, v___x_1888_, v___x_1886_);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_array_get_size(v___x_1889_);
v___x_1892_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__1));
v___x_1893_ = lean_nat_dec_lt(v___x_1890_, v___x_1891_);
if (v___x_1893_ == 0)
{
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_env_1884_);
return v___x_1892_;
}
else
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_le(v___x_1891_, v___x_1891_);
if (v___x_1894_ == 0)
{
if (v___x_1893_ == 0)
{
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_env_1884_);
return v___x_1892_;
}
else
{
size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_usize_of_nat(v___x_1891_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1875_, v_env_1884_, v_includeDecls_1876_, v___x_1889_, v___x_1888_, v___x_1895_, v___x_1892_);
lean_dec_ref(v___x_1889_);
return v___x_1896_;
}
}
else
{
size_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_usize_of_nat(v___x_1891_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1875_, v_env_1884_, v_includeDecls_1876_, v___x_1889_, v___x_1888_, v___x_1897_, v___x_1892_);
lean_dec_ref(v___x_1889_);
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1899_, lean_object* v_level_1900_, lean_object* v_includeDecls_1901_){
_start:
{
uint8_t v_level_boxed_1902_; uint8_t v_includeDecls_boxed_1903_; lean_object* v_res_1904_; 
v_level_boxed_1902_ = lean_unbox(v_level_1900_);
v_includeDecls_boxed_1903_ = lean_unbox(v_includeDecls_1901_);
v_res_1904_ = lean_get_ir_extra_const_names(v_env_1899_, v_level_boxed_1902_, v_includeDecls_boxed_1903_);
return v_res_1904_;
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
