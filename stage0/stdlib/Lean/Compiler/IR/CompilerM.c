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
lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_246_; 
v_ref_200_ = lean_ctor_get(v___y_197_, 2);
v___x_201_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_196_, v___y_197_, v___y_198_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_246_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_246_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_246_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v_traceState_207_; lean_object* v_env_208_; lean_object* v_nextMacroScope_209_; lean_object* v_ngen_210_; lean_object* v_auxDeclNGen_211_; lean_object* v_cache_212_; lean_object* v_messages_213_; lean_object* v_infoState_214_; lean_object* v_snapshotTasks_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_245_; 
v___x_206_ = lean_st_ref_take(v___y_198_);
v_traceState_207_ = lean_ctor_get(v___x_206_, 4);
v_env_208_ = lean_ctor_get(v___x_206_, 0);
v_nextMacroScope_209_ = lean_ctor_get(v___x_206_, 1);
v_ngen_210_ = lean_ctor_get(v___x_206_, 2);
v_auxDeclNGen_211_ = lean_ctor_get(v___x_206_, 3);
v_cache_212_ = lean_ctor_get(v___x_206_, 5);
v_messages_213_ = lean_ctor_get(v___x_206_, 6);
v_infoState_214_ = lean_ctor_get(v___x_206_, 7);
v_snapshotTasks_215_ = lean_ctor_get(v___x_206_, 8);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_245_ == 0)
{
v___x_217_ = v___x_206_;
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snapshotTasks_215_);
lean_inc(v_infoState_214_);
lean_inc(v_messages_213_);
lean_inc(v_cache_212_);
lean_inc(v_traceState_207_);
lean_inc(v_auxDeclNGen_211_);
lean_inc(v_ngen_210_);
lean_inc(v_nextMacroScope_209_);
lean_inc(v_env_208_);
lean_dec(v___x_206_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint64_t v_tid_219_; lean_object* v_traces_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_244_; 
v_tid_219_ = lean_ctor_get_uint64(v_traceState_207_, sizeof(void*)*1);
v_traces_220_ = lean_ctor_get(v_traceState_207_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_traceState_207_);
if (v_isSharedCheck_244_ == 0)
{
v___x_222_ = v_traceState_207_;
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_traces_220_);
lean_dec(v_traceState_207_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; double v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_224_ = lean_box(0);
v___x_225_ = lean_box(0);
v___x_226_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_227_ = 0;
v___x_228_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_229_, 0, v_cls_195_);
lean_ctor_set(v___x_229_, 1, v___x_225_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_ctor_set_float(v___x_229_, sizeof(void*)*3, v___x_226_);
lean_ctor_set_float(v___x_229_, sizeof(void*)*3 + 8, v___x_226_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*3 + 16, v___x_227_);
v___x_230_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_231_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v_a_202_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_inc(v_ref_200_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_ref_200_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_Lean_PersistentArray_push___redArg(v_traces_220_, v___x_232_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_233_);
v___x_235_ = v___x_222_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_233_);
lean_ctor_set_uint64(v_reuseFailAlloc_243_, sizeof(void*)*1, v_tid_219_);
v___x_235_ = v_reuseFailAlloc_243_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v___x_235_);
v___x_237_ = v___x_217_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_env_208_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_nextMacroScope_209_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_ngen_210_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_auxDeclNGen_211_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_messages_213_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v_infoState_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_snapshotTasks_215_);
v___x_237_ = v_reuseFailAlloc_242_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_put(v___y_198_, v___x_237_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_224_);
v___x_240_ = v___x_204_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_224_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_247_, v_msg_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_263_ = l_Lean_IR_LogEntry_fmt(v_entry_258_);
v___x_264_ = l_Lean_MessageData_ofFormat(v___x_263_);
v___x_265_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_262_, v___x_264_, v_a_259_, v_a_260_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_IR_log(v_entry_266_, v_a_267_, v_a_268_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_270_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_279_, lean_object* v_optName_280_){
_start:
{
lean_object* v_map_281_; lean_object* v___x_288_; 
v_map_281_ = lean_ctor_get(v_opts_279_, 0);
v___x_288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_281_, v_optName_280_);
if (lean_obj_tag(v___x_288_) == 1)
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
goto v___jp_282_;
}
}
else
{
lean_dec(v___x_288_);
goto v___jp_282_;
}
v___jp_282_:
{
lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_284_ = 0;
v___x_285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_281_, v___x_283_);
if (lean_obj_tag(v___x_285_) == 0)
{
return v___x_284_;
}
else
{
lean_object* v_val_286_; 
v_val_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_285_, 1);
if (lean_obj_tag(v_val_286_) == 1)
{
uint8_t v_v_287_; 
v_v_287_ = lean_ctor_get_uint8(v_val_286_, 0);
lean_dec_ref_known(v_val_286_, 0);
return v_v_287_;
}
else
{
lean_dec(v_val_286_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_291_, lean_object* v_optName_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_291_, v_optName_292_);
lean_dec(v_optName_292_);
lean_dec_ref(v_opts_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_295_, lean_object* v_cls_296_, lean_object* v_decls_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_toCold_301_; lean_object* v_options_302_; uint8_t v___x_303_; 
v_toCold_301_ = lean_ctor_get(v_a_298_, 0);
v_options_302_ = lean_ctor_get(v_toCold_301_, 2);
v___x_303_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_302_, v_optName_295_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_decls_297_);
lean_dec(v_cls_296_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_cls_296_);
lean_ctor_set(v___x_306_, 1, v_decls_297_);
v___x_307_ = l_Lean_IR_log(v___x_306_, v_a_298_, v_a_299_);
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
lean_object* v_toCold_335_; lean_object* v_options_336_; uint8_t v___x_337_; 
v_toCold_335_ = lean_ctor_get(v_a_332_, 0);
v_options_336_ = lean_ctor_get(v_toCold_335_, 2);
v___x_337_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_336_, v_optName_330_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_a_331_);
lean_dec_ref(v_inst_329_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_apply_1(v_inst_329_, v_a_331_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = l_Lean_IR_log(v___x_341_, v_a_332_, v_a_333_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_343_, lean_object* v_optName_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_343_, v_optName_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_optName_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_350_, lean_object* v_inst_351_, lean_object* v_optName_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_351_, v_optName_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_358_, lean_object* v_inst_359_, lean_object* v_optName_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_358_, v_inst_359_, v_optName_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_optName_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_366_, lean_object* v_cls_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_373_ = l_Lean_Name_append(v___x_372_, v_cls_367_);
v___x_374_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_366_, v___x_373_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_375_, lean_object* v_cls_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_IR_logMessageIf___redArg(v_inst_375_, v_cls_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_cls_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_390_ = l_Lean_Name_append(v___x_389_, v_cls_384_);
v___x_391_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_383_, v___x_390_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_392_, lean_object* v_inst_393_, lean_object* v_cls_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_IR_logMessageIf(v_00_u03b1_392_, v_inst_393_, v_cls_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_406_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_400_, v___x_405_, v_a_401_, v_a_402_, v_a_403_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_IR_logMessage___redArg(v_inst_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_413_, lean_object* v_inst_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_420_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_414_, v___x_419_, v_a_415_, v_a_416_, v_a_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_421_, lean_object* v_inst_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_IR_logMessage(v_00_u03b1_421_, v_inst_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_428_, lean_object* v_b_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = l_Lean_IR_Decl_name(v_a_428_);
v___x_431_ = l_Lean_IR_Decl_name(v_b_429_);
v___x_432_ = l_Lean_Name_quickLt(v___x_430_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v___x_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_433_, lean_object* v_b_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_433_, v_b_434_);
lean_dec_ref(v_b_434_);
lean_dec_ref(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_array_get_size(v_decls_438_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_nat_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___y_446_; uint8_t v___x_450_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_sub(v___x_439_, v___x_443_);
v___x_450_ = lean_nat_dec_le(v___x_440_, v___x_444_);
if (v___x_450_ == 0)
{
lean_inc(v___x_444_);
v___y_446_ = v___x_444_;
goto v___jp_445_;
}
else
{
v___y_446_ = v___x_440_;
goto v___jp_445_;
}
v___jp_445_:
{
uint8_t v___x_447_; 
v___x_447_ = lean_nat_dec_le(v___y_446_, v___x_444_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec(v___x_444_);
lean_inc(v___y_446_);
v___x_448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_442_, v___x_439_, v_decls_438_, v___y_446_, v___y_446_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_446_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_442_, v___x_439_, v_decls_438_, v___y_446_, v___x_444_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_444_);
return v___x_449_;
}
}
}
else
{
return v_decls_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_454_, lean_object* v_declName_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_array_get_size(v_decls_454_);
v___x_458_ = lean_nat_dec_lt(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_declName_455_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_sub(v___x_457_, v___x_460_);
v___x_462_ = lean_nat_dec_le(v___x_456_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v___x_461_);
lean_dec(v_declName_455_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_tmpDecl_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_465_ = lean_box(0);
v___x_466_ = lean_box(0);
v_tmpDecl_467_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_467_, 0, v_declName_455_);
lean_ctor_set(v_tmpDecl_467_, 1, v___x_464_);
lean_ctor_set(v_tmpDecl_467_, 2, v___x_465_);
lean_ctor_set(v_tmpDecl_467_, 3, v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_469_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_470_ = l_Array_binSearchAux___redArg(v___x_468_, v___x_469_, v_decls_454_, v_tmpDecl_467_, v___x_456_, v___x_461_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_471_, lean_object* v_declName_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_471_, v_declName_472_);
lean_dec_ref(v_decls_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_474_, lean_object* v_pivot_475_, lean_object* v_as_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_lt(v_k_478_, v_hi_474_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_k_478_);
v___x_480_ = lean_array_fswap(v_as_476_, v_i_477_, v_hi_474_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_i_477_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_482_ = lean_array_fget_borrowed(v_as_476_, v_k_478_);
v___x_483_ = l_Lean_IR_Decl_name(v___x_482_);
v___x_484_ = l_Lean_IR_Decl_name(v_pivot_475_);
v___x_485_ = l_Lean_Name_quickLt(v___x_483_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_483_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_k_478_, v___x_486_);
lean_dec(v_k_478_);
v_k_478_ = v___x_487_;
goto _start;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_array_fswap(v_as_476_, v_i_477_, v_k_478_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_477_, v___x_490_);
lean_dec(v_i_477_);
v___x_492_ = lean_nat_add(v_k_478_, v___x_490_);
lean_dec(v_k_478_);
v_as_476_ = v___x_489_;
v_i_477_ = v___x_491_;
v_k_478_ = v___x_492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_494_, lean_object* v_pivot_495_, lean_object* v_as_496_, lean_object* v_i_497_, lean_object* v_k_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_494_, v_pivot_495_, v_as_496_, v_i_497_, v_k_498_);
lean_dec_ref(v_pivot_495_);
lean_dec(v_hi_494_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = l_Lean_IR_Decl_name(v___y_500_);
v___x_503_ = l_Lean_IR_Decl_name(v___y_501_);
v___x_504_ = l_Lean_Name_quickLt(v___x_502_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___x_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_505_, v___y_506_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v___y_505_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_509_, lean_object* v_as_510_, lean_object* v_lo_511_, lean_object* v_hi_512_){
_start:
{
lean_object* v___y_514_; uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_lt(v_lo_511_, v_hi_512_);
if (v___x_524_ == 0)
{
lean_dec(v_lo_511_);
return v_as_510_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_mid_527_; lean_object* v___y_529_; lean_object* v___y_535_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_525_ = lean_nat_add(v_lo_511_, v_hi_512_);
v___x_526_ = lean_unsigned_to_nat(1u);
v_mid_527_ = lean_nat_shiftr(v___x_525_, v___x_526_);
lean_dec(v___x_525_);
v___x_540_ = lean_array_fget_borrowed(v_as_510_, v_mid_527_);
v___x_541_ = lean_array_fget_borrowed(v_as_510_, v_lo_511_);
v___x_542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
v___y_535_ = v_as_510_;
goto v___jp_534_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_array_fswap(v_as_510_, v_lo_511_, v_mid_527_);
v___y_535_ = v___x_543_;
goto v___jp_534_;
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_array_fget_borrowed(v___y_529_, v_mid_527_);
v___x_531_ = lean_array_fget_borrowed(v___y_529_, v_hi_512_);
v___x_532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec(v_mid_527_);
v___y_514_ = v___y_529_;
goto v___jp_513_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_array_fswap(v___y_529_, v_mid_527_, v_hi_512_);
lean_dec(v_mid_527_);
v___y_514_ = v___x_533_;
goto v___jp_513_;
}
}
v___jp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_array_fget_borrowed(v___y_535_, v_hi_512_);
v___x_537_ = lean_array_fget_borrowed(v___y_535_, v_lo_511_);
v___x_538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
v___y_529_ = v___y_535_;
goto v___jp_528_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_array_fswap(v___y_535_, v_lo_511_, v_hi_512_);
v___y_529_ = v___x_539_;
goto v___jp_528_;
}
}
}
v___jp_513_:
{
lean_object* v_pivot_515_; lean_object* v___x_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; uint8_t v___x_519_; 
v_pivot_515_ = lean_array_fget(v___y_514_, v_hi_512_);
lean_inc_n(v_lo_511_, 2);
v___x_516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_512_, v_pivot_515_, v___y_514_, v_lo_511_, v_lo_511_);
lean_dec(v_pivot_515_);
v_fst_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_fst_517_);
v_snd_518_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_snd_518_);
lean_dec_ref(v___x_516_);
v___x_519_ = lean_nat_dec_le(v_hi_512_, v_fst_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_509_, v_snd_518_, v_lo_511_, v_fst_517_);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_add(v_fst_517_, v___x_521_);
lean_dec(v_fst_517_);
v_as_510_ = v___x_520_;
v_lo_511_ = v___x_522_;
goto _start;
}
else
{
lean_dec(v_fst_517_);
lean_dec(v_lo_511_);
return v_snd_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_544_, lean_object* v_as_545_, lean_object* v_lo_546_, lean_object* v_hi_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_544_, v_as_545_, v_lo_546_, v_hi_547_);
lean_dec(v_hi_547_);
lean_dec(v_n_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_555_, lean_object* v_as_556_, size_t v_i_557_, size_t v_stop_558_, lean_object* v_b_559_){
_start:
{
lean_object* v___y_561_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_eq(v_i_557_, v_stop_558_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; uint8_t v___y_575_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_573_ = lean_array_uget_borrowed(v_as_556_, v_i_557_);
v___x_590_ = l_Lean_IR_Decl_name(v___x_573_);
lean_inc_ref(v_env_555_);
v___x_591_ = l_Lean_isDeclMeta(v_env_555_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; 
lean_inc_ref(v_env_555_);
v___x_592_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_555_, v___x_590_);
if (v___x_592_ == 0)
{
lean_dec(v___x_590_);
v___y_561_ = v_b_559_;
goto v___jp_560_;
}
else
{
uint8_t v___x_593_; 
v___x_593_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_590_);
if (v___x_593_ == 0)
{
lean_dec(v___x_590_);
v___y_575_ = v___x_591_;
goto v___jp_574_;
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = l_Lean_Name_getPrefix(v___x_590_);
lean_dec(v___x_590_);
lean_inc_ref(v_env_555_);
v___x_595_ = l_Lean_isExtern(v_env_555_, v___x_594_);
v___y_575_ = v___x_595_;
goto v___jp_574_;
}
}
}
else
{
lean_object* v___x_596_; 
lean_dec(v___x_590_);
lean_inc(v___x_573_);
v___x_596_ = lean_array_push(v_b_559_, v___x_573_);
v___y_561_ = v___x_596_;
goto v___jp_560_;
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_f_576_; lean_object* v_xs_577_; lean_object* v_type_578_; lean_object* v___x_579_; 
v_f_576_ = lean_ctor_get(v___x_573_, 0);
v_xs_577_ = lean_ctor_get(v___x_573_, 1);
v_type_578_ = lean_ctor_get(v___x_573_, 2);
lean_inc(v_f_576_);
lean_inc_ref(v_env_555_);
v___x_579_ = lean_get_export_name_for(v_env_555_, v_f_576_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; 
v_val_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v___x_579_, 1);
if (lean_obj_tag(v_val_580_) == 1)
{
lean_object* v_str_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_str_581_ = lean_ctor_get(v_val_580_, 1);
lean_inc_ref(v_str_581_);
lean_dec_ref_known(v_val_580_, 2);
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_str_581_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
lean_inc(v_type_578_);
lean_inc_ref(v_xs_577_);
lean_inc(v_f_576_);
v___x_586_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_586_, 0, v_f_576_);
lean_ctor_set(v___x_586_, 1, v_xs_577_);
lean_ctor_set(v___x_586_, 2, v_type_578_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
v___x_587_ = lean_array_push(v_b_559_, v___x_586_);
v___y_561_ = v___x_587_;
goto v___jp_560_;
}
else
{
lean_dec(v_val_580_);
lean_inc_ref(v_xs_577_);
lean_inc(v_f_576_);
lean_inc(v_type_578_);
v___y_566_ = v_type_578_;
v___y_567_ = v_f_576_;
v___y_568_ = v_xs_577_;
goto v___jp_565_;
}
}
else
{
lean_dec(v___x_579_);
lean_inc_ref(v_xs_577_);
lean_inc(v_f_576_);
lean_inc(v_type_578_);
v___y_566_ = v_type_578_;
v___y_567_ = v_f_576_;
v___y_568_ = v_xs_577_;
goto v___jp_565_;
}
}
else
{
lean_object* v___x_588_; 
lean_inc(v___x_573_);
v___x_588_ = lean_array_push(v_b_559_, v___x_573_);
v___y_561_ = v___x_588_;
goto v___jp_560_;
}
}
else
{
lean_object* v___x_589_; 
lean_inc(v___x_573_);
v___x_589_ = lean_array_push(v_b_559_, v___x_573_);
v___y_561_ = v___x_589_;
goto v___jp_560_;
}
}
}
else
{
lean_dec_ref(v_env_555_);
return v_b_559_;
}
v___jp_560_:
{
size_t v___x_562_; size_t v___x_563_; 
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_557_, v___x_562_);
v_i_557_ = v___x_563_;
v_b_559_ = v___y_561_;
goto _start;
}
v___jp_565_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_570_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_570_, 0, v___y_567_);
lean_ctor_set(v___x_570_, 1, v___y_568_);
lean_ctor_set(v___x_570_, 2, v___y_566_);
lean_ctor_set(v___x_570_, 3, v___x_569_);
v___x_571_ = lean_array_push(v_b_559_, v___x_570_);
v___y_561_ = v___x_571_;
goto v___jp_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_597_, lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_stop_600_, lean_object* v_b_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; lean_object* v_res_604_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_600_);
lean_dec(v_stop_600_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_597_, v_as_598_, v_i_boxed_602_, v_stop_boxed_603_, v_b_601_);
lean_dec_ref(v_as_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_607_, lean_object* v_as_608_, lean_object* v_start_609_, lean_object* v_stop_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_612_ = lean_nat_dec_lt(v_start_609_, v_stop_610_);
if (v___x_612_ == 0)
{
lean_dec_ref(v_env_607_);
return v___x_611_;
}
else
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_get_size(v_as_608_);
v___x_614_ = lean_nat_dec_le(v_stop_610_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v_start_609_, v___x_613_);
if (v___x_615_ == 0)
{
lean_dec_ref(v_env_607_);
return v___x_611_;
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_usize_of_nat(v_start_609_);
v___x_617_ = lean_usize_of_nat(v___x_613_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_607_, v_as_608_, v___x_616_, v___x_617_, v___x_611_);
return v___x_618_;
}
}
else
{
size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_usize_of_nat(v_start_609_);
v___x_620_ = lean_usize_of_nat(v_stop_610_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_607_, v_as_608_, v___x_619_, v___x_620_, v___x_611_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_622_, lean_object* v_as_623_, lean_object* v_start_624_, lean_object* v_stop_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_622_, v_as_623_, v_start_624_, v_stop_625_);
lean_dec(v_stop_625_);
lean_dec(v_start_624_);
lean_dec_ref(v_as_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
return v_x_627_;
}
else
{
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_631_; 
v_head_629_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_head_629_);
v_tail_630_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_tail_630_);
lean_dec_ref_known(v_x_628_, 2);
v___x_631_ = lean_array_push(v_x_627_, v_head_629_);
v_x_627_ = v___x_631_;
v_x_628_ = v_tail_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_633_, lean_object* v_s_634_, lean_object* v_entries_635_){
_start:
{
lean_object* v___y_637_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_decls_647_; lean_object* v___x_648_; lean_object* v___y_650_; lean_object* v___y_651_; uint8_t v___x_653_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_647_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_646_, v_entries_635_);
v___x_648_ = lean_array_get_size(v_decls_647_);
v___x_653_ = lean_nat_dec_eq(v___x_648_, v___x_645_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___y_657_; uint8_t v___x_659_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_sub(v___x_648_, v___x_654_);
v___x_659_ = lean_nat_dec_le(v___x_645_, v___x_655_);
if (v___x_659_ == 0)
{
lean_inc(v___x_655_);
v___y_657_ = v___x_655_;
goto v___jp_656_;
}
else
{
v___y_657_ = v___x_645_;
goto v___jp_656_;
}
v___jp_656_:
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_le(v___y_657_, v___x_655_);
if (v___x_658_ == 0)
{
lean_dec(v___x_655_);
lean_inc(v___y_657_);
v___y_650_ = v___y_657_;
v___y_651_ = v___y_657_;
goto v___jp_649_;
}
else
{
v___y_650_ = v___y_657_;
v___y_651_ = v___x_655_;
goto v___jp_649_;
}
}
}
else
{
v___y_637_ = v_decls_647_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; uint8_t v_isModule_639_; 
v___x_638_ = l_Lean_Environment_header(v_env_633_);
v_isModule_639_ = lean_ctor_get_uint8(v___x_638_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_638_);
if (v_isModule_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_env_633_);
lean_inc_ref_n(v___y_637_, 2);
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v___y_637_);
lean_ctor_set(v___x_640_, 1, v___y_637_);
lean_ctor_set(v___x_640_, 2, v___y_637_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_array_get_size(v___y_637_);
v___x_643_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_633_, v___y_637_, v___x_641_, v___x_642_);
lean_dec_ref(v___y_637_);
lean_inc_ref_n(v___x_643_, 2);
v___x_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
return v___x_644_;
}
}
v___jp_649_:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_648_, v_decls_647_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
v___y_637_ = v___x_652_;
goto v___jp_636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_660_, lean_object* v_s_661_, lean_object* v_entries_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_660_, v_s_661_, v_entries_662_);
lean_dec_ref(v_s_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_array_mk(v_es_664_);
return v___x_665_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object* v_keys_666_, lean_object* v_i_667_, lean_object* v_k_668_){
_start:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_array_get_size(v_keys_666_);
v___x_670_ = lean_nat_dec_lt(v_i_667_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec(v_i_667_);
return v___x_670_;
}
else
{
lean_object* v_k_x27_671_; uint8_t v___x_672_; 
v_k_x27_671_ = lean_array_fget_borrowed(v_keys_666_, v_i_667_);
v___x_672_ = lean_name_eq(v_k_668_, v_k_x27_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_i_667_, v___x_673_);
lean_dec(v_i_667_);
v_i_667_ = v___x_674_;
goto _start;
}
else
{
lean_dec(v_i_667_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_676_, lean_object* v_i_677_, lean_object* v_k_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_676_, v_i_677_, v_k_678_);
lean_dec(v_k_678_);
lean_dec_ref(v_keys_676_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_681_, size_t v_x_682_, lean_object* v_x_683_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_object* v_es_684_; lean_object* v___x_685_; size_t v___x_686_; size_t v___x_687_; lean_object* v_j_688_; lean_object* v___x_689_; 
v_es_684_ = lean_ctor_get(v_x_681_, 0);
v___x_685_ = lean_box(2);
v___x_686_ = ((size_t)31ULL);
v___x_687_ = lean_usize_land(v_x_682_, v___x_686_);
v_j_688_ = lean_usize_to_nat(v___x_687_);
v___x_689_ = lean_array_get_borrowed(v___x_685_, v_es_684_, v_j_688_);
lean_dec(v_j_688_);
switch(lean_obj_tag(v___x_689_))
{
case 0:
{
lean_object* v_key_690_; uint8_t v___x_691_; 
v_key_690_ = lean_ctor_get(v___x_689_, 0);
v___x_691_ = lean_name_eq(v_x_683_, v_key_690_);
return v___x_691_;
}
case 1:
{
lean_object* v_node_692_; size_t v___x_693_; size_t v___x_694_; 
v_node_692_ = lean_ctor_get(v___x_689_, 0);
v___x_693_ = ((size_t)5ULL);
v___x_694_ = lean_usize_shift_right(v_x_682_, v___x_693_);
v_x_681_ = v_node_692_;
v_x_682_ = v___x_694_;
goto _start;
}
default: 
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
}
else
{
lean_object* v_ks_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_ks_697_ = lean_ctor_get(v_x_681_, 0);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_697_, v___x_698_, v_x_683_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
size_t v_x_2170__boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_x_2170__boxed_703_ = lean_unbox_usize(v_x_701_);
lean_dec(v_x_701_);
v_res_704_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_700_, v_x_2170__boxed_703_, v_x_702_);
lean_dec(v_x_702_);
lean_dec_ref(v_x_700_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
uint64_t v___y_709_; 
if (lean_obj_tag(v_x_707_) == 0)
{
uint64_t v___x_712_; 
v___x_712_ = 1723ULL;
v___y_709_ = v___x_712_;
goto v___jp_708_;
}
else
{
uint64_t v_hash_713_; 
v_hash_713_ = lean_ctor_get_uint64(v_x_707_, sizeof(void*)*2);
v___y_709_ = v_hash_713_;
goto v___jp_708_;
}
v___jp_708_:
{
size_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_uint64_to_usize(v___y_709_);
v___x_711_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_706_, v___x_710_, v_x_707_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_714_, v_x_715_);
lean_dec(v_x_715_);
lean_dec_ref(v_x_714_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_718_, lean_object* v_x2_719_){
_start:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_IR_Decl_name(v_x2_719_);
v___x_721_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_718_, v___x_720_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = 1;
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_724_, lean_object* v_x2_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_724_, v_x2_725_);
lean_dec_ref(v_x2_725_);
lean_dec_ref(v_x1_724_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_732_);
lean_dec_ref(v_x_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
lean_object* v_ks_738_; lean_object* v_vs_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_763_; 
v_ks_738_ = lean_ctor_get(v_x_734_, 0);
v_vs_739_ = lean_ctor_get(v_x_734_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_763_ == 0)
{
v___x_741_ = v_x_734_;
v_isShared_742_ = v_isSharedCheck_763_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_vs_739_);
lean_inc(v_ks_738_);
lean_dec(v_x_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_763_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v_ks_738_);
v___x_744_ = lean_nat_dec_lt(v_x_735_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec(v_x_735_);
v___x_745_ = lean_array_push(v_ks_738_, v_x_736_);
v___x_746_ = lean_array_push(v_vs_739_, v_x_737_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_746_);
lean_ctor_set(v___x_741_, 0, v___x_745_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_object* v_k_x27_750_; uint8_t v___x_751_; 
v_k_x27_750_ = lean_array_fget_borrowed(v_ks_738_, v_x_735_);
v___x_751_ = lean_name_eq(v_x_736_, v_k_x27_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_753_; 
if (v_isShared_742_ == 0)
{
v___x_753_ = v___x_741_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_ks_738_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_vs_739_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_x_735_, v___x_754_);
lean_dec(v_x_735_);
v_x_734_ = v___x_753_;
v_x_735_ = v___x_755_;
goto _start;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = lean_array_fset(v_ks_738_, v_x_735_, v_x_736_);
v___x_759_ = lean_array_fset(v_vs_739_, v_x_735_, v_x_737_);
lean_dec(v_x_735_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_759_);
lean_ctor_set(v___x_741_, 0, v___x_758_);
v___x_761_ = v___x_741_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_764_, lean_object* v_k_765_, lean_object* v_v_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_764_, v___x_767_, v_k_765_, v_v_766_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_770_, size_t v_x_771_, size_t v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_object* v_es_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v_j_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_es_775_ = lean_ctor_get(v_x_770_, 0);
v___x_776_ = ((size_t)31ULL);
v___x_777_ = lean_usize_land(v_x_771_, v___x_776_);
v_j_778_ = lean_usize_to_nat(v___x_777_);
v___x_779_ = lean_array_get_size(v_es_775_);
v___x_780_ = lean_nat_dec_lt(v_j_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v_j_778_);
lean_dec(v_x_774_);
lean_dec(v_x_773_);
return v_x_770_;
}
else
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_819_; 
lean_inc_ref(v_es_775_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_x_770_, 0);
lean_dec(v_unused_820_);
v___x_782_ = v_x_770_;
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_x_770_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_v_784_; lean_object* v___x_785_; lean_object* v_xs_x27_786_; lean_object* v___y_788_; 
v_v_784_ = lean_array_fget(v_es_775_, v_j_778_);
v___x_785_ = lean_box(0);
v_xs_x27_786_ = lean_array_fset(v_es_775_, v_j_778_, v___x_785_);
switch(lean_obj_tag(v_v_784_))
{
case 0:
{
lean_object* v_key_793_; lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_804_; 
v_key_793_ = lean_ctor_get(v_v_784_, 0);
v_val_794_ = lean_ctor_get(v_v_784_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_v_784_);
if (v_isSharedCheck_804_ == 0)
{
v___x_796_ = v_v_784_;
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_inc(v_key_793_);
lean_dec(v_v_784_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
uint8_t v___x_798_; 
v___x_798_ = lean_name_eq(v_x_773_, v_key_793_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_796_);
v___x_799_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_793_, v_val_794_, v_x_773_, v_x_774_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
v___y_788_ = v___x_800_;
goto v___jp_787_;
}
else
{
lean_object* v___x_802_; 
lean_dec(v_val_794_);
lean_dec(v_key_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_x_774_);
lean_ctor_set(v___x_796_, 0, v_x_773_);
v___x_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_x_773_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_x_774_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v___y_788_ = v___x_802_;
goto v___jp_787_;
}
}
}
}
case 1:
{
lean_object* v_node_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_817_; 
v_node_805_ = lean_ctor_get(v_v_784_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_v_784_);
if (v_isSharedCheck_817_ == 0)
{
v___x_807_ = v_v_784_;
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_node_805_);
lean_dec(v_v_784_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_809_ = ((size_t)5ULL);
v___x_810_ = lean_usize_shift_right(v_x_771_, v___x_809_);
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_add(v_x_772_, v___x_811_);
v___x_813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_805_, v___x_810_, v___x_812_, v_x_773_, v_x_774_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_813_);
v___x_815_ = v___x_807_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v___y_788_ = v___x_815_;
goto v___jp_787_;
}
}
}
default: 
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_x_773_);
lean_ctor_set(v___x_818_, 1, v_x_774_);
v___y_788_ = v___x_818_;
goto v___jp_787_;
}
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_array_fset(v_xs_x27_786_, v_j_778_, v___y_788_);
lean_dec(v_j_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_789_);
v___x_791_ = v___x_782_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
else
{
lean_object* v_ks_821_; lean_object* v_vs_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_840_; 
v_ks_821_ = lean_ctor_get(v_x_770_, 0);
v_vs_822_ = lean_ctor_get(v_x_770_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_840_ == 0)
{
v___x_824_ = v_x_770_;
v_isShared_825_ = v_isSharedCheck_840_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_vs_822_);
lean_inc(v_ks_821_);
lean_dec(v_x_770_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_840_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_ks_821_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_vs_822_);
v___x_827_ = v_reuseFailAlloc_839_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v_newNode_828_; size_t v___x_829_; uint8_t v___x_830_; 
v_newNode_828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_827_, v_x_773_, v_x_774_);
v___x_829_ = ((size_t)7ULL);
v___x_830_ = lean_usize_dec_le(v___x_829_, v_x_772_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_828_);
v___x_832_ = lean_unsigned_to_nat(4u);
v___x_833_ = lean_nat_dec_lt(v___x_831_, v___x_832_);
lean_dec(v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_ks_834_ = lean_ctor_get(v_newNode_828_, 0);
lean_inc_ref(v_ks_834_);
v_vs_835_ = lean_ctor_get(v_newNode_828_, 1);
lean_inc_ref(v_vs_835_);
lean_dec_ref(v_newNode_828_);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_772_, v_ks_834_, v_vs_835_, v___x_836_, v___x_837_);
lean_dec_ref(v_vs_835_);
lean_dec_ref(v_ks_834_);
return v___x_838_;
}
else
{
return v_newNode_828_;
}
}
else
{
return v_newNode_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t v_depth_841_, lean_object* v_keys_842_, lean_object* v_vals_843_, lean_object* v_i_844_, lean_object* v_entries_845_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_get_size(v_keys_842_);
v___x_847_ = lean_nat_dec_lt(v_i_844_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_i_844_);
return v_entries_845_;
}
else
{
lean_object* v_k_848_; lean_object* v_v_849_; uint64_t v___y_851_; 
v_k_848_ = lean_array_fget_borrowed(v_keys_842_, v_i_844_);
v_v_849_ = lean_array_fget_borrowed(v_vals_843_, v_i_844_);
if (lean_obj_tag(v_k_848_) == 0)
{
uint64_t v___x_862_; 
v___x_862_ = 1723ULL;
v___y_851_ = v___x_862_;
goto v___jp_850_;
}
else
{
uint64_t v_hash_863_; 
v_hash_863_ = lean_ctor_get_uint64(v_k_848_, sizeof(void*)*2);
v___y_851_ = v_hash_863_;
goto v___jp_850_;
}
v___jp_850_:
{
size_t v_h_852_; size_t v___x_853_; lean_object* v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v_h_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_h_852_ = lean_uint64_to_usize(v___y_851_);
v___x_853_ = ((size_t)5ULL);
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = ((size_t)1ULL);
v___x_856_ = lean_usize_sub(v_depth_841_, v___x_855_);
v___x_857_ = lean_usize_mul(v___x_853_, v___x_856_);
v_h_858_ = lean_usize_shift_right(v_h_852_, v___x_857_);
v___x_859_ = lean_nat_add(v_i_844_, v___x_854_);
lean_dec(v_i_844_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
v___x_860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_845_, v_h_858_, v_depth_841_, v_k_848_, v_v_849_);
v_i_844_ = v___x_859_;
v_entries_845_ = v___x_860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_i_867_, lean_object* v_entries_868_){
_start:
{
size_t v_depth_boxed_869_; lean_object* v_res_870_; 
v_depth_boxed_869_ = lean_unbox_usize(v_depth_864_);
lean_dec(v_depth_864_);
v_res_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_869_, v_keys_865_, v_vals_866_, v_i_867_, v_entries_868_);
lean_dec_ref(v_vals_866_);
lean_dec_ref(v_keys_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_2331__boxed_876_; size_t v_x_2332__boxed_877_; lean_object* v_res_878_; 
v_x_2331__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_2332__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_871_, v_x_2331__boxed_876_, v_x_2332__boxed_877_, v_x_874_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
uint64_t v___y_883_; 
if (lean_obj_tag(v_x_880_) == 0)
{
uint64_t v___x_887_; 
v___x_887_ = 1723ULL;
v___y_883_ = v___x_887_;
goto v___jp_882_;
}
else
{
uint64_t v_hash_888_; 
v_hash_888_ = lean_ctor_get_uint64(v_x_880_, sizeof(void*)*2);
v___y_883_ = v_hash_888_;
goto v___jp_882_;
}
v___jp_882_:
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_uint64_to_usize(v___y_883_);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_879_, v___x_884_, v___x_885_, v_x_880_, v_x_881_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_889_, lean_object* v_d_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = l_Lean_IR_Decl_name(v_d_890_);
v___x_892_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_889_, v___x_891_, v_d_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_921_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_924_, lean_object* v_as_925_, lean_object* v_lo_926_, lean_object* v_hi_927_, lean_object* v_w_928_, lean_object* v_hlo_929_, lean_object* v_hhi_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_924_, v_as_925_, v_lo_926_, v_hi_927_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_932_, lean_object* v_as_933_, lean_object* v_lo_934_, lean_object* v_hi_935_, lean_object* v_w_936_, lean_object* v_hlo_937_, lean_object* v_hhi_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_932_, v_as_933_, v_lo_934_, v_hi_935_, v_w_936_, v_hlo_937_, v_hhi_938_);
lean_dec(v_hi_935_);
lean_dec(v_n_932_);
return v_res_939_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_944_, v_x_945_, v_x_946_);
lean_dec(v_x_946_);
lean_dec_ref(v_x_945_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_950_, v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_954_, lean_object* v_lo_955_, lean_object* v_hi_956_, lean_object* v_hhi_957_, lean_object* v_pivot_958_, lean_object* v_as_959_, lean_object* v_i_960_, lean_object* v_k_961_, lean_object* v_ilo_962_, lean_object* v_ik_963_, lean_object* v_w_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_956_, v_pivot_958_, v_as_959_, v_i_960_, v_k_961_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_966_, lean_object* v_lo_967_, lean_object* v_hi_968_, lean_object* v_hhi_969_, lean_object* v_pivot_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_k_973_, lean_object* v_ilo_974_, lean_object* v_ik_975_, lean_object* v_w_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_966_, v_lo_967_, v_hi_968_, v_hhi_969_, v_pivot_970_, v_as_971_, v_i_972_, v_k_973_, v_ilo_974_, v_ik_975_, v_w_976_);
lean_dec_ref(v_pivot_970_);
lean_dec(v_hi_968_);
lean_dec(v_lo_967_);
lean_dec(v_n_966_);
return v_res_977_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_978_, lean_object* v_x_979_, size_t v_x_980_, lean_object* v_x_981_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_979_, v_x_980_, v_x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
size_t v_x_2613__boxed_987_; uint8_t v_res_988_; lean_object* v_r_989_; 
v_x_2613__boxed_987_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_res_988_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_983_, v_x_984_, v_x_2613__boxed_987_, v_x_986_);
lean_dec(v_x_986_);
lean_dec_ref(v_x_984_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, size_t v_x_992_, size_t v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_991_, v_x_992_, v_x_993_, v_x_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
size_t v_x_2624__boxed_1003_; size_t v_x_2625__boxed_1004_; lean_object* v_res_1005_; 
v_x_2624__boxed_1003_ = lean_unbox_usize(v_x_999_);
lean_dec(v_x_999_);
v_x_2625__boxed_1004_ = lean_unbox_usize(v_x_1000_);
lean_dec(v_x_1000_);
v_res_1005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_997_, v_x_998_, v_x_2624__boxed_1003_, v_x_2625__boxed_1004_, v_x_1001_, v_x_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1006_, lean_object* v_keys_1007_, lean_object* v_vals_1008_, lean_object* v_heq_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_1007_, v_i_1010_, v_k_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1013_, lean_object* v_keys_1014_, lean_object* v_vals_1015_, lean_object* v_heq_1016_, lean_object* v_i_1017_, lean_object* v_k_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1013_, v_keys_1014_, v_vals_1015_, v_heq_1016_, v_i_1017_, v_k_1018_);
lean_dec(v_k_1018_);
lean_dec_ref(v_vals_1015_);
lean_dec_ref(v_keys_1014_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1021_, lean_object* v_n_1022_, lean_object* v_k_1023_, lean_object* v_v_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1022_, v_k_1023_, v_v_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1026_, size_t v_depth_1027_, lean_object* v_keys_1028_, lean_object* v_vals_1029_, lean_object* v_heq_1030_, lean_object* v_i_1031_, lean_object* v_entries_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1027_, v_keys_1028_, v_vals_1029_, v_i_1031_, v_entries_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1034_, lean_object* v_depth_1035_, lean_object* v_keys_1036_, lean_object* v_vals_1037_, lean_object* v_heq_1038_, lean_object* v_i_1039_, lean_object* v_entries_1040_){
_start:
{
size_t v_depth_boxed_1041_; lean_object* v_res_1042_; 
v_depth_boxed_1041_ = lean_unbox_usize(v_depth_1035_);
lean_dec(v_depth_1035_);
v_res_1042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1034_, v_depth_boxed_1041_, v_keys_1036_, v_vals_1037_, v_heq_1038_, v_i_1039_, v_entries_1040_);
lean_dec_ref(v_vals_1037_);
lean_dec_ref(v_keys_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_array_get_size(v_irDecls_1049_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_nat_dec_eq(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___y_1057_; uint8_t v___x_1061_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_sub(v___x_1050_, v___x_1054_);
v___x_1061_ = lean_nat_dec_le(v___x_1051_, v___x_1055_);
if (v___x_1061_ == 0)
{
lean_inc(v___x_1055_);
v___y_1057_ = v___x_1055_;
goto v___jp_1056_;
}
else
{
v___y_1057_ = v___x_1051_;
goto v___jp_1056_;
}
v___jp_1056_:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_le(v___y_1057_, v___x_1055_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v___x_1055_);
lean_inc(v___y_1057_);
v___x_1059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1053_, v___x_1050_, v_irDecls_1049_, v___y_1057_, v___y_1057_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1057_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1053_, v___x_1050_, v_irDecls_1049_, v___y_1057_, v___x_1055_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_1055_);
return v___x_1060_;
}
}
}
else
{
return v_irDecls_1049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1062_){
_start:
{
lean_inc_ref(v_initDecls_1062_);
return v_initDecls_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1063_);
lean_dec_ref(v_initDecls_1063_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1065_){
_start:
{
lean_inc_ref(v_modPkg_1065_);
return v_modPkg_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1066_);
lean_dec_ref(v_modPkg_1066_);
return v_res_1067_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0(void){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v_toEnvExtension_1074_; lean_object* v_name_1075_; lean_object* v_asyncMode_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___y_1081_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_irDecls_1111_; lean_object* v___x_1112_; lean_object* v___y_1114_; lean_object* v___y_1115_; uint8_t v___x_1117_; 
v___x_1073_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1074_ = lean_ctor_get(v___x_1073_, 0);
v_name_1075_ = lean_ctor_get(v___x_1073_, 1);
v_asyncMode_1076_ = lean_ctor_get(v_toEnvExtension_1074_, 2);
v___x_1077_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1078_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1079_ = lean_box(0);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1072_);
v___x_1110_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1077_, v___x_1073_, v_env_1072_, v_asyncMode_1076_);
v_irDecls_1111_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1109_, v___x_1110_);
v___x_1112_ = lean_array_get_size(v_irDecls_1111_);
v___x_1117_ = lean_nat_dec_eq(v___x_1112_, v___x_1108_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___y_1121_; uint8_t v___x_1123_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_sub(v___x_1112_, v___x_1118_);
v___x_1123_ = lean_nat_dec_le(v___x_1108_, v___x_1119_);
if (v___x_1123_ == 0)
{
lean_inc(v___x_1119_);
v___y_1121_ = v___x_1119_;
goto v___jp_1120_;
}
else
{
v___y_1121_ = v___x_1108_;
goto v___jp_1120_;
}
v___jp_1120_:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_nat_dec_le(v___y_1121_, v___x_1119_);
if (v___x_1122_ == 0)
{
lean_dec(v___x_1119_);
lean_inc(v___y_1121_);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v___y_1121_;
goto v___jp_1113_;
}
else
{
v___y_1114_ = v___y_1121_;
v___y_1115_ = v___x_1119_;
goto v___jp_1113_;
}
}
}
else
{
v___y_1081_ = v_irDecls_1111_;
goto v___jp_1080_;
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v_ext_1083_; lean_object* v_toEnvExtension_1084_; lean_object* v_name_1085_; lean_object* v_exportEntriesFn_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_private_1091_; lean_object* v___x_1092_; lean_object* v_toEnvExtension_1093_; lean_object* v_name_1094_; lean_object* v_exportEntriesFn_1095_; lean_object* v_asyncMode_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_private_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1082_ = l_Lean_regularInitAttr;
v_ext_1083_ = lean_ctor_get(v___x_1082_, 1);
v_toEnvExtension_1084_ = lean_ctor_get(v_ext_1083_, 0);
v_name_1085_ = lean_ctor_get(v_ext_1083_, 1);
v_exportEntriesFn_1086_ = lean_ctor_get(v_ext_1083_, 4);
v_asyncMode_1087_ = lean_ctor_get(v_toEnvExtension_1084_, 2);
v___x_1088_ = lean_box(0);
lean_inc_ref_n(v_env_1072_, 3);
v___x_1089_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1078_, v_ext_1083_, v_env_1072_, v_asyncMode_1087_, v___x_1088_);
lean_inc_ref(v_exportEntriesFn_1086_);
v___x_1090_ = lean_apply_2(v_exportEntriesFn_1086_, v_env_1072_, v___x_1089_);
v_private_1091_ = lean_ctor_get(v___x_1090_, 2);
lean_inc(v_private_1091_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1093_ = lean_ctor_get(v___x_1092_, 0);
v_name_1094_ = lean_ctor_get(v___x_1092_, 1);
v_exportEntriesFn_1095_ = lean_ctor_get(v___x_1092_, 4);
v_asyncMode_1096_ = lean_ctor_get(v_toEnvExtension_1093_, 2);
v___x_1097_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1079_, v___x_1092_, v_env_1072_, v_asyncMode_1096_, v___x_1088_);
lean_inc_ref(v_exportEntriesFn_1095_);
v___x_1098_ = lean_apply_2(v_exportEntriesFn_1095_, v_env_1072_, v___x_1097_);
v_private_1099_ = lean_ctor_get(v___x_1098_, 2);
lean_inc(v_private_1099_);
lean_dec_ref(v___x_1098_);
lean_inc(v_name_1075_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_name_1075_);
lean_ctor_set(v___x_1100_, 1, v___y_1081_);
lean_inc(v_name_1085_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_name_1085_);
lean_ctor_set(v___x_1101_, 1, v_private_1091_);
lean_inc(v_name_1094_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_name_1094_);
lean_ctor_set(v___x_1102_, 1, v_private_1099_);
v___x_1103_ = lean_unsigned_to_nat(3u);
v___x_1104_ = lean_mk_empty_array_with_capacity(v___x_1103_);
v___x_1105_ = lean_array_push(v___x_1104_, v___x_1100_);
v___x_1106_ = lean_array_push(v___x_1105_, v___x_1101_);
v___x_1107_ = lean_array_push(v___x_1106_, v___x_1102_);
return v___x_1107_;
}
v___jp_1113_:
{
lean_object* v___x_1116_; 
v___x_1116_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1112_, v_irDecls_1111_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
v___y_1081_ = v___x_1116_;
goto v___jp_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1124_, lean_object* v_k_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_m_1130_; lean_object* v_a_1131_; uint8_t v___x_1132_; 
v___x_1128_ = lean_nat_add(v_x_1126_, v_x_1127_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v_m_1130_ = lean_nat_shiftr(v___x_1128_, v___x_1129_);
lean_dec(v___x_1128_);
v_a_1131_ = lean_array_fget_borrowed(v_as_1124_, v_m_1130_);
v___x_1132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1131_, v_k_1125_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
lean_dec(v_x_1127_);
v___x_1133_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1125_, v_a_1131_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_m_1130_);
lean_dec(v_x_1126_);
lean_inc(v_a_1131_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1131_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; uint8_t v___y_1139_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_eq(v_m_1130_, v___x_1135_);
v___x_1137_ = lean_nat_sub(v_m_1130_, v___x_1129_);
lean_dec(v_m_1130_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_nat_dec_lt(v___x_1137_, v_x_1126_);
v___y_1139_ = v___x_1142_;
goto v___jp_1138_;
}
else
{
v___y_1139_ = v___x_1136_;
goto v___jp_1138_;
}
v___jp_1138_:
{
if (v___y_1139_ == 0)
{
v_x_1127_ = v___x_1137_;
goto _start;
}
else
{
lean_object* v___x_1141_; 
lean_dec(v___x_1137_);
lean_dec(v_x_1126_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
}
}
}
else
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
lean_dec(v_x_1126_);
v___x_1143_ = lean_nat_add(v_m_1130_, v___x_1129_);
lean_dec(v_m_1130_);
v___x_1144_ = lean_nat_dec_le(v___x_1143_, v_x_1127_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_dec(v___x_1143_);
lean_dec(v_x_1127_);
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
else
{
v_x_1126_ = v___x_1143_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1147_, lean_object* v_k_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1147_, v_k_1148_, v_x_1149_, v_x_1150_);
lean_dec_ref(v_k_1148_);
lean_dec_ref(v_as_1147_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_i_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_array_get_size(v_keys_1152_);
v___x_1157_ = lean_nat_dec_lt(v_i_1154_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_dec(v_i_1154_);
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
else
{
lean_object* v_k_x27_1159_; uint8_t v___x_1160_; 
v_k_x27_1159_ = lean_array_fget_borrowed(v_keys_1152_, v_i_1154_);
v___x_1160_ = lean_name_eq(v_k_1155_, v_k_x27_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_i_1154_, v___x_1161_);
lean_dec(v_i_1154_);
v_i_1154_ = v___x_1162_;
goto _start;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_array_fget_borrowed(v_vals_1153_, v_i_1154_);
lean_dec(v_i_1154_);
lean_inc(v___x_1164_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1166_, lean_object* v_vals_1167_, lean_object* v_i_1168_, lean_object* v_k_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1166_, v_vals_1167_, v_i_1168_, v_k_1169_);
lean_dec(v_k_1169_);
lean_dec_ref(v_vals_1167_);
lean_dec_ref(v_keys_1166_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1171_, size_t v_x_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1171_) == 0)
{
lean_object* v_es_1174_; lean_object* v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v_j_1178_; lean_object* v___x_1179_; 
v_es_1174_ = lean_ctor_get(v_x_1171_, 0);
v___x_1175_ = lean_box(2);
v___x_1176_ = ((size_t)31ULL);
v___x_1177_ = lean_usize_land(v_x_1172_, v___x_1176_);
v_j_1178_ = lean_usize_to_nat(v___x_1177_);
v___x_1179_ = lean_array_get_borrowed(v___x_1175_, v_es_1174_, v_j_1178_);
lean_dec(v_j_1178_);
switch(lean_obj_tag(v___x_1179_))
{
case 0:
{
lean_object* v_key_1180_; lean_object* v_val_1181_; uint8_t v___x_1182_; 
v_key_1180_ = lean_ctor_get(v___x_1179_, 0);
v_val_1181_ = lean_ctor_get(v___x_1179_, 1);
v___x_1182_ = lean_name_eq(v_x_1173_, v_key_1180_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; 
lean_inc(v_val_1181_);
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_val_1181_);
return v___x_1184_;
}
}
case 1:
{
lean_object* v_node_1185_; size_t v___x_1186_; size_t v___x_1187_; 
v_node_1185_ = lean_ctor_get(v___x_1179_, 0);
v___x_1186_ = ((size_t)5ULL);
v___x_1187_ = lean_usize_shift_right(v_x_1172_, v___x_1186_);
v_x_1171_ = v_node_1185_;
v_x_1172_ = v___x_1187_;
goto _start;
}
default: 
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_box(0);
return v___x_1189_;
}
}
}
else
{
lean_object* v_ks_1190_; lean_object* v_vs_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_ks_1190_ = lean_ctor_get(v_x_1171_, 0);
v_vs_1191_ = lean_ctor_get(v_x_1171_, 1);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1190_, v_vs_1191_, v___x_1192_, v_x_1173_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
size_t v_x_434__boxed_1197_; lean_object* v_res_1198_; 
v_x_434__boxed_1197_ = lean_unbox_usize(v_x_1195_);
lean_dec(v_x_1195_);
v_res_1198_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1194_, v_x_434__boxed_1197_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec_ref(v_x_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
uint64_t v___y_1202_; 
if (lean_obj_tag(v_x_1200_) == 0)
{
uint64_t v___x_1205_; 
v___x_1205_ = 1723ULL;
v___y_1202_ = v___x_1205_;
goto v___jp_1201_;
}
else
{
uint64_t v_hash_1206_; 
v_hash_1206_ = lean_ctor_get_uint64(v_x_1200_, sizeof(void*)*2);
v___y_1202_ = v_hash_1206_;
goto v___jp_1201_;
}
v___jp_1201_:
{
size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_uint64_to_usize(v___y_1202_);
v___x_1204_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1199_, v___x_1203_, v_x_1200_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1207_, v_x_1208_);
lean_dec(v_x_1208_);
lean_dec_ref(v_x_1207_);
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1213_, lean_object* v_declName_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1225_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1217_ = l_Lean_IR_declMapExt;
v___x_1225_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1213_, v_declName_1214_);
if (lean_obj_tag(v___x_1225_) == 0)
{
goto v___jp_1218_;
}
else
{
lean_object* v_val_1226_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_val_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1240_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1216_, v___x_1217_, v_env_1213_, v_val_1226_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_array_get_size(v___x_1240_);
v___x_1243_ = lean_nat_dec_lt(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v___x_1240_);
goto v___jp_1227_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_sub(v___x_1242_, v___x_1244_);
v___x_1246_ = lean_nat_dec_le(v___x_1241_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1240_);
goto v___jp_1227_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_tmpDecl_1249_; lean_object* v___x_1250_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1248_ = lean_box(0);
lean_inc(v_declName_1214_);
v_tmpDecl_1249_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1249_, 0, v_declName_1214_);
lean_ctor_set(v_tmpDecl_1249_, 1, v___x_1247_);
lean_ctor_set(v_tmpDecl_1249_, 2, v___x_1248_);
lean_ctor_set(v_tmpDecl_1249_, 3, v___x_1215_);
v___x_1250_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1240_, v_tmpDecl_1249_, v___x_1241_, v___x_1245_);
lean_dec_ref_known(v_tmpDecl_1249_, 4);
lean_dec_ref(v___x_1240_);
if (lean_obj_tag(v___x_1250_) == 0)
{
goto v___jp_1227_;
}
else
{
lean_dec(v_val_1226_);
lean_dec(v_declName_1214_);
lean_dec_ref(v_env_1213_);
return v___x_1250_;
}
}
}
v___jp_1227_:
{
uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1228_ = 0;
v___x_1229_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1216_, v___x_1217_, v_env_1213_, v_val_1226_, v___x_1228_);
lean_dec(v_val_1226_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_array_get_size(v___x_1229_);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec_ref(v___x_1229_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_sub(v___x_1231_, v___x_1233_);
v___x_1235_ = lean_nat_dec_le(v___x_1230_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec(v___x_1234_);
lean_dec_ref(v___x_1229_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_tmpDecl_1238_; lean_object* v___x_1239_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1237_ = lean_box(0);
lean_inc(v_declName_1214_);
v_tmpDecl_1238_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1238_, 0, v_declName_1214_);
lean_ctor_set(v_tmpDecl_1238_, 1, v___x_1236_);
lean_ctor_set(v_tmpDecl_1238_, 2, v___x_1237_);
lean_ctor_set(v_tmpDecl_1238_, 3, v___x_1215_);
v___x_1239_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1229_, v_tmpDecl_1238_, v___x_1230_, v___x_1234_);
lean_dec_ref_known(v_tmpDecl_1238_, 4);
lean_dec_ref(v___x_1229_);
if (lean_obj_tag(v___x_1239_) == 0)
{
goto v___jp_1218_;
}
else
{
lean_dec(v_declName_1214_);
lean_dec_ref(v_env_1213_);
return v___x_1239_;
}
}
}
}
}
v___jp_1218_:
{
lean_object* v_toEnvExtension_1219_; lean_object* v_asyncMode_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_snd_1223_; lean_object* v___x_1224_; 
v_toEnvExtension_1219_ = lean_ctor_get(v___x_1217_, 0);
v_asyncMode_1220_ = lean_ctor_get(v_toEnvExtension_1219_, 2);
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1216_, v___x_1217_, v_env_1213_, v_asyncMode_1220_, v___x_1221_);
v_snd_1223_ = lean_ctor_get(v___x_1222_, 1);
lean_inc(v_snd_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1223_, v_declName_1214_);
lean_dec(v_declName_1214_);
lean_dec(v_snd_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1252_, v_x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1255_, v_x_1256_, v_x_1257_);
lean_dec(v_x_1257_);
lean_dec_ref(v_x_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1259_, lean_object* v_k_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1259_, v_k_1260_, v_x_1261_, v_x_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1265_, lean_object* v_k_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1265_, v_k_1266_, v_x_1267_, v_x_1268_, v_x_1269_);
lean_dec_ref(v_k_1266_);
lean_dec_ref(v_as_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1271_, lean_object* v_x_1272_, size_t v_x_1273_, lean_object* v_x_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1272_, v_x_1273_, v_x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
size_t v_x_594__boxed_1280_; lean_object* v_res_1281_; 
v_x_594__boxed_1280_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_res_1281_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1276_, v_x_1277_, v_x_594__boxed_1280_, v_x_1279_);
lean_dec(v_x_1279_);
lean_dec_ref(v_x_1277_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1282_, lean_object* v_keys_1283_, lean_object* v_vals_1284_, lean_object* v_heq_1285_, lean_object* v_i_1286_, lean_object* v_k_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1283_, v_vals_1284_, v_i_1286_, v_k_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_keys_1290_, lean_object* v_vals_1291_, lean_object* v_heq_1292_, lean_object* v_i_1293_, lean_object* v_k_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1289_, v_keys_1290_, v_vals_1291_, v_heq_1292_, v_i_1293_, v_k_1294_);
lean_dec(v_k_1294_);
lean_dec_ref(v_vals_1291_);
lean_dec_ref(v_keys_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1296_, lean_object* v_declName_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1299_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1296_, v_declName_1297_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v___x_1300_; lean_object* v_toEnvExtension_1301_; lean_object* v_asyncMode_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1300_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1301_ = lean_ctor_get(v___x_1300_, 0);
v_asyncMode_1302_ = lean_ctor_get(v_toEnvExtension_1301_, 2);
v___x_1303_ = lean_box(0);
v___x_1304_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1298_, v___x_1300_, v_env_1296_, v_asyncMode_1302_, v___x_1303_);
v___x_1305_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1304_, v_declName_1297_);
lean_dec(v_declName_1297_);
lean_dec(v___x_1304_);
return v___x_1305_;
}
else
{
lean_object* v_val_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___y_1311_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_val_1306_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1309_ = l_Lean_IR_declMapExt;
v___x_1324_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1308_, v___x_1309_, v_env_1296_, v_val_1306_);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_array_get_size(v___x_1324_);
v___x_1327_ = lean_nat_dec_lt(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec_ref(v___x_1324_);
v___x_1328_ = lean_box(0);
v___y_1311_ = v___x_1328_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_sub(v___x_1326_, v___x_1329_);
v___x_1331_ = lean_nat_dec_le(v___x_1325_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec(v___x_1330_);
lean_dec_ref(v___x_1324_);
v___x_1332_ = lean_box(0);
v___y_1311_ = v___x_1332_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_tmpDecl_1335_; lean_object* v___x_1336_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1334_ = lean_box(0);
lean_inc(v_declName_1297_);
v_tmpDecl_1335_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1335_, 0, v_declName_1297_);
lean_ctor_set(v_tmpDecl_1335_, 1, v___x_1333_);
lean_ctor_set(v_tmpDecl_1335_, 2, v___x_1334_);
lean_ctor_set(v_tmpDecl_1335_, 3, v___x_1307_);
v___x_1336_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1324_, v_tmpDecl_1335_, v___x_1325_, v___x_1330_);
lean_dec_ref_known(v_tmpDecl_1335_, 4);
lean_dec_ref(v___x_1324_);
if (lean_obj_tag(v___x_1336_) == 0)
{
v___y_1311_ = v___x_1336_;
goto v___jp_1310_;
}
else
{
lean_dec(v_val_1306_);
lean_dec(v_declName_1297_);
lean_dec_ref(v_env_1296_);
return v___x_1336_;
}
}
}
v___jp_1310_:
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1312_ = 0;
v___x_1313_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1308_, v___x_1309_, v_env_1296_, v_val_1306_, v___x_1312_);
lean_dec(v_val_1306_);
lean_dec_ref(v_env_1296_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_array_get_size(v___x_1313_);
v___x_1316_ = lean_nat_dec_lt(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v___x_1313_);
lean_dec(v_declName_1297_);
return v___y_1311_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_sub(v___x_1315_, v___x_1317_);
v___x_1319_ = lean_nat_dec_le(v___x_1314_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v___x_1318_);
lean_dec_ref(v___x_1313_);
lean_dec(v_declName_1297_);
return v___y_1311_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v_tmpDecl_1322_; lean_object* v___x_1323_; 
lean_dec(v___y_1311_);
v___x_1320_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1321_ = lean_box(0);
v_tmpDecl_1322_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1322_, 0, v_declName_1297_);
lean_ctor_set(v_tmpDecl_1322_, 1, v___x_1320_);
lean_ctor_set(v_tmpDecl_1322_, 2, v___x_1321_);
lean_ctor_set(v_tmpDecl_1322_, 3, v___x_1307_);
v___x_1323_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1313_, v_tmpDecl_1322_, v___x_1314_, v___x_1318_);
lean_dec_ref_known(v_tmpDecl_1322_, 4);
lean_dec_ref(v___x_1313_);
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1337_, lean_object* v_declName_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v_boxed_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
lean_inc(v_declName_1338_);
v_boxed_1340_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1338_);
v___x_1341_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1337_, v_declName_1338_);
lean_dec(v_declName_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1342_; lean_object* v_toEnvExtension_1343_; lean_object* v_asyncMode_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1342_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1343_ = lean_ctor_get(v___x_1342_, 0);
v_asyncMode_1344_ = lean_ctor_get(v_toEnvExtension_1343_, 2);
v___x_1345_ = lean_box(0);
v___x_1346_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1339_, v___x_1342_, v_env_1337_, v_asyncMode_1344_, v___x_1345_);
v___x_1347_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1346_, v_boxed_1340_);
lean_dec(v_boxed_1340_);
lean_dec(v___x_1346_);
return v___x_1347_;
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___y_1353_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_val_1348_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1351_ = l_Lean_IR_declMapExt;
v___x_1366_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1350_, v___x_1351_, v_env_1337_, v_val_1348_);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_array_get_size(v___x_1366_);
v___x_1369_ = lean_nat_dec_lt(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec_ref(v___x_1366_);
v___x_1370_ = lean_box(0);
v___y_1353_ = v___x_1370_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_sub(v___x_1368_, v___x_1371_);
v___x_1373_ = lean_nat_dec_le(v___x_1367_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v___x_1372_);
lean_dec_ref(v___x_1366_);
v___x_1374_ = lean_box(0);
v___y_1353_ = v___x_1374_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_tmpDecl_1377_; lean_object* v___x_1378_; 
v___x_1375_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1376_ = lean_box(0);
lean_inc(v_boxed_1340_);
v_tmpDecl_1377_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1377_, 0, v_boxed_1340_);
lean_ctor_set(v_tmpDecl_1377_, 1, v___x_1375_);
lean_ctor_set(v_tmpDecl_1377_, 2, v___x_1376_);
lean_ctor_set(v_tmpDecl_1377_, 3, v___x_1349_);
v___x_1378_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1366_, v_tmpDecl_1377_, v___x_1367_, v___x_1372_);
lean_dec_ref_known(v_tmpDecl_1377_, 4);
lean_dec_ref(v___x_1366_);
if (lean_obj_tag(v___x_1378_) == 0)
{
v___y_1353_ = v___x_1378_;
goto v___jp_1352_;
}
else
{
lean_dec(v_val_1348_);
lean_dec(v_boxed_1340_);
lean_dec_ref(v_env_1337_);
return v___x_1378_;
}
}
}
v___jp_1352_:
{
uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1354_ = 0;
v___x_1355_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1350_, v___x_1351_, v_env_1337_, v_val_1348_, v___x_1354_);
lean_dec(v_val_1348_);
lean_dec_ref(v_env_1337_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_array_get_size(v___x_1355_);
v___x_1358_ = lean_nat_dec_lt(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v___x_1355_);
lean_dec(v_boxed_1340_);
return v___y_1353_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_nat_sub(v___x_1357_, v___x_1359_);
v___x_1361_ = lean_nat_dec_le(v___x_1356_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec(v___x_1360_);
lean_dec_ref(v___x_1355_);
lean_dec(v_boxed_1340_);
return v___y_1353_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_tmpDecl_1364_; lean_object* v___x_1365_; 
lean_dec(v___y_1353_);
v___x_1362_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1363_ = lean_box(0);
v_tmpDecl_1364_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1364_, 0, v_boxed_1340_);
lean_ctor_set(v_tmpDecl_1364_, 1, v___x_1362_);
lean_ctor_set(v_tmpDecl_1364_, 2, v___x_1363_);
lean_ctor_set(v_tmpDecl_1364_, 3, v___x_1349_);
v___x_1365_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1355_, v_tmpDecl_1364_, v___x_1356_, v___x_1360_);
lean_dec_ref_known(v_tmpDecl_1364_, 4);
lean_dec_ref(v___x_1355_);
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1379_, lean_object* v_constName_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1379_, v_constName_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1382_; lean_object* v_toEnvExtension_1383_; lean_object* v_asyncMode_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1382_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1383_ = lean_ctor_get(v___x_1382_, 0);
v_asyncMode_1384_ = lean_ctor_get(v_toEnvExtension_1383_, 2);
v___x_1385_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1386_ = lean_box(0);
v___x_1387_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1385_, v___x_1382_, v_env_1379_, v_asyncMode_1384_, v___x_1386_);
v___x_1388_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1387_, v_constName_1380_);
lean_dec(v_constName_1380_);
lean_dec(v___x_1387_);
if (v___x_1388_ == 0)
{
uint8_t v___x_1389_; 
v___x_1389_ = 1;
return v___x_1389_;
}
else
{
uint8_t v___x_1390_; 
v___x_1390_ = 0;
return v___x_1390_;
}
}
else
{
uint8_t v___x_1391_; 
lean_dec_ref_known(v___x_1381_, 1);
lean_dec(v_constName_1380_);
lean_dec_ref(v_env_1379_);
v___x_1391_ = 0;
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1392_, lean_object* v_constName_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = lean_has_compile_error(v_env_1392_, v_constName_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v_env_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1399_ = lean_st_ref_get(v_a_1397_);
v_env_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc_ref(v_env_1400_);
lean_dec(v___x_1399_);
v___x_1401_ = l_Lean_IR_findEnvDecl(v_env_1400_, v_n_1396_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_IR_findDecl___redArg(v_n_1403_, v_a_1404_);
lean_dec(v_a_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_IR_findDecl___redArg(v_n_1407_, v_a_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_IR_findDecl(v_n_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1435_; 
v___x_1420_ = l_Lean_IR_findDecl___redArg(v_n_1417_, v_a_1418_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1435_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1435_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
if (lean_obj_tag(v_a_1421_) == 0)
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = 0;
v___x_1426_ = lean_box(v___x_1425_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1426_);
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec_ref_known(v_a_1421_, 1);
v___x_1430_ = 1;
v___x_1431_ = lean_box(v___x_1430_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1431_);
v___x_1433_ = v___x_1423_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_IR_containsDecl___redArg(v_n_1436_, v_a_1437_);
lean_dec(v_a_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_IR_containsDecl___redArg(v_n_1440_, v_a_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_IR_containsDecl(v_n_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_ref_1454_; lean_object* v___x_1455_; lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
v_ref_1454_ = lean_ctor_get(v___y_1451_, 2);
v___x_1455_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1450_, v___y_1451_, v___y_1452_);
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_inc(v_ref_1454_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_ref_1454_);
lean_ctor_set(v___x_1460_, 1, v_a_1456_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 1);
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1494_; 
lean_inc(v_n_1472_);
v___x_1476_ = l_Lean_IR_findDecl___redArg(v_n_1472_, v_a_1474_);
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1494_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1494_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
if (lean_obj_tag(v_a_1477_) == 1)
{
lean_object* v_val_1481_; lean_object* v___x_1483_; 
lean_dec(v_n_1472_);
v_val_1481_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v_a_1477_, 1);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v_val_1481_);
v___x_1483_ = v___x_1479_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_val_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
else
{
lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_del_object(v___x_1479_);
lean_dec(v_a_1477_);
v___x_1485_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1486_ = 1;
v___x_1487_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1472_, v___x_1486_);
v___x_1488_ = lean_string_append(v___x_1485_, v___x_1487_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1490_ = lean_string_append(v___x_1488_, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
v___x_1492_ = l_Lean_MessageData_ofFormat(v___x_1491_);
v___x_1493_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1492_, v_a_1473_, v_a_1474_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_IR_getDecl(v_n_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1501_, v___y_1502_, v___y_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1506_, lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1506_, v_msg_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_env_1517_; lean_object* v___x_1518_; lean_object* v_toEnvExtension_1519_; lean_object* v_asyncMode_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1515_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1516_ = lean_st_ref_get(v_a_1513_);
v_env_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc_ref(v_env_1517_);
lean_dec(v___x_1516_);
v___x_1518_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1519_ = lean_ctor_get(v___x_1518_, 0);
v_asyncMode_1520_ = lean_ctor_get(v_toEnvExtension_1519_, 2);
v___x_1521_ = lean_box(0);
v___x_1522_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1515_, v___x_1518_, v_env_1517_, v_asyncMode_1520_, v___x_1521_);
v___x_1523_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1522_, v_n_1512_);
lean_dec(v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_IR_findLocalDecl___redArg(v_n_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec(v_n_1525_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_IR_findLocalDecl___redArg(v_n_1529_, v_a_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_IR_findLocalDecl(v_n_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_n_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v_toEnvExtension_1541_; lean_object* v_asyncMode_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1541_ = lean_ctor_get(v___x_1540_, 0);
v_asyncMode_1542_ = lean_ctor_get(v_toEnvExtension_1541_, 2);
v___x_1543_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1544_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1543_, v___x_1540_, v_env_1539_, v_asyncMode_1542_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v_env_1553_; lean_object* v_nextMacroScope_1554_; lean_object* v_ngen_1555_; lean_object* v_auxDeclNGen_1556_; lean_object* v_traceState_1557_; lean_object* v_messages_1558_; lean_object* v_infoState_1559_; lean_object* v_snapshotTasks_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1576_; 
v___x_1552_ = lean_st_ref_take(v_a_1550_);
v_env_1553_ = lean_ctor_get(v___x_1552_, 0);
v_nextMacroScope_1554_ = lean_ctor_get(v___x_1552_, 1);
v_ngen_1555_ = lean_ctor_get(v___x_1552_, 2);
v_auxDeclNGen_1556_ = lean_ctor_get(v___x_1552_, 3);
v_traceState_1557_ = lean_ctor_get(v___x_1552_, 4);
v_messages_1558_ = lean_ctor_get(v___x_1552_, 6);
v_infoState_1559_ = lean_ctor_get(v___x_1552_, 7);
v_snapshotTasks_1560_ = lean_ctor_get(v___x_1552_, 8);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1552_, 5);
lean_dec(v_unused_1577_);
v___x_1562_ = v___x_1552_;
v_isShared_1563_ = v_isSharedCheck_1576_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snapshotTasks_1560_);
lean_inc(v_infoState_1559_);
lean_inc(v_messages_1558_);
lean_inc(v_traceState_1557_);
lean_inc(v_auxDeclNGen_1556_);
lean_inc(v_ngen_1555_);
lean_inc(v_nextMacroScope_1554_);
lean_inc(v_env_1553_);
lean_dec(v___x_1552_);
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
v___x_1569_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1564_, v_env_1553_, v_decl_1549_, v_asyncMode_1566_, v___x_1568_);
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
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_nextMacroScope_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_ngen_1555_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_auxDeclNGen_1556_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_traceState_1557_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_messages_1558_);
lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_infoState_1559_);
lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_snapshotTasks_1560_);
v___x_1572_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_st_ref_put(v_a_1550_, v___x_1572_);
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
