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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_;
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
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3_value;
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
static lean_once_cell_t l_Lean_IR_addDecl___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addDecl___redArg___closed__2;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value;
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
v___x_153_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_158_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v_options_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_176_);
v_options_178_ = lean_ctor_get(v___y_173_, 2);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_178_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_177_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set(v___x_181_, 3, v_options_178_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_172_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_188_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0(void){
_start:
{
lean_object* v___x_189_; double v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_float_of_nat(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object* v_cls_194_, lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_245_; 
v_ref_199_ = lean_ctor_get(v___y_196_, 5);
v___x_200_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_195_, v___y_196_, v___y_197_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_245_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_245_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_245_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v_traceState_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_cache_211_; lean_object* v_messages_212_; lean_object* v_infoState_213_; lean_object* v_snapshotTasks_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_244_; 
v___x_205_ = lean_st_ref_take(v___y_197_);
v_traceState_206_ = lean_ctor_get(v___x_205_, 4);
v_env_207_ = lean_ctor_get(v___x_205_, 0);
v_nextMacroScope_208_ = lean_ctor_get(v___x_205_, 1);
v_ngen_209_ = lean_ctor_get(v___x_205_, 2);
v_auxDeclNGen_210_ = lean_ctor_get(v___x_205_, 3);
v_cache_211_ = lean_ctor_get(v___x_205_, 5);
v_messages_212_ = lean_ctor_get(v___x_205_, 6);
v_infoState_213_ = lean_ctor_get(v___x_205_, 7);
v_snapshotTasks_214_ = lean_ctor_get(v___x_205_, 8);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_244_ == 0)
{
v___x_216_ = v___x_205_;
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_snapshotTasks_214_);
lean_inc(v_infoState_213_);
lean_inc(v_messages_212_);
lean_inc(v_cache_211_);
lean_inc(v_traceState_206_);
lean_inc(v_auxDeclNGen_210_);
lean_inc(v_ngen_209_);
lean_inc(v_nextMacroScope_208_);
lean_inc(v_env_207_);
lean_dec(v___x_205_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint64_t v_tid_218_; lean_object* v_traces_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_243_; 
v_tid_218_ = lean_ctor_get_uint64(v_traceState_206_, sizeof(void*)*1);
v_traces_219_ = lean_ctor_get(v_traceState_206_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_traceState_206_);
if (v_isSharedCheck_243_ == 0)
{
v___x_221_ = v_traceState_206_;
v_isShared_222_ = v_isSharedCheck_243_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_traces_219_);
lean_dec(v_traceState_206_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_243_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; double v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_223_ = lean_box(0);
v___x_224_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_225_ = 0;
v___x_226_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_227_, 0, v_cls_194_);
lean_ctor_set(v___x_227_, 1, v___x_223_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
lean_ctor_set_float(v___x_227_, sizeof(void*)*3, v___x_224_);
lean_ctor_set_float(v___x_227_, sizeof(void*)*3 + 8, v___x_224_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*3 + 16, v___x_225_);
v___x_228_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_229_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v_a_201_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_inc(v_ref_199_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_ref_199_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_PersistentArray_push___redArg(v_traces_219_, v___x_230_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_231_);
v___x_233_ = v___x_221_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_231_);
lean_ctor_set_uint64(v_reuseFailAlloc_242_, sizeof(void*)*1, v_tid_218_);
v___x_233_ = v_reuseFailAlloc_242_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 4, v___x_233_);
v___x_235_ = v___x_216_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_env_207_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_cache_211_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_messages_212_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v_infoState_213_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v_snapshotTasks_214_);
v___x_235_ = v_reuseFailAlloc_241_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = lean_st_ref_set(v___y_197_, v___x_235_);
v___x_237_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_237_);
v___x_239_ = v___x_203_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_246_, v_msg_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_262_ = l_Lean_IR_LogEntry_fmt(v_entry_257_);
v___x_263_ = l_Lean_MessageData_ofFormat(v___x_262_);
v___x_264_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_261_, v___x_263_, v_a_258_, v_a_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_IR_log(v_entry_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_269_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_278_, lean_object* v_optName_279_){
_start:
{
lean_object* v_map_280_; lean_object* v___x_287_; 
v_map_280_ = lean_ctor_get(v_opts_278_, 0);
v___x_287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_280_, v_optName_279_);
if (lean_obj_tag(v___x_287_) == 1)
{
lean_object* v_val_288_; 
v_val_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v___x_287_, 1);
if (lean_obj_tag(v_val_288_) == 1)
{
uint8_t v_v_289_; 
v_v_289_ = lean_ctor_get_uint8(v_val_288_, 0);
lean_dec_ref_known(v_val_288_, 0);
return v_v_289_;
}
else
{
lean_dec(v_val_288_);
goto v___jp_281_;
}
}
else
{
lean_dec(v___x_287_);
goto v___jp_281_;
}
v___jp_281_:
{
lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_283_ = 0;
v___x_284_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_280_, v___x_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
return v___x_283_;
}
else
{
lean_object* v_val_285_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_284_, 1);
if (lean_obj_tag(v_val_285_) == 1)
{
uint8_t v_v_286_; 
v_v_286_ = lean_ctor_get_uint8(v_val_285_, 0);
lean_dec_ref_known(v_val_285_, 0);
return v_v_286_;
}
else
{
lean_dec(v_val_285_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_290_, lean_object* v_optName_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_290_, v_optName_291_);
lean_dec(v_optName_291_);
lean_dec_ref(v_opts_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_294_, lean_object* v_cls_295_, lean_object* v_decls_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_options_300_; uint8_t v___x_301_; 
v_options_300_ = lean_ctor_get(v_a_297_, 2);
v___x_301_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_300_, v_optName_294_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_decls_296_);
lean_dec(v_cls_295_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_cls_295_);
lean_ctor_set(v___x_304_, 1, v_decls_296_);
v___x_305_ = l_Lean_IR_log(v___x_304_, v_a_297_, v_a_298_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_306_, lean_object* v_cls_307_, lean_object* v_decls_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_306_, v_cls_307_, v_decls_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_optName_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_313_, lean_object* v_decl_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_313_);
v___x_319_ = l_Lean_Name_append(v___x_318_, v_cls_313_);
v___x_320_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_319_, v_cls_313_, v_decl_314_, v_a_315_, v_a_316_);
lean_dec(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_321_, lean_object* v_decl_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_IR_logDecls(v_cls_321_, v_decl_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_327_, lean_object* v_optName_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_options_333_; uint8_t v___x_334_; 
v_options_333_ = lean_ctor_get(v_a_330_, 2);
v___x_334_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_333_, v_optName_328_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_a_329_);
lean_dec_ref(v_inst_327_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_apply_1(v_inst_327_, v_a_329_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = l_Lean_IR_log(v___x_338_, v_a_330_, v_a_331_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_340_, lean_object* v_optName_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_340_, v_optName_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_optName_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_optName_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_348_, v_optName_349_, v_a_350_, v_a_351_, v_a_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_355_, lean_object* v_inst_356_, lean_object* v_optName_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_355_, v_inst_356_, v_optName_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_optName_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_363_, lean_object* v_cls_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_370_ = l_Lean_Name_append(v___x_369_, v_cls_364_);
v___x_371_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_363_, v___x_370_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_372_, lean_object* v_cls_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_IR_logMessageIf___redArg(v_inst_372_, v_cls_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_cls_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_387_ = l_Lean_Name_append(v___x_386_, v_cls_381_);
v___x_388_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_380_, v___x_387_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_389_, lean_object* v_inst_390_, lean_object* v_cls_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_IR_logMessageIf(v_00_u03b1_389_, v_inst_390_, v_cls_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_403_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_397_, v___x_402_, v_a_398_, v_a_399_, v_a_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_IR_logMessage___redArg(v_inst_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_410_, lean_object* v_inst_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_417_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_411_, v___x_416_, v_a_412_, v_a_413_, v_a_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_IR_logMessage(v_00_u03b1_418_, v_inst_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_425_, lean_object* v_b_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = l_Lean_IR_Decl_name(v_a_425_);
v___x_428_ = l_Lean_IR_Decl_name(v_b_426_);
v___x_429_ = l_Lean_Name_quickLt(v___x_427_, v___x_428_);
lean_dec(v___x_428_);
lean_dec(v___x_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_430_, v_b_431_);
lean_dec_ref(v_b_431_);
lean_dec_ref(v_a_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_array_get_size(v_decls_435_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_nat_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___y_443_; uint8_t v___x_447_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_sub(v___x_436_, v___x_440_);
v___x_447_ = lean_nat_dec_le(v___x_437_, v___x_441_);
if (v___x_447_ == 0)
{
lean_inc(v___x_441_);
v___y_443_ = v___x_441_;
goto v___jp_442_;
}
else
{
v___y_443_ = v___x_437_;
goto v___jp_442_;
}
v___jp_442_:
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v___y_443_, v___x_441_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v___x_441_);
lean_inc(v___y_443_);
v___x_445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_439_, v___x_436_, v_decls_435_, v___y_443_, v___y_443_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_443_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_439_, v___x_436_, v_decls_435_, v___y_443_, v___x_441_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_441_);
return v___x_446_;
}
}
}
else
{
return v_decls_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_451_, lean_object* v_declName_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_array_get_size(v_decls_451_);
v___x_455_ = lean_nat_dec_lt(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v_declName_452_);
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_sub(v___x_454_, v___x_457_);
v___x_459_ = lean_nat_dec_le(v___x_453_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v___x_458_);
lean_dec(v_declName_452_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_tmpDecl_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_462_ = lean_box(0);
v___x_463_ = lean_box(0);
v_tmpDecl_464_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_464_, 0, v_declName_452_);
lean_ctor_set(v_tmpDecl_464_, 1, v___x_461_);
lean_ctor_set(v_tmpDecl_464_, 2, v___x_462_);
lean_ctor_set(v_tmpDecl_464_, 3, v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_466_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_467_ = l_Array_binSearchAux___redArg(v___x_465_, v___x_466_, v_decls_451_, v_tmpDecl_464_, v___x_453_, v___x_458_);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_468_, lean_object* v_declName_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_468_, v_declName_469_);
lean_dec_ref(v_decls_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_471_, lean_object* v_pivot_472_, lean_object* v_as_473_, lean_object* v_i_474_, lean_object* v_k_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_lt(v_k_475_, v_hi_471_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_k_475_);
v___x_477_ = lean_array_fswap(v_as_473_, v_i_474_, v_hi_471_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_i_474_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_array_fget_borrowed(v_as_473_, v_k_475_);
v___x_480_ = l_Lean_IR_Decl_name(v___x_479_);
v___x_481_ = l_Lean_IR_Decl_name(v_pivot_472_);
v___x_482_ = l_Lean_Name_quickLt(v___x_480_, v___x_481_);
lean_dec(v___x_481_);
lean_dec(v___x_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_k_475_, v___x_483_);
lean_dec(v_k_475_);
v_k_475_ = v___x_484_;
goto _start;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_array_fswap(v_as_473_, v_i_474_, v_k_475_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_i_474_, v___x_487_);
lean_dec(v_i_474_);
v___x_489_ = lean_nat_add(v_k_475_, v___x_487_);
lean_dec(v_k_475_);
v_as_473_ = v___x_486_;
v_i_474_ = v___x_488_;
v_k_475_ = v___x_489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_491_, lean_object* v_pivot_492_, lean_object* v_as_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_491_, v_pivot_492_, v_as_493_, v_i_494_, v_k_495_);
lean_dec_ref(v_pivot_492_);
lean_dec(v_hi_491_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = l_Lean_IR_Decl_name(v___y_497_);
v___x_500_ = l_Lean_IR_Decl_name(v___y_498_);
v___x_501_ = l_Lean_Name_quickLt(v___x_499_, v___x_500_);
lean_dec(v___x_500_);
lean_dec(v___x_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_502_, v___y_503_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v___y_502_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_506_, lean_object* v_as_507_, lean_object* v_lo_508_, lean_object* v_hi_509_){
_start:
{
lean_object* v___y_511_; uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_lt(v_lo_508_, v_hi_509_);
if (v___x_521_ == 0)
{
lean_dec(v_lo_508_);
return v_as_507_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_mid_524_; lean_object* v___y_526_; lean_object* v___y_532_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_522_ = lean_nat_add(v_lo_508_, v_hi_509_);
v___x_523_ = lean_unsigned_to_nat(1u);
v_mid_524_ = lean_nat_shiftr(v___x_522_, v___x_523_);
lean_dec(v___x_522_);
v___x_537_ = lean_array_fget_borrowed(v_as_507_, v_mid_524_);
v___x_538_ = lean_array_fget_borrowed(v_as_507_, v_lo_508_);
v___x_539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
v___y_532_ = v_as_507_;
goto v___jp_531_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = lean_array_fswap(v_as_507_, v_lo_508_, v_mid_524_);
v___y_532_ = v___x_540_;
goto v___jp_531_;
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_array_fget_borrowed(v___y_526_, v_mid_524_);
v___x_528_ = lean_array_fget_borrowed(v___y_526_, v_hi_509_);
v___x_529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v_mid_524_);
v___y_511_ = v___y_526_;
goto v___jp_510_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_array_fswap(v___y_526_, v_mid_524_, v_hi_509_);
lean_dec(v_mid_524_);
v___y_511_ = v___x_530_;
goto v___jp_510_;
}
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_array_fget_borrowed(v___y_532_, v_hi_509_);
v___x_534_ = lean_array_fget_borrowed(v___y_532_, v_lo_508_);
v___x_535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
v___y_526_ = v___y_532_;
goto v___jp_525_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_array_fswap(v___y_532_, v_lo_508_, v_hi_509_);
v___y_526_ = v___x_536_;
goto v___jp_525_;
}
}
}
v___jp_510_:
{
lean_object* v_pivot_512_; lean_object* v___x_513_; lean_object* v_fst_514_; lean_object* v_snd_515_; uint8_t v___x_516_; 
v_pivot_512_ = lean_array_fget(v___y_511_, v_hi_509_);
lean_inc_n(v_lo_508_, 2);
v___x_513_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_509_, v_pivot_512_, v___y_511_, v_lo_508_, v_lo_508_);
lean_dec(v_pivot_512_);
v_fst_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_fst_514_);
v_snd_515_ = lean_ctor_get(v___x_513_, 1);
lean_inc(v_snd_515_);
lean_dec_ref(v___x_513_);
v___x_516_ = lean_nat_dec_le(v_hi_509_, v_fst_514_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_506_, v_snd_515_, v_lo_508_, v_fst_514_);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_fst_514_, v___x_518_);
lean_dec(v_fst_514_);
v_as_507_ = v___x_517_;
v_lo_508_ = v___x_519_;
goto _start;
}
else
{
lean_dec(v_fst_514_);
lean_dec(v_lo_508_);
return v_snd_515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_541_, lean_object* v_as_542_, lean_object* v_lo_543_, lean_object* v_hi_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_541_, v_as_542_, v_lo_543_, v_hi_544_);
lean_dec(v_hi_544_);
lean_dec(v_n_541_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_552_, lean_object* v_as_553_, size_t v_i_554_, size_t v_stop_555_, lean_object* v_b_556_){
_start:
{
lean_object* v___y_558_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_eq(v_i_554_, v_stop_555_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; uint8_t v___y_572_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_570_ = lean_array_uget_borrowed(v_as_553_, v_i_554_);
v___x_587_ = l_Lean_IR_Decl_name(v___x_570_);
lean_inc_ref(v_env_552_);
v___x_588_ = l_Lean_isDeclMeta(v_env_552_, v___x_587_);
if (v___x_588_ == 0)
{
uint8_t v___x_589_; 
lean_inc_ref(v_env_552_);
v___x_589_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_552_, v___x_587_);
if (v___x_589_ == 0)
{
lean_dec(v___x_587_);
v___y_558_ = v_b_556_;
goto v___jp_557_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_587_);
if (v___x_590_ == 0)
{
lean_dec(v___x_587_);
v___y_572_ = v___x_590_;
goto v___jp_571_;
}
else
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = l_Lean_Name_getPrefix(v___x_587_);
lean_dec(v___x_587_);
lean_inc_ref(v_env_552_);
v___x_592_ = l_Lean_isExtern(v_env_552_, v___x_591_);
v___y_572_ = v___x_592_;
goto v___jp_571_;
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec(v___x_587_);
lean_inc(v___x_570_);
v___x_593_ = lean_array_push(v_b_556_, v___x_570_);
v___y_558_ = v___x_593_;
goto v___jp_557_;
}
v___jp_571_:
{
if (v___y_572_ == 0)
{
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_f_573_; lean_object* v_xs_574_; lean_object* v_type_575_; lean_object* v___x_576_; 
v_f_573_ = lean_ctor_get(v___x_570_, 0);
v_xs_574_ = lean_ctor_get(v___x_570_, 1);
v_type_575_ = lean_ctor_get(v___x_570_, 2);
lean_inc(v_f_573_);
lean_inc_ref(v_env_552_);
v___x_576_ = lean_get_export_name_for(v_env_552_, v_f_573_);
if (lean_obj_tag(v___x_576_) == 1)
{
lean_object* v_val_577_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_576_, 1);
if (lean_obj_tag(v_val_577_) == 1)
{
lean_object* v_str_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_str_578_ = lean_ctor_get(v_val_577_, 1);
lean_inc_ref(v_str_578_);
lean_dec_ref_known(v_val_577_, 2);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_str_578_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
lean_inc(v_type_575_);
lean_inc_ref(v_xs_574_);
lean_inc(v_f_573_);
v___x_583_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_583_, 0, v_f_573_);
lean_ctor_set(v___x_583_, 1, v_xs_574_);
lean_ctor_set(v___x_583_, 2, v_type_575_);
lean_ctor_set(v___x_583_, 3, v___x_582_);
v___x_584_ = lean_array_push(v_b_556_, v___x_583_);
v___y_558_ = v___x_584_;
goto v___jp_557_;
}
else
{
lean_dec(v_val_577_);
lean_inc(v_f_573_);
lean_inc(v_type_575_);
lean_inc_ref(v_xs_574_);
v___y_563_ = v_xs_574_;
v___y_564_ = v_type_575_;
v___y_565_ = v_f_573_;
goto v___jp_562_;
}
}
else
{
lean_dec(v___x_576_);
lean_inc(v_f_573_);
lean_inc(v_type_575_);
lean_inc_ref(v_xs_574_);
v___y_563_ = v_xs_574_;
v___y_564_ = v_type_575_;
v___y_565_ = v_f_573_;
goto v___jp_562_;
}
}
else
{
lean_object* v___x_585_; 
lean_inc(v___x_570_);
v___x_585_ = lean_array_push(v_b_556_, v___x_570_);
v___y_558_ = v___x_585_;
goto v___jp_557_;
}
}
else
{
lean_object* v___x_586_; 
lean_inc(v___x_570_);
v___x_586_ = lean_array_push(v_b_556_, v___x_570_);
v___y_558_ = v___x_586_;
goto v___jp_557_;
}
}
}
else
{
lean_dec_ref(v_env_552_);
return v_b_556_;
}
v___jp_557_:
{
size_t v___x_559_; size_t v___x_560_; 
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_554_, v___x_559_);
v_i_554_ = v___x_560_;
v_b_556_ = v___y_558_;
goto _start;
}
v___jp_562_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_567_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_567_, 0, v___y_565_);
lean_ctor_set(v___x_567_, 1, v___y_563_);
lean_ctor_set(v___x_567_, 2, v___y_564_);
lean_ctor_set(v___x_567_, 3, v___x_566_);
v___x_568_ = lean_array_push(v_b_556_, v___x_567_);
v___y_558_ = v___x_568_;
goto v___jp_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_594_, lean_object* v_as_595_, lean_object* v_i_596_, lean_object* v_stop_597_, lean_object* v_b_598_){
_start:
{
size_t v_i_boxed_599_; size_t v_stop_boxed_600_; lean_object* v_res_601_; 
v_i_boxed_599_ = lean_unbox_usize(v_i_596_);
lean_dec(v_i_596_);
v_stop_boxed_600_ = lean_unbox_usize(v_stop_597_);
lean_dec(v_stop_597_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_594_, v_as_595_, v_i_boxed_599_, v_stop_boxed_600_, v_b_598_);
lean_dec_ref(v_as_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_604_, lean_object* v_as_605_, lean_object* v_start_606_, lean_object* v_stop_607_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_609_ = lean_nat_dec_lt(v_start_606_, v_stop_607_);
if (v___x_609_ == 0)
{
lean_dec_ref(v_env_604_);
return v___x_608_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_as_605_);
v___x_611_ = lean_nat_dec_le(v_stop_607_, v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_lt(v_start_606_, v___x_610_);
if (v___x_612_ == 0)
{
lean_dec_ref(v_env_604_);
return v___x_608_;
}
else
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_usize_of_nat(v_start_606_);
v___x_614_ = lean_usize_of_nat(v___x_610_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_604_, v_as_605_, v___x_613_, v___x_614_, v___x_608_);
return v___x_615_;
}
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_usize_of_nat(v_start_606_);
v___x_617_ = lean_usize_of_nat(v_stop_607_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_604_, v_as_605_, v___x_616_, v___x_617_, v___x_608_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_619_, lean_object* v_as_620_, lean_object* v_start_621_, lean_object* v_stop_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_619_, v_as_620_, v_start_621_, v_stop_622_);
lean_dec(v_stop_622_);
lean_dec(v_start_621_);
lean_dec_ref(v_as_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
return v_x_624_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; 
v_head_626_ = lean_ctor_get(v_x_625_, 0);
lean_inc(v_head_626_);
v_tail_627_ = lean_ctor_get(v_x_625_, 1);
lean_inc(v_tail_627_);
lean_dec_ref_known(v_x_625_, 2);
v___x_628_ = lean_array_push(v_x_624_, v_head_626_);
v_x_624_ = v___x_628_;
v_x_625_ = v_tail_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_630_, lean_object* v_s_631_, lean_object* v_entries_632_){
_start:
{
lean_object* v___y_634_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_decls_644_; lean_object* v___x_645_; lean_object* v___y_647_; lean_object* v___y_648_; uint8_t v___x_650_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_644_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_643_, v_entries_632_);
v___x_645_ = lean_array_get_size(v_decls_644_);
v___x_650_ = lean_nat_dec_eq(v___x_645_, v___x_642_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___y_654_; uint8_t v___x_656_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_sub(v___x_645_, v___x_651_);
v___x_656_ = lean_nat_dec_le(v___x_642_, v___x_652_);
if (v___x_656_ == 0)
{
lean_inc(v___x_652_);
v___y_654_ = v___x_652_;
goto v___jp_653_;
}
else
{
v___y_654_ = v___x_642_;
goto v___jp_653_;
}
v___jp_653_:
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_le(v___y_654_, v___x_652_);
if (v___x_655_ == 0)
{
lean_dec(v___x_652_);
lean_inc(v___y_654_);
v___y_647_ = v___y_654_;
v___y_648_ = v___y_654_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___y_654_;
v___y_648_ = v___x_652_;
goto v___jp_646_;
}
}
}
else
{
v___y_634_ = v_decls_644_;
goto v___jp_633_;
}
v___jp_633_:
{
lean_object* v___x_635_; uint8_t v_isModule_636_; 
v___x_635_ = l_Lean_Environment_header(v_env_630_);
v_isModule_636_ = lean_ctor_get_uint8(v___x_635_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_635_);
if (v_isModule_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec_ref(v_env_630_);
lean_inc_ref_n(v___y_634_, 2);
v___x_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_637_, 0, v___y_634_);
lean_ctor_set(v___x_637_, 1, v___y_634_);
lean_ctor_set(v___x_637_, 2, v___y_634_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_array_get_size(v___y_634_);
v___x_640_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_630_, v___y_634_, v___x_638_, v___x_639_);
lean_dec_ref(v___y_634_);
lean_inc_ref_n(v___x_640_, 2);
v___x_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_ctor_set(v___x_641_, 2, v___x_640_);
return v___x_641_;
}
}
v___jp_646_:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_645_, v_decls_644_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
v___y_634_ = v___x_649_;
goto v___jp_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_657_, lean_object* v_s_658_, lean_object* v_entries_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_657_, v_s_658_, v_entries_659_);
lean_dec_ref(v_s_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lean_array_mk(v_es_661_);
return v___x_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object* v_keys_663_, lean_object* v_i_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_get_size(v_keys_663_);
v___x_667_ = lean_nat_dec_lt(v_i_664_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec(v_i_664_);
return v___x_667_;
}
else
{
lean_object* v_k_x27_668_; uint8_t v___x_669_; 
v_k_x27_668_ = lean_array_fget_borrowed(v_keys_663_, v_i_664_);
v___x_669_ = lean_name_eq(v_k_665_, v_k_x27_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_i_664_, v___x_670_);
lean_dec(v_i_664_);
v_i_664_ = v___x_671_;
goto _start;
}
else
{
lean_dec(v_i_664_);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_673_, lean_object* v_i_674_, lean_object* v_k_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_673_, v_i_674_, v_k_675_);
lean_dec(v_k_675_);
lean_dec_ref(v_keys_673_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_678_, size_t v_x_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_object* v_es_681_; lean_object* v___x_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v_j_685_; lean_object* v___x_686_; 
v_es_681_ = lean_ctor_get(v_x_678_, 0);
v___x_682_ = lean_box(2);
v___x_683_ = ((size_t)31ULL);
v___x_684_ = lean_usize_land(v_x_679_, v___x_683_);
v_j_685_ = lean_usize_to_nat(v___x_684_);
v___x_686_ = lean_array_get_borrowed(v___x_682_, v_es_681_, v_j_685_);
lean_dec(v_j_685_);
switch(lean_obj_tag(v___x_686_))
{
case 0:
{
lean_object* v_key_687_; uint8_t v___x_688_; 
v_key_687_ = lean_ctor_get(v___x_686_, 0);
v___x_688_ = lean_name_eq(v_x_680_, v_key_687_);
return v___x_688_;
}
case 1:
{
lean_object* v_node_689_; size_t v___x_690_; size_t v___x_691_; 
v_node_689_ = lean_ctor_get(v___x_686_, 0);
v___x_690_ = ((size_t)5ULL);
v___x_691_ = lean_usize_shift_right(v_x_679_, v___x_690_);
v_x_678_ = v_node_689_;
v_x_679_ = v___x_691_;
goto _start;
}
default: 
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
}
else
{
lean_object* v_ks_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_ks_694_ = lean_ctor_get(v_x_678_, 0);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_694_, v___x_695_, v_x_680_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
size_t v_x_2605__boxed_700_; uint8_t v_res_701_; lean_object* v_r_702_; 
v_x_2605__boxed_700_ = lean_unbox_usize(v_x_698_);
lean_dec(v_x_698_);
v_res_701_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_697_, v_x_2605__boxed_700_, v_x_699_);
lean_dec(v_x_699_);
lean_dec_ref(v_x_697_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_703_; uint64_t v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(1723u);
v___x_704_ = lean_uint64_of_nat(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
uint64_t v___y_708_; 
if (lean_obj_tag(v_x_706_) == 0)
{
uint64_t v___x_711_; 
v___x_711_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
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
lean_object* v___x_719_; uint8_t v___x_720_; uint8_t v___x_721_; 
v___x_719_ = l_Lean_IR_Decl_name(v_x2_718_);
v___x_720_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_717_, v___x_719_);
lean_dec(v___x_719_);
v___x_721_ = lean_bool_not(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_722_, lean_object* v_x2_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_722_, v_x2_723_);
lean_dec_ref(v_x2_723_);
lean_dec_ref(v_x1_722_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_726_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
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
v___x_768_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_820_; lean_object* v_vs_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_841_; 
v_ks_820_ = lean_ctor_get(v_x_769_, 0);
v_vs_821_ = lean_ctor_get(v_x_769_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_841_ == 0)
{
v___x_823_ = v_x_769_;
v_isShared_824_ = v_isSharedCheck_841_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_vs_821_);
lean_inc(v_ks_820_);
lean_dec(v_x_769_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_841_;
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
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_ks_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_vs_821_);
v___x_826_ = v_reuseFailAlloc_840_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v_newNode_827_; uint8_t v___y_829_; size_t v___x_835_; uint8_t v___x_836_; 
v_newNode_827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_826_, v_x_772_, v_x_773_);
v___x_835_ = ((size_t)7ULL);
v___x_836_ = lean_usize_dec_le(v___x_835_, v_x_771_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_827_);
v___x_838_ = lean_unsigned_to_nat(4u);
v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
lean_dec(v___x_837_);
v___y_829_ = v___x_839_;
goto v___jp_828_;
}
else
{
v___y_829_ = v___x_836_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v_ks_830_; lean_object* v_vs_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_ks_830_ = lean_ctor_get(v_newNode_827_, 0);
lean_inc_ref(v_ks_830_);
v_vs_831_ = lean_ctor_get(v_newNode_827_, 1);
lean_inc_ref(v_vs_831_);
lean_dec_ref(v_newNode_827_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_771_, v_ks_830_, v_vs_831_, v___x_832_, v___x_833_);
lean_dec_ref(v_vs_831_);
lean_dec_ref(v_ks_830_);
return v___x_834_;
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
v___x_863_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
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
size_t v_x_2775__boxed_877_; size_t v_x_2776__boxed_878_; lean_object* v_res_879_; 
v_x_2775__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_x_2776__boxed_878_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_872_, v_x_2775__boxed_877_, v_x_2776__boxed_878_, v_x_875_, v_x_876_);
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
v___x_888_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
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
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_922_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_925_, lean_object* v_as_926_, lean_object* v_lo_927_, lean_object* v_hi_928_, lean_object* v_w_929_, lean_object* v_hlo_930_, lean_object* v_hhi_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_925_, v_as_926_, v_lo_927_, v_hi_928_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_933_, lean_object* v_as_934_, lean_object* v_lo_935_, lean_object* v_hi_936_, lean_object* v_w_937_, lean_object* v_hlo_938_, lean_object* v_hhi_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_933_, v_as_934_, v_lo_935_, v_hi_936_, v_w_937_, v_hlo_938_, v_hhi_939_);
lean_dec(v_hi_936_);
lean_dec(v_n_933_);
return v_res_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_942_, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_945_, v_x_946_, v_x_947_);
lean_dec(v_x_947_);
lean_dec_ref(v_x_946_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_955_, lean_object* v_lo_956_, lean_object* v_hi_957_, lean_object* v_hhi_958_, lean_object* v_pivot_959_, lean_object* v_as_960_, lean_object* v_i_961_, lean_object* v_k_962_, lean_object* v_ilo_963_, lean_object* v_ik_964_, lean_object* v_w_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_957_, v_pivot_959_, v_as_960_, v_i_961_, v_k_962_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_967_, lean_object* v_lo_968_, lean_object* v_hi_969_, lean_object* v_hhi_970_, lean_object* v_pivot_971_, lean_object* v_as_972_, lean_object* v_i_973_, lean_object* v_k_974_, lean_object* v_ilo_975_, lean_object* v_ik_976_, lean_object* v_w_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_967_, v_lo_968_, v_hi_969_, v_hhi_970_, v_pivot_971_, v_as_972_, v_i_973_, v_k_974_, v_ilo_975_, v_ik_976_, v_w_977_);
lean_dec_ref(v_pivot_971_);
lean_dec(v_hi_969_);
lean_dec(v_lo_968_);
lean_dec(v_n_967_);
return v_res_978_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, size_t v_x_981_, lean_object* v_x_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_980_, v_x_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
size_t v_x_3064__boxed_988_; uint8_t v_res_989_; lean_object* v_r_990_; 
v_x_3064__boxed_988_ = lean_unbox_usize(v_x_986_);
lean_dec(v_x_986_);
v_res_989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_984_, v_x_985_, v_x_3064__boxed_988_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_x_985_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_991_, lean_object* v_x_992_, size_t v_x_993_, size_t v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_992_, v_x_993_, v_x_994_, v_x_995_, v_x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
size_t v_x_3075__boxed_1004_; size_t v_x_3076__boxed_1005_; lean_object* v_res_1006_; 
v_x_3075__boxed_1004_ = lean_unbox_usize(v_x_1000_);
lean_dec(v_x_1000_);
v_x_3076__boxed_1005_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_res_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_998_, v_x_999_, v_x_3075__boxed_1004_, v_x_3076__boxed_1005_, v_x_1002_, v_x_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1007_, lean_object* v_keys_1008_, lean_object* v_vals_1009_, lean_object* v_heq_1010_, lean_object* v_i_1011_, lean_object* v_k_1012_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_1008_, v_i_1011_, v_k_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_heq_1017_, lean_object* v_i_1018_, lean_object* v_k_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1014_, v_keys_1015_, v_vals_1016_, v_heq_1017_, v_i_1018_, v_k_1019_);
lean_dec(v_k_1019_);
lean_dec_ref(v_vals_1016_);
lean_dec_ref(v_keys_1015_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1022_, lean_object* v_n_1023_, lean_object* v_k_1024_, lean_object* v_v_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1023_, v_k_1024_, v_v_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1027_, size_t v_depth_1028_, lean_object* v_keys_1029_, lean_object* v_vals_1030_, lean_object* v_heq_1031_, lean_object* v_i_1032_, lean_object* v_entries_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1028_, v_keys_1029_, v_vals_1030_, v_i_1032_, v_entries_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1035_, lean_object* v_depth_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_entries_1041_){
_start:
{
size_t v_depth_boxed_1042_; lean_object* v_res_1043_; 
v_depth_boxed_1042_ = lean_unbox_usize(v_depth_1036_);
lean_dec(v_depth_1036_);
v_res_1043_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1035_, v_depth_boxed_1042_, v_keys_1037_, v_vals_1038_, v_heq_1039_, v_i_1040_, v_entries_1041_);
lean_dec_ref(v_vals_1038_);
lean_dec_ref(v_keys_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1045_, v_x_1046_, v_x_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1051_ = lean_array_get_size(v_irDecls_1050_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_nat_dec_eq(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___y_1057_; uint8_t v___x_1061_; 
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_sub(v___x_1051_, v___x_1054_);
v___x_1061_ = lean_nat_dec_le(v___x_1052_, v___x_1055_);
if (v___x_1061_ == 0)
{
lean_inc(v___x_1055_);
v___y_1057_ = v___x_1055_;
goto v___jp_1056_;
}
else
{
v___y_1057_ = v___x_1052_;
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
v___x_1059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1051_, v_irDecls_1050_, v___y_1057_, v___y_1057_);
lean_dec(v___y_1057_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1051_, v_irDecls_1050_, v___y_1057_, v___x_1055_);
lean_dec(v___x_1055_);
return v___x_1060_;
}
}
}
else
{
return v_irDecls_1050_;
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
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1071_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0));
v___x_1072_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1071_, v___x_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v_toEnvExtension_1078_; lean_object* v_name_1079_; lean_object* v_asyncMode_1080_; lean_object* v___x_1081_; lean_object* v_ext_1082_; lean_object* v_toEnvExtension_1083_; lean_object* v_name_1084_; lean_object* v_exportEntriesFn_1085_; lean_object* v_asyncMode_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_private_1093_; lean_object* v___x_1094_; lean_object* v_toEnvExtension_1095_; lean_object* v_name_1096_; lean_object* v_exportEntriesFn_1097_; lean_object* v_asyncMode_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_private_1102_; lean_object* v___x_1103_; lean_object* v_irDecls_1104_; lean_object* v_irEntries_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1077_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1078_ = lean_ctor_get(v___x_1077_, 0);
v_name_1079_ = lean_ctor_get(v___x_1077_, 1);
v_asyncMode_1080_ = lean_ctor_get(v_toEnvExtension_1078_, 2);
v___x_1081_ = l_Lean_regularInitAttr;
v_ext_1082_ = lean_ctor_get(v___x_1081_, 1);
v_toEnvExtension_1083_ = lean_ctor_get(v_ext_1082_, 0);
v_name_1084_ = lean_ctor_get(v_ext_1082_, 1);
v_exportEntriesFn_1085_ = lean_ctor_get(v_ext_1082_, 4);
v_asyncMode_1086_ = lean_ctor_get(v_toEnvExtension_1083_, 2);
v___x_1087_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1088_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
lean_inc_ref_n(v_env_1076_, 4);
v___x_1089_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1087_, v___x_1077_, v_env_1076_, v_asyncMode_1080_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1088_, v_ext_1082_, v_env_1076_, v_asyncMode_1086_, v___x_1090_);
lean_inc_ref(v_exportEntriesFn_1085_);
v___x_1092_ = lean_apply_2(v_exportEntriesFn_1085_, v_env_1076_, v___x_1091_);
v_private_1093_ = lean_ctor_get(v___x_1092_, 2);
lean_inc(v_private_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1095_ = lean_ctor_get(v___x_1094_, 0);
v_name_1096_ = lean_ctor_get(v___x_1094_, 1);
v_exportEntriesFn_1097_ = lean_ctor_get(v___x_1094_, 4);
v_asyncMode_1098_ = lean_ctor_get(v_toEnvExtension_1095_, 2);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1099_, v___x_1094_, v_env_1076_, v_asyncMode_1098_, v___x_1090_);
lean_inc_ref(v_exportEntriesFn_1097_);
v___x_1101_ = lean_apply_2(v_exportEntriesFn_1097_, v_env_1076_, v___x_1100_);
v_private_1102_ = lean_ctor_get(v___x_1101_, 2);
lean_inc(v_private_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_irDecls_1104_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1103_, v___x_1089_);
v_irEntries_1105_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(v_irDecls_1104_);
lean_inc(v_name_1079_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_name_1079_);
lean_ctor_set(v___x_1106_, 1, v_irEntries_1105_);
lean_inc(v_name_1084_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_name_1084_);
lean_ctor_set(v___x_1107_, 1, v_private_1093_);
lean_inc(v_name_1096_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_name_1096_);
lean_ctor_set(v___x_1108_, 1, v_private_1102_);
v___x_1109_ = lean_unsigned_to_nat(3u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1106_);
v___x_1112_ = lean_array_push(v___x_1111_, v___x_1107_);
v___x_1113_ = lean_array_push(v___x_1112_, v___x_1108_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1114_, lean_object* v_k_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_m_1120_; lean_object* v_a_1121_; uint8_t v___x_1122_; 
v___x_1118_ = lean_nat_add(v_x_1116_, v_x_1117_);
v___x_1119_ = lean_unsigned_to_nat(1u);
v_m_1120_ = lean_nat_shiftr(v___x_1118_, v___x_1119_);
lean_dec(v___x_1118_);
v_a_1121_ = lean_array_fget_borrowed(v_as_1114_, v_m_1120_);
v___x_1122_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1121_, v_k_1115_);
if (v___x_1122_ == 0)
{
uint8_t v___x_1123_; 
lean_dec(v_x_1117_);
v___x_1123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1115_, v_a_1121_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_m_1120_);
lean_dec(v_x_1116_);
lean_inc(v_a_1121_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1121_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_nat_dec_eq(v_m_1120_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_nat_sub(v_m_1120_, v___x_1119_);
lean_dec(v_m_1120_);
v___x_1128_ = lean_nat_dec_lt(v___x_1127_, v_x_1116_);
if (v___x_1128_ == 0)
{
v_x_1117_ = v___x_1127_;
goto _start;
}
else
{
lean_object* v___x_1130_; 
lean_dec(v___x_1127_);
lean_dec(v_x_1116_);
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
}
else
{
lean_object* v___x_1131_; 
lean_dec(v_m_1120_);
lean_dec(v_x_1116_);
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
}
}
else
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
lean_dec(v_x_1116_);
v___x_1132_ = lean_nat_add(v_m_1120_, v___x_1119_);
lean_dec(v_m_1120_);
v___x_1133_ = lean_nat_dec_le(v___x_1132_, v_x_1117_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1132_);
lean_dec(v_x_1117_);
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
v_x_1116_ = v___x_1132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1136_, lean_object* v_k_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1136_, v_k_1137_, v_x_1138_, v_x_1139_);
lean_dec_ref(v_k_1137_);
lean_dec_ref(v_as_1136_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_i_1143_, lean_object* v_k_1144_){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_keys_1141_);
v___x_1146_ = lean_nat_dec_lt(v_i_1143_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec(v_i_1143_);
v___x_1147_ = lean_box(0);
return v___x_1147_;
}
else
{
lean_object* v_k_x27_1148_; uint8_t v___x_1149_; 
v_k_x27_1148_ = lean_array_fget_borrowed(v_keys_1141_, v_i_1143_);
v___x_1149_ = lean_name_eq(v_k_1144_, v_k_x27_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_i_1143_, v___x_1150_);
lean_dec(v_i_1143_);
v_i_1143_ = v___x_1151_;
goto _start;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_array_fget_borrowed(v_vals_1142_, v_i_1143_);
lean_dec(v_i_1143_);
lean_inc(v___x_1153_);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_i_1157_, lean_object* v_k_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1155_, v_vals_1156_, v_i_1157_, v_k_1158_);
lean_dec(v_k_1158_);
lean_dec_ref(v_vals_1156_);
lean_dec_ref(v_keys_1155_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1160_, size_t v_x_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1160_) == 0)
{
lean_object* v_es_1163_; lean_object* v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; lean_object* v_j_1167_; lean_object* v___x_1168_; 
v_es_1163_ = lean_ctor_get(v_x_1160_, 0);
v___x_1164_ = lean_box(2);
v___x_1165_ = ((size_t)31ULL);
v___x_1166_ = lean_usize_land(v_x_1161_, v___x_1165_);
v_j_1167_ = lean_usize_to_nat(v___x_1166_);
v___x_1168_ = lean_array_get_borrowed(v___x_1164_, v_es_1163_, v_j_1167_);
lean_dec(v_j_1167_);
switch(lean_obj_tag(v___x_1168_))
{
case 0:
{
lean_object* v_key_1169_; lean_object* v_val_1170_; uint8_t v___x_1171_; 
v_key_1169_ = lean_ctor_get(v___x_1168_, 0);
v_val_1170_ = lean_ctor_get(v___x_1168_, 1);
v___x_1171_ = lean_name_eq(v_x_1162_, v_key_1169_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_inc(v_val_1170_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_val_1170_);
return v___x_1173_;
}
}
case 1:
{
lean_object* v_node_1174_; size_t v___x_1175_; size_t v___x_1176_; 
v_node_1174_ = lean_ctor_get(v___x_1168_, 0);
v___x_1175_ = ((size_t)5ULL);
v___x_1176_ = lean_usize_shift_right(v_x_1161_, v___x_1175_);
v_x_1160_ = v_node_1174_;
v_x_1161_ = v___x_1176_;
goto _start;
}
default: 
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
}
}
else
{
lean_object* v_ks_1179_; lean_object* v_vs_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_ks_1179_ = lean_ctor_get(v_x_1160_, 0);
v_vs_1180_ = lean_ctor_get(v_x_1160_, 1);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1179_, v_vs_1180_, v___x_1181_, v_x_1162_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
size_t v_x_406__boxed_1186_; lean_object* v_res_1187_; 
v_x_406__boxed_1186_ = lean_unbox_usize(v_x_1184_);
lean_dec(v_x_1184_);
v_res_1187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1183_, v_x_406__boxed_1186_, v_x_1185_);
lean_dec(v_x_1185_);
lean_dec_ref(v_x_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
uint64_t v___y_1191_; 
if (lean_obj_tag(v_x_1189_) == 0)
{
uint64_t v___x_1194_; 
v___x_1194_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_1191_ = v___x_1194_;
goto v___jp_1190_;
}
else
{
uint64_t v_hash_1195_; 
v_hash_1195_ = lean_ctor_get_uint64(v_x_1189_, sizeof(void*)*2);
v___y_1191_ = v_hash_1195_;
goto v___jp_1190_;
}
v___jp_1190_:
{
size_t v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_uint64_to_usize(v___y_1191_);
v___x_1193_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1188_, v___x_1192_, v_x_1189_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1196_, v_x_1197_);
lean_dec(v_x_1197_);
lean_dec_ref(v_x_1196_);
return v_res_1198_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___x_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1202_, lean_object* v_declName_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1214_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1206_ = l_Lean_IR_declMapExt;
v___x_1214_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1202_, v_declName_1203_);
if (lean_obj_tag(v___x_1214_) == 0)
{
goto v___jp_1207_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1229_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1205_, v___x_1206_, v_env_1202_, v_val_1215_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_array_get_size(v___x_1229_);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec_ref(v___x_1229_);
goto v___jp_1216_;
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
goto v___jp_1216_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_tmpDecl_1238_; lean_object* v___x_1239_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1237_ = lean_box(0);
lean_inc(v_declName_1203_);
v_tmpDecl_1238_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1238_, 0, v_declName_1203_);
lean_ctor_set(v_tmpDecl_1238_, 1, v___x_1236_);
lean_ctor_set(v_tmpDecl_1238_, 2, v___x_1237_);
lean_ctor_set(v_tmpDecl_1238_, 3, v___x_1204_);
v___x_1239_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1229_, v_tmpDecl_1238_, v___x_1230_, v___x_1234_);
lean_dec_ref_known(v_tmpDecl_1238_, 4);
lean_dec_ref(v___x_1229_);
if (lean_obj_tag(v___x_1239_) == 0)
{
goto v___jp_1216_;
}
else
{
lean_dec(v_val_1215_);
lean_dec(v_declName_1203_);
lean_dec_ref(v_env_1202_);
return v___x_1239_;
}
}
}
v___jp_1216_:
{
uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1217_ = 0;
v___x_1218_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1205_, v___x_1206_, v_env_1202_, v_val_1215_, v___x_1217_);
lean_dec(v_val_1215_);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_array_get_size(v___x_1218_);
v___x_1221_ = lean_nat_dec_lt(v___x_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_dec_ref(v___x_1218_);
goto v___jp_1207_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_sub(v___x_1220_, v___x_1222_);
v___x_1224_ = lean_nat_dec_le(v___x_1219_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_dec(v___x_1223_);
lean_dec_ref(v___x_1218_);
goto v___jp_1207_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_tmpDecl_1227_; lean_object* v___x_1228_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1226_ = lean_box(0);
lean_inc(v_declName_1203_);
v_tmpDecl_1227_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1227_, 0, v_declName_1203_);
lean_ctor_set(v_tmpDecl_1227_, 1, v___x_1225_);
lean_ctor_set(v_tmpDecl_1227_, 2, v___x_1226_);
lean_ctor_set(v_tmpDecl_1227_, 3, v___x_1204_);
v___x_1228_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1218_, v_tmpDecl_1227_, v___x_1219_, v___x_1223_);
lean_dec_ref_known(v_tmpDecl_1227_, 4);
lean_dec_ref(v___x_1218_);
if (lean_obj_tag(v___x_1228_) == 0)
{
goto v___jp_1207_;
}
else
{
lean_dec(v_declName_1203_);
lean_dec_ref(v_env_1202_);
return v___x_1228_;
}
}
}
}
}
v___jp_1207_:
{
lean_object* v_toEnvExtension_1208_; lean_object* v_asyncMode_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_snd_1212_; lean_object* v___x_1213_; 
v_toEnvExtension_1208_ = lean_ctor_get(v___x_1206_, 0);
v_asyncMode_1209_ = lean_ctor_get(v_toEnvExtension_1208_, 2);
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1205_, v___x_1206_, v_env_1202_, v_asyncMode_1209_, v___x_1210_);
v_snd_1212_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_snd_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1212_, v_declName_1203_);
lean_dec(v_declName_1203_);
lean_dec(v_snd_1212_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1241_, v_x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1244_, v_x_1245_, v_x_1246_);
lean_dec(v_x_1246_);
lean_dec_ref(v_x_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1248_, lean_object* v_k_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1248_, v_k_1249_, v_x_1250_, v_x_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1254_, lean_object* v_k_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1254_, v_k_1255_, v_x_1256_, v_x_1257_, v_x_1258_);
lean_dec_ref(v_k_1255_);
lean_dec_ref(v_as_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, size_t v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1261_, v_x_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
size_t v_x_573__boxed_1269_; lean_object* v_res_1270_; 
v_x_573__boxed_1269_ = lean_unbox_usize(v_x_1267_);
lean_dec(v_x_1267_);
v_res_1270_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1265_, v_x_1266_, v_x_573__boxed_1269_, v_x_1268_);
lean_dec(v_x_1268_);
lean_dec_ref(v_x_1266_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1271_, lean_object* v_keys_1272_, lean_object* v_vals_1273_, lean_object* v_heq_1274_, lean_object* v_i_1275_, lean_object* v_k_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1272_, v_vals_1273_, v_i_1275_, v_k_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1278_, lean_object* v_keys_1279_, lean_object* v_vals_1280_, lean_object* v_heq_1281_, lean_object* v_i_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1278_, v_keys_1279_, v_vals_1280_, v_heq_1281_, v_i_1282_, v_k_1283_);
lean_dec(v_k_1283_);
lean_dec_ref(v_vals_1280_);
lean_dec_ref(v_keys_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1285_, lean_object* v_declName_1286_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1285_, v_declName_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; lean_object* v_toEnvExtension_1290_; lean_object* v_asyncMode_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1289_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1290_ = lean_ctor_get(v___x_1289_, 0);
v_asyncMode_1291_ = lean_ctor_get(v_toEnvExtension_1290_, 2);
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1287_, v___x_1289_, v_env_1285_, v_asyncMode_1291_, v___x_1292_);
v___x_1294_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1293_, v_declName_1286_);
lean_dec(v_declName_1286_);
lean_dec(v___x_1293_);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___y_1300_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_val_1295_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1295_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1298_ = l_Lean_IR_declMapExt;
v___x_1313_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1297_, v___x_1298_, v_env_1285_, v_val_1295_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_array_get_size(v___x_1313_);
v___x_1316_ = lean_nat_dec_lt(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1313_);
v___x_1317_ = lean_box(0);
v___y_1300_ = v___x_1317_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_sub(v___x_1315_, v___x_1318_);
v___x_1320_ = lean_nat_dec_le(v___x_1314_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v___x_1319_);
lean_dec_ref(v___x_1313_);
v___x_1321_ = lean_box(0);
v___y_1300_ = v___x_1321_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_tmpDecl_1324_; lean_object* v___x_1325_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1323_ = lean_box(0);
lean_inc(v_declName_1286_);
v_tmpDecl_1324_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1324_, 0, v_declName_1286_);
lean_ctor_set(v_tmpDecl_1324_, 1, v___x_1322_);
lean_ctor_set(v_tmpDecl_1324_, 2, v___x_1323_);
lean_ctor_set(v_tmpDecl_1324_, 3, v___x_1296_);
v___x_1325_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1313_, v_tmpDecl_1324_, v___x_1314_, v___x_1319_);
lean_dec_ref_known(v_tmpDecl_1324_, 4);
lean_dec_ref(v___x_1313_);
if (lean_obj_tag(v___x_1325_) == 0)
{
v___y_1300_ = v___x_1325_;
goto v___jp_1299_;
}
else
{
lean_dec(v_val_1295_);
lean_dec(v_declName_1286_);
lean_dec_ref(v_env_1285_);
return v___x_1325_;
}
}
}
v___jp_1299_:
{
uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1301_ = 0;
v___x_1302_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1297_, v___x_1298_, v_env_1285_, v_val_1295_, v___x_1301_);
lean_dec(v_val_1295_);
lean_dec_ref(v_env_1285_);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_array_get_size(v___x_1302_);
v___x_1305_ = lean_nat_dec_lt(v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v___x_1302_);
lean_dec(v_declName_1286_);
return v___y_1300_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_sub(v___x_1304_, v___x_1306_);
v___x_1308_ = lean_nat_dec_le(v___x_1303_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec(v___x_1307_);
lean_dec_ref(v___x_1302_);
lean_dec(v_declName_1286_);
return v___y_1300_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_tmpDecl_1311_; lean_object* v___x_1312_; 
lean_dec(v___y_1300_);
v___x_1309_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1310_ = lean_box(0);
v_tmpDecl_1311_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1311_, 0, v_declName_1286_);
lean_ctor_set(v_tmpDecl_1311_, 1, v___x_1309_);
lean_ctor_set(v_tmpDecl_1311_, 2, v___x_1310_);
lean_ctor_set(v_tmpDecl_1311_, 3, v___x_1296_);
v___x_1312_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1302_, v_tmpDecl_1311_, v___x_1303_, v___x_1307_);
lean_dec_ref_known(v_tmpDecl_1311_, 4);
lean_dec_ref(v___x_1302_);
return v___x_1312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1326_, lean_object* v_declName_1327_){
_start:
{
lean_object* v___x_1328_; lean_object* v_boxed_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc(v_declName_1327_);
v_boxed_1329_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1327_);
v___x_1330_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1326_, v_declName_1327_);
lean_dec(v_declName_1327_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v___x_1331_; lean_object* v_toEnvExtension_1332_; lean_object* v_asyncMode_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1332_ = lean_ctor_get(v___x_1331_, 0);
v_asyncMode_1333_ = lean_ctor_get(v_toEnvExtension_1332_, 2);
v___x_1334_ = lean_box(0);
v___x_1335_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1328_, v___x_1331_, v_env_1326_, v_asyncMode_1333_, v___x_1334_);
v___x_1336_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1335_, v_boxed_1329_);
lean_dec(v_boxed_1329_);
lean_dec(v___x_1335_);
return v___x_1336_;
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___y_1342_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_val_1337_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1340_ = l_Lean_IR_declMapExt;
v___x_1355_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1339_, v___x_1340_, v_env_1326_, v_val_1337_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_array_get_size(v___x_1355_);
v___x_1358_ = lean_nat_dec_lt(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v___x_1355_);
v___x_1359_ = lean_box(0);
v___y_1342_ = v___x_1359_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_nat_sub(v___x_1357_, v___x_1360_);
v___x_1362_ = lean_nat_dec_le(v___x_1356_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec(v___x_1361_);
lean_dec_ref(v___x_1355_);
v___x_1363_ = lean_box(0);
v___y_1342_ = v___x_1363_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_tmpDecl_1366_; lean_object* v___x_1367_; 
v___x_1364_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1365_ = lean_box(0);
lean_inc(v_boxed_1329_);
v_tmpDecl_1366_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1366_, 0, v_boxed_1329_);
lean_ctor_set(v_tmpDecl_1366_, 1, v___x_1364_);
lean_ctor_set(v_tmpDecl_1366_, 2, v___x_1365_);
lean_ctor_set(v_tmpDecl_1366_, 3, v___x_1338_);
v___x_1367_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1355_, v_tmpDecl_1366_, v___x_1356_, v___x_1361_);
lean_dec_ref_known(v_tmpDecl_1366_, 4);
lean_dec_ref(v___x_1355_);
if (lean_obj_tag(v___x_1367_) == 0)
{
v___y_1342_ = v___x_1367_;
goto v___jp_1341_;
}
else
{
lean_dec(v_val_1337_);
lean_dec(v_boxed_1329_);
lean_dec_ref(v_env_1326_);
return v___x_1367_;
}
}
}
v___jp_1341_:
{
uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1343_ = 0;
v___x_1344_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1339_, v___x_1340_, v_env_1326_, v_val_1337_, v___x_1343_);
lean_dec(v_val_1337_);
lean_dec_ref(v_env_1326_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v___x_1344_);
v___x_1347_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v___x_1344_);
lean_dec(v_boxed_1329_);
return v___y_1342_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_sub(v___x_1346_, v___x_1348_);
v___x_1350_ = lean_nat_dec_le(v___x_1345_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec(v___x_1349_);
lean_dec_ref(v___x_1344_);
lean_dec(v_boxed_1329_);
return v___y_1342_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_tmpDecl_1353_; lean_object* v___x_1354_; 
lean_dec(v___y_1342_);
v___x_1351_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1352_ = lean_box(0);
v_tmpDecl_1353_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1353_, 0, v_boxed_1329_);
lean_ctor_set(v_tmpDecl_1353_, 1, v___x_1351_);
lean_ctor_set(v_tmpDecl_1353_, 2, v___x_1352_);
lean_ctor_set(v_tmpDecl_1353_, 3, v___x_1338_);
v___x_1354_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1344_, v_tmpDecl_1353_, v___x_1345_, v___x_1349_);
lean_dec_ref_known(v_tmpDecl_1353_, 4);
lean_dec_ref(v___x_1344_);
return v___x_1354_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1368_, lean_object* v_constName_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1368_, v_constName_1369_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1371_; lean_object* v_toEnvExtension_1372_; lean_object* v_asyncMode_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1371_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1372_ = lean_ctor_get(v___x_1371_, 0);
v_asyncMode_1373_ = lean_ctor_get(v_toEnvExtension_1372_, 2);
v___x_1374_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1374_, v___x_1371_, v_env_1368_, v_asyncMode_1373_, v___x_1375_);
v___x_1377_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1376_, v_constName_1369_);
lean_dec(v_constName_1369_);
lean_dec(v___x_1376_);
v___x_1378_ = lean_bool_not(v___x_1377_);
return v___x_1378_;
}
else
{
uint8_t v___x_1379_; 
lean_dec_ref_known(v___x_1370_, 1);
lean_dec(v_constName_1369_);
lean_dec_ref(v_env_1368_);
v___x_1379_ = 0;
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1380_, lean_object* v_constName_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = lean_has_compile_error(v_env_1380_, v_constName_1381_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; lean_object* v_env_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1387_ = lean_st_ref_get(v_a_1385_);
v_env_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc_ref(v_env_1388_);
lean_dec(v___x_1387_);
v___x_1389_ = l_Lean_IR_findEnvDecl(v_env_1388_, v_n_1384_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_IR_findDecl___redArg(v_n_1391_, v_a_1392_);
lean_dec(v_a_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_IR_findDecl___redArg(v_n_1395_, v_a_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_IR_findDecl(v_n_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1423_; 
v___x_1408_ = l_Lean_IR_findDecl___redArg(v_n_1405_, v_a_1406_);
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1423_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1423_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
if (lean_obj_tag(v_a_1409_) == 0)
{
uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = 0;
v___x_1414_ = lean_box(v___x_1413_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_dec_ref_known(v_a_1409_, 1);
v___x_1418_ = 1;
v___x_1419_ = lean_box(v___x_1418_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1419_);
v___x_1421_ = v___x_1411_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_IR_containsDecl___redArg(v_n_1424_, v_a_1425_);
lean_dec(v_a_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_IR_containsDecl___redArg(v_n_1428_, v_a_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_IR_containsDecl(v_n_1433_, v_a_1434_, v_a_1435_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_ref_1442_; lean_object* v___x_1443_; lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_ref_1442_ = lean_ctor_get(v___y_1439_, 5);
v___x_1443_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1438_, v___y_1439_, v___y_1440_);
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_inc(v_ref_1442_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_ref_1442_);
lean_ctor_set(v___x_1448_, 1, v_a_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 1);
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1482_; 
lean_inc(v_n_1460_);
v___x_1464_ = l_Lean_IR_findDecl___redArg(v_n_1460_, v_a_1462_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
if (lean_obj_tag(v_a_1465_) == 1)
{
lean_object* v_val_1469_; lean_object* v___x_1471_; 
lean_dec(v_n_1460_);
v_val_1469_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_val_1469_);
lean_dec_ref_known(v_a_1465_, 1);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_val_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_val_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_del_object(v___x_1467_);
lean_dec(v_a_1465_);
v___x_1473_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1474_ = 1;
v___x_1475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1460_, v___x_1474_);
v___x_1476_ = lean_string_append(v___x_1473_, v___x_1475_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
v___x_1480_ = l_Lean_MessageData_ofFormat(v___x_1479_);
v___x_1481_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1480_, v_a_1461_, v_a_1462_);
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_IR_getDecl(v_n_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1488_, lean_object* v_msg_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1494_, v_msg_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v_env_1504_; lean_object* v___x_1505_; lean_object* v_toEnvExtension_1506_; lean_object* v_asyncMode_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1503_ = lean_st_ref_get(v_a_1501_);
v_env_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_ref(v_env_1504_);
lean_dec(v___x_1503_);
v___x_1505_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1506_ = lean_ctor_get(v___x_1505_, 0);
v_asyncMode_1507_ = lean_ctor_get(v_toEnvExtension_1506_, 2);
v___x_1508_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1509_ = lean_box(0);
v___x_1510_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1508_, v___x_1505_, v_env_1504_, v_asyncMode_1507_, v___x_1509_);
v___x_1511_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1510_, v_n_1500_);
lean_dec(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_IR_findLocalDecl___redArg(v_n_1513_, v_a_1514_);
lean_dec(v_a_1514_);
lean_dec(v_n_1513_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_IR_findLocalDecl___redArg(v_n_1517_, v_a_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_IR_findLocalDecl(v_n_1522_, v_a_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_n_1522_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v_toEnvExtension_1529_; lean_object* v_asyncMode_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1529_ = lean_ctor_get(v___x_1528_, 0);
v_asyncMode_1530_ = lean_ctor_get(v_toEnvExtension_1529_, 2);
v___x_1531_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1532_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1531_, v___x_1528_, v_env_1527_, v_asyncMode_1530_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v_env_1542_; lean_object* v_nextMacroScope_1543_; lean_object* v_ngen_1544_; lean_object* v_auxDeclNGen_1545_; lean_object* v_traceState_1546_; lean_object* v_messages_1547_; lean_object* v_infoState_1548_; lean_object* v_snapshotTasks_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1565_; 
v___x_1541_ = lean_st_ref_take(v_a_1539_);
v_env_1542_ = lean_ctor_get(v___x_1541_, 0);
v_nextMacroScope_1543_ = lean_ctor_get(v___x_1541_, 1);
v_ngen_1544_ = lean_ctor_get(v___x_1541_, 2);
v_auxDeclNGen_1545_ = lean_ctor_get(v___x_1541_, 3);
v_traceState_1546_ = lean_ctor_get(v___x_1541_, 4);
v_messages_1547_ = lean_ctor_get(v___x_1541_, 6);
v_infoState_1548_ = lean_ctor_get(v___x_1541_, 7);
v_snapshotTasks_1549_ = lean_ctor_get(v___x_1541_, 8);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v___x_1541_, 5);
lean_dec(v_unused_1566_);
v___x_1551_ = v___x_1541_;
v_isShared_1552_ = v_isSharedCheck_1565_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_snapshotTasks_1549_);
lean_inc(v_infoState_1548_);
lean_inc(v_messages_1547_);
lean_inc(v_traceState_1546_);
lean_inc(v_auxDeclNGen_1545_);
lean_inc(v_ngen_1544_);
lean_inc(v_nextMacroScope_1543_);
lean_inc(v_env_1542_);
lean_dec(v___x_1541_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1565_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v_toEnvExtension_1554_; lean_object* v_asyncMode_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1553_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1554_ = lean_ctor_get(v___x_1553_, 0);
v_asyncMode_1555_ = lean_ctor_get(v_toEnvExtension_1554_, 2);
v___x_1556_ = lean_box(0);
v___x_1557_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1553_, v_env_1542_, v_decl_1538_, v_asyncMode_1555_, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 5, v___x_1558_);
lean_ctor_set(v___x_1551_, 0, v___x_1557_);
v___x_1560_ = v___x_1551_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_nextMacroScope_1543_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_ngen_1544_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_auxDeclNGen_1545_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_traceState_1546_);
lean_ctor_set(v_reuseFailAlloc_1564_, 5, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 6, v_messages_1547_);
lean_ctor_set(v_reuseFailAlloc_1564_, 7, v_infoState_1548_);
lean_ctor_set(v_reuseFailAlloc_1564_, 8, v_snapshotTasks_1549_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_st_ref_set(v_a_1539_, v___x_1560_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_IR_addDecl___redArg(v_decl_1567_, v_a_1568_);
lean_dec(v_a_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_IR_addDecl___redArg(v_decl_1571_, v_a_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_IR_addDecl(v_decl_1576_, v_a_1577_, v_a_1578_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1581_, size_t v_i_1582_, size_t v_stop_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v___x_1587_; 
v___x_1587_ = lean_usize_dec_eq(v_i_1582_, v_stop_1583_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_array_uget_borrowed(v_as_1581_, v_i_1582_);
lean_inc(v___x_1588_);
v___x_1589_ = l_Lean_IR_addDecl___redArg(v___x_1588_, v___y_1585_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; size_t v___x_1591_; size_t v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1582_, v___x_1591_);
v_i_1582_ = v___x_1592_;
v_b_1584_ = v_a_1590_;
goto _start;
}
else
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_b_1584_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1595_, lean_object* v_i_1596_, lean_object* v_stop_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
size_t v_i_boxed_1601_; size_t v_stop_boxed_1602_; lean_object* v_res_1603_; 
v_i_boxed_1601_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_stop_boxed_1602_ = lean_unbox_usize(v_stop_1597_);
lean_dec(v_stop_1597_);
v_res_1603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1595_, v_i_boxed_1601_, v_stop_boxed_1602_, v_b_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v_as_1595_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_array_get_size(v_decls_1604_);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_nat_dec_lt(v___x_1608_, v___x_1609_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
return v___x_1612_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_le(v___x_1609_, v___x_1609_);
if (v___x_1613_ == 0)
{
if (v___x_1611_ == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1610_);
return v___x_1614_;
}
else
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = lean_usize_of_nat(v___x_1609_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1604_, v___x_1615_, v___x_1616_, v___x_1610_, v_a_1606_);
return v___x_1617_;
}
}
else
{
size_t v___x_1618_; size_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = lean_usize_of_nat(v___x_1609_);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1604_, v___x_1618_, v___x_1619_, v___x_1610_, v_a_1606_);
return v___x_1620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_IR_addDecls(v_decls_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec_ref(v_decls_1621_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1626_, size_t v_i_1627_, size_t v_stop_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1626_, v_i_1627_, v_stop_1628_, v_b_1629_, v___y_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_stop_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
size_t v_i_boxed_1641_; size_t v_stop_boxed_1642_; lean_object* v_res_1643_; 
v_i_boxed_1641_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_stop_boxed_1642_ = lean_unbox_usize(v_stop_1636_);
lean_dec(v_stop_1636_);
v_res_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1634_, v_i_boxed_1641_, v_stop_boxed_1642_, v_b_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_as_1634_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1647_, lean_object* v_as_1648_, size_t v_sz_1649_, size_t v_i_1650_, lean_object* v_b_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_usize_dec_lt(v_i_1650_, v_sz_1649_);
if (v___x_1652_ == 0)
{
lean_inc_ref(v_b_1651_);
return v_b_1651_;
}
else
{
lean_object* v___x_1653_; lean_object* v_a_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1653_ = lean_box(0);
v_a_1654_ = lean_array_uget_borrowed(v_as_1648_, v_i_1650_);
v___x_1655_ = l_Lean_IR_Decl_name(v_a_1654_);
v___x_1656_ = lean_name_eq(v___x_1655_, v_n_1647_);
lean_dec(v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; 
v___x_1657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_add(v_i_1650_, v___x_1658_);
v_i_1650_ = v___x_1659_;
v_b_1651_ = v___x_1657_;
goto _start;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_inc(v_a_1654_);
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1654_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1653_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1664_, lean_object* v_as_1665_, lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_b_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1664_, v_as_1665_, v_sz_boxed_1669_, v_i_boxed_1670_, v_b_1668_);
lean_dec_ref(v_b_1668_);
lean_dec_ref(v_as_1665_);
lean_dec(v_n_1664_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1672_, lean_object* v_n_1673_, lean_object* v_decls_1674_){
_start:
{
lean_object* v___x_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; lean_object* v_fst_1679_; 
v___x_1675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1676_ = lean_array_size(v_decls_1674_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1673_, v_decls_1674_, v_sz_1676_, v___x_1677_, v___x_1675_);
v_fst_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_fst_1679_);
lean_dec_ref(v___x_1678_);
if (lean_obj_tag(v_fst_1679_) == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_IR_findEnvDecl(v_env_1672_, v_n_1673_);
return v___x_1680_;
}
else
{
lean_object* v_val_1681_; 
v_val_1681_ = lean_ctor_get(v_fst_1679_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_fst_1679_, 1);
if (lean_obj_tag(v_val_1681_) == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_IR_findEnvDecl(v_env_1672_, v_n_1673_);
return v___x_1682_;
}
else
{
lean_dec(v_n_1673_);
lean_dec_ref(v_env_1672_);
return v_val_1681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1683_, lean_object* v_n_1684_, lean_object* v_decls_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_IR_findEnvDecl_x27(v_env_1683_, v_n_1684_, v_decls_1685_);
lean_dec_ref(v_decls_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1687_, lean_object* v_decls_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v_env_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1691_ = lean_st_ref_get(v_a_1689_);
v_env_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc_ref(v_env_1692_);
lean_dec(v___x_1691_);
v___x_1693_ = l_Lean_IR_findEnvDecl_x27(v_env_1692_, v_n_1687_, v_decls_1688_);
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1695_, lean_object* v_decls_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_IR_findDecl_x27___redArg(v_n_1695_, v_decls_1696_, v_a_1697_);
lean_dec(v_a_1697_);
lean_dec_ref(v_decls_1696_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1700_, lean_object* v_decls_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_IR_findDecl_x27___redArg(v_n_1700_, v_decls_1701_, v_a_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1706_, lean_object* v_decls_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_IR_findDecl_x27(v_n_1706_, v_decls_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec_ref(v_decls_1707_);
return v_res_1711_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1712_, lean_object* v_as_1713_, size_t v_i_1714_, size_t v_stop_1715_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_eq(v_i_1714_, v_stop_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1717_ = lean_array_uget_borrowed(v_as_1713_, v_i_1714_);
v___x_1718_ = l_Lean_IR_Decl_name(v___x_1717_);
v___x_1719_ = lean_name_eq(v___x_1718_, v_n_1712_);
lean_dec(v___x_1718_);
if (v___x_1719_ == 0)
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1714_, v___x_1720_);
v_i_1714_ = v___x_1721_;
goto _start;
}
else
{
return v___x_1719_;
}
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1724_, lean_object* v_as_1725_, lean_object* v_i_1726_, lean_object* v_stop_1727_){
_start:
{
size_t v_i_boxed_1728_; size_t v_stop_boxed_1729_; uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_i_boxed_1728_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_stop_boxed_1729_ = lean_unbox_usize(v_stop_1727_);
lean_dec(v_stop_1727_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1724_, v_as_1725_, v_i_boxed_1728_, v_stop_boxed_1729_);
lean_dec_ref(v_as_1725_);
lean_dec(v_n_1724_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1732_, lean_object* v_decls_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_array_get_size(v_decls_1733_);
v___x_1738_ = lean_nat_dec_lt(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_IR_containsDecl___redArg(v_n_1732_, v_a_1734_);
return v___x_1739_;
}
else
{
if (v___x_1738_ == 0)
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_IR_containsDecl___redArg(v_n_1732_, v_a_1734_);
return v___x_1740_;
}
else
{
size_t v___x_1741_; size_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = lean_usize_of_nat(v___x_1737_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1732_, v_decls_1733_, v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_IR_containsDecl___redArg(v_n_1732_, v_a_1734_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v_n_1732_);
v___x_1745_ = lean_box(v___x_1743_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1747_, lean_object* v_decls_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1747_, v_decls_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_decls_1748_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1752_, lean_object* v_decls_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1752_, v_decls_1753_, v_a_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1758_, lean_object* v_decls_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_IR_containsDecl_x27(v_n_1758_, v_decls_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec_ref(v_decls_1759_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1764_, lean_object* v_decls_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1787_; 
lean_inc(v_n_1764_);
v___x_1769_ = l_Lean_IR_findDecl_x27___redArg(v_n_1764_, v_decls_1765_, v_a_1767_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1787_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1787_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
if (lean_obj_tag(v_a_1770_) == 1)
{
lean_object* v_val_1774_; lean_object* v___x_1776_; 
lean_dec(v_n_1764_);
v_val_1774_ = lean_ctor_get(v_a_1770_, 0);
lean_inc(v_val_1774_);
lean_dec_ref_known(v_a_1770_, 1);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_val_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_val_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_del_object(v___x_1772_);
lean_dec(v_a_1770_);
v___x_1778_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1779_ = 1;
v___x_1780_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1764_, v___x_1779_);
v___x_1781_ = lean_string_append(v___x_1778_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1783_ = lean_string_append(v___x_1781_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
v___x_1785_ = l_Lean_MessageData_ofFormat(v___x_1784_);
v___x_1786_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1785_, v_a_1766_, v_a_1767_);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1788_, lean_object* v_decls_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_IR_getDecl_x27(v_n_1788_, v_decls_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec_ref(v_decls_1789_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1794_, lean_object* v_declName_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_IR_findEnvDecl(v_env_1794_, v_declName_1795_);
if (lean_obj_tag(v___x_1796_) == 1)
{
lean_object* v_val_1797_; 
v_val_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v___x_1796_, 1);
if (lean_obj_tag(v_val_1797_) == 0)
{
lean_object* v_info_1798_; 
v_info_1798_ = lean_ctor_get(v_val_1797_, 4);
lean_inc(v_info_1798_);
lean_dec_ref_known(v_val_1797_, 5);
return v_info_1798_;
}
else
{
lean_object* v___x_1799_; 
lean_dec(v_val_1797_);
v___x_1799_ = lean_box(0);
return v___x_1799_;
}
}
else
{
lean_object* v___x_1800_; 
lean_dec(v___x_1796_);
v___x_1800_ = lean_box(0);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1801_, uint8_t v_level_1802_, uint8_t v_includeDecls_1803_, lean_object* v_as_1804_, size_t v_i_1805_, size_t v_stop_1806_, lean_object* v_b_1807_){
_start:
{
lean_object* v___y_1809_; uint8_t v___x_1813_; 
v___x_1813_ = lean_usize_dec_eq(v_i_1805_, v_stop_1806_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; uint8_t v___y_1816_; uint8_t v___y_1819_; 
v___x_1814_ = lean_array_uget_borrowed(v_as_1804_, v_i_1805_);
if (v_includeDecls_1803_ == 0)
{
uint8_t v___x_1826_; uint8_t v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = 1;
lean_inc(v___x_1814_);
lean_inc_ref(v_env_1801_);
v___x_1827_ = l_Lean_Environment_contains(v_env_1801_, v___x_1814_, v___x_1826_);
v___x_1828_ = lean_bool_not(v___x_1827_);
if (v___x_1828_ == 0)
{
v___y_1816_ = v___x_1828_;
goto v___jp_1815_;
}
else
{
goto v___jp_1822_;
}
}
else
{
goto v___jp_1822_;
}
v___jp_1815_:
{
if (v___y_1816_ == 0)
{
v___y_1809_ = v_b_1807_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1817_; 
lean_inc(v___x_1814_);
v___x_1817_ = lean_array_push(v_b_1807_, v___x_1814_);
v___y_1809_ = v___x_1817_;
goto v___jp_1808_;
}
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
uint8_t v___x_1820_; 
lean_inc_ref(v_env_1801_);
v___x_1820_ = l_Lean_isDeclMeta(v_env_1801_, v___x_1814_);
v___y_1816_ = v___x_1820_;
goto v___jp_1815_;
}
else
{
lean_object* v___x_1821_; 
lean_inc(v___x_1814_);
v___x_1821_ = lean_array_push(v_b_1807_, v___x_1814_);
v___y_1809_ = v___x_1821_;
goto v___jp_1808_;
}
}
v___jp_1822_:
{
uint8_t v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = 2;
v___x_1824_ = l_Lean_instDecidableEqOLeanLevel(v_level_1802_, v___x_1823_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; 
lean_inc_ref(v_env_1801_);
v___x_1825_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1801_, v___x_1814_);
v___y_1819_ = v___x_1825_;
goto v___jp_1818_;
}
else
{
v___y_1819_ = v___x_1824_;
goto v___jp_1818_;
}
}
}
else
{
lean_dec_ref(v_env_1801_);
return v_b_1807_;
}
v___jp_1808_:
{
size_t v___x_1810_; size_t v___x_1811_; 
v___x_1810_ = ((size_t)1ULL);
v___x_1811_ = lean_usize_add(v_i_1805_, v___x_1810_);
v_i_1805_ = v___x_1811_;
v_b_1807_ = v___y_1809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1829_, lean_object* v_level_1830_, lean_object* v_includeDecls_1831_, lean_object* v_as_1832_, lean_object* v_i_1833_, lean_object* v_stop_1834_, lean_object* v_b_1835_){
_start:
{
uint8_t v_level_boxed_1836_; uint8_t v_includeDecls_boxed_1837_; size_t v_i_boxed_1838_; size_t v_stop_boxed_1839_; lean_object* v_res_1840_; 
v_level_boxed_1836_ = lean_unbox(v_level_1830_);
v_includeDecls_boxed_1837_ = lean_unbox(v_includeDecls_1831_);
v_i_boxed_1838_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_stop_boxed_1839_ = lean_unbox_usize(v_stop_1834_);
lean_dec(v_stop_1834_);
v_res_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1829_, v_level_boxed_1836_, v_includeDecls_boxed_1837_, v_as_1832_, v_i_boxed_1838_, v_stop_boxed_1839_, v_b_1835_);
lean_dec_ref(v_as_1832_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1841_, size_t v_i_1842_, lean_object* v_bs_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_usize_dec_lt(v_i_1842_, v_sz_1841_);
if (v___x_1844_ == 0)
{
return v_bs_1843_;
}
else
{
lean_object* v_v_1845_; lean_object* v___x_1846_; lean_object* v_bs_x27_1847_; lean_object* v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
v_v_1845_ = lean_array_uget(v_bs_1843_, v_i_1842_);
v___x_1846_ = lean_unsigned_to_nat(0u);
v_bs_x27_1847_ = lean_array_uset(v_bs_1843_, v_i_1842_, v___x_1846_);
v___x_1848_ = l_Lean_IR_Decl_name(v_v_1845_);
lean_dec(v_v_1845_);
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_add(v_i_1842_, v___x_1849_);
v___x_1851_ = lean_array_uset(v_bs_x27_1847_, v_i_1842_, v___x_1848_);
v_i_1842_ = v___x_1850_;
v_bs_1843_ = v___x_1851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1853_, lean_object* v_i_1854_, lean_object* v_bs_1855_){
_start:
{
size_t v_sz_boxed_1856_; size_t v_i_boxed_1857_; lean_object* v_res_1858_; 
v_sz_boxed_1856_ = lean_unbox_usize(v_sz_1853_);
lean_dec(v_sz_1853_);
v_i_boxed_1857_ = lean_unbox_usize(v_i_1854_);
lean_dec(v_i_1854_);
v_res_1858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1856_, v_i_boxed_1857_, v_bs_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1861_, uint8_t v_level_1862_, uint8_t v_includeDecls_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v_toEnvExtension_1865_; lean_object* v_asyncMode_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; uint8_t v___x_1869_; lean_object* v_env_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; size_t v_sz_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1864_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1865_ = lean_ctor_get(v___x_1864_, 0);
v_asyncMode_1866_ = lean_ctor_get(v_toEnvExtension_1865_, 2);
v___x_1867_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1868_ = 0;
v___x_1869_ = l_Lean_instDecidableEqOLeanLevel(v_level_1862_, v___x_1868_);
v_env_1870_ = l_Lean_Environment_setExporting(v_env_1861_, v___x_1869_);
lean_inc_ref(v_env_1870_);
v___x_1871_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1867_, v___x_1864_, v_env_1870_, v_asyncMode_1866_);
v___x_1872_ = lean_array_mk(v___x_1871_);
v_sz_1873_ = lean_array_size(v___x_1872_);
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1873_, v___x_1874_, v___x_1872_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_array_get_size(v___x_1875_);
v___x_1878_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1879_ = lean_nat_dec_lt(v___x_1876_, v___x_1877_);
if (v___x_1879_ == 0)
{
lean_dec_ref(v___x_1875_);
lean_dec_ref(v_env_1870_);
return v___x_1878_;
}
else
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_nat_dec_le(v___x_1877_, v___x_1877_);
if (v___x_1880_ == 0)
{
if (v___x_1879_ == 0)
{
lean_dec_ref(v___x_1875_);
lean_dec_ref(v_env_1870_);
return v___x_1878_;
}
else
{
size_t v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_usize_of_nat(v___x_1877_);
v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1870_, v_level_1862_, v_includeDecls_1863_, v___x_1875_, v___x_1874_, v___x_1881_, v___x_1878_);
lean_dec_ref(v___x_1875_);
return v___x_1882_;
}
}
else
{
size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_usize_of_nat(v___x_1877_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1870_, v_level_1862_, v_includeDecls_1863_, v___x_1875_, v___x_1874_, v___x_1883_, v___x_1878_);
lean_dec_ref(v___x_1875_);
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1885_, lean_object* v_level_1886_, lean_object* v_includeDecls_1887_){
_start:
{
uint8_t v_level_boxed_1888_; uint8_t v_includeDecls_boxed_1889_; lean_object* v_res_1890_; 
v_level_boxed_1888_ = lean_unbox(v_level_1886_);
v_includeDecls_boxed_1889_ = lean_unbox(v_includeDecls_1887_);
v_res_1890_ = lean_get_ir_extra_const_names(v_env_1885_, v_level_boxed_1888_, v_includeDecls_boxed_1889_);
return v_res_1890_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
