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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_xs_574_);
lean_inc(v_type_575_);
lean_inc(v_f_573_);
v___y_563_ = v_f_573_;
v___y_564_ = v_type_575_;
v___y_565_ = v_xs_574_;
goto v___jp_562_;
}
}
else
{
lean_dec(v___x_576_);
lean_inc_ref(v_xs_574_);
lean_inc(v_type_575_);
lean_inc(v_f_573_);
v___y_563_ = v_f_573_;
v___y_564_ = v_type_575_;
v___y_565_ = v_xs_574_;
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
lean_ctor_set(v___x_567_, 0, v___y_563_);
lean_ctor_set(v___x_567_, 1, v___y_565_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
uint64_t v___y_706_; 
if (lean_obj_tag(v_x_704_) == 0)
{
uint64_t v___x_709_; 
v___x_709_ = 1723ULL;
v___y_706_ = v___x_709_;
goto v___jp_705_;
}
else
{
uint64_t v_hash_710_; 
v_hash_710_ = lean_ctor_get_uint64(v_x_704_, sizeof(void*)*2);
v___y_706_ = v_hash_710_;
goto v___jp_705_;
}
v___jp_705_:
{
size_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_uint64_to_usize(v___y_706_);
v___x_708_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_703_, v___x_707_, v_x_704_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_711_, v_x_712_);
lean_dec(v_x_712_);
lean_dec_ref(v_x_711_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_715_, lean_object* v_x2_716_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = l_Lean_IR_Decl_name(v_x2_716_);
v___x_718_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_715_, v___x_717_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = 1;
return v___x_719_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = 0;
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_721_, lean_object* v_x2_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_721_, v_x2_722_);
lean_dec_ref(v_x2_722_);
lean_dec_ref(v_x1_721_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_730_);
lean_dec_ref(v_x_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v_ks_736_; lean_object* v_vs_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_761_; 
v_ks_736_ = lean_ctor_get(v_x_732_, 0);
v_vs_737_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_761_ == 0)
{
v___x_739_ = v_x_732_;
v_isShared_740_ = v_isSharedCheck_761_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_vs_737_);
lean_inc(v_ks_736_);
lean_dec(v_x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_761_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_ks_736_);
v___x_742_ = lean_nat_dec_lt(v_x_733_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_x_733_);
v___x_743_ = lean_array_push(v_ks_736_, v_x_734_);
v___x_744_ = lean_array_push(v_vs_737_, v_x_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_744_);
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_746_ = v___x_739_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v_k_x27_748_; uint8_t v___x_749_; 
v_k_x27_748_ = lean_array_fget_borrowed(v_ks_736_, v_x_733_);
v___x_749_ = lean_name_eq(v_x_734_, v_k_x27_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_ks_736_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_vs_737_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_x_733_, v___x_752_);
lean_dec(v_x_733_);
v_x_732_ = v___x_751_;
v_x_733_ = v___x_753_;
goto _start;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = lean_array_fset(v_ks_736_, v_x_733_, v_x_734_);
v___x_757_ = lean_array_fset(v_vs_737_, v_x_733_, v_x_735_);
lean_dec(v_x_733_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_757_);
lean_ctor_set(v___x_739_, 0, v___x_756_);
v___x_759_ = v___x_739_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_762_, lean_object* v_k_763_, lean_object* v_v_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_762_, v___x_765_, v_k_763_, v_v_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_768_, size_t v_x_769_, size_t v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v_es_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v_j_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_es_773_ = lean_ctor_get(v_x_768_, 0);
v___x_774_ = ((size_t)31ULL);
v___x_775_ = lean_usize_land(v_x_769_, v___x_774_);
v_j_776_ = lean_usize_to_nat(v___x_775_);
v___x_777_ = lean_array_get_size(v_es_773_);
v___x_778_ = lean_nat_dec_lt(v_j_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec(v_j_776_);
lean_dec(v_x_772_);
lean_dec(v_x_771_);
return v_x_768_;
}
else
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_817_; 
lean_inc_ref(v_es_773_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_x_768_, 0);
lean_dec(v_unused_818_);
v___x_780_ = v_x_768_;
v_isShared_781_ = v_isSharedCheck_817_;
goto v_resetjp_779_;
}
else
{
lean_dec(v_x_768_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_817_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_v_782_; lean_object* v___x_783_; lean_object* v_xs_x27_784_; lean_object* v___y_786_; 
v_v_782_ = lean_array_fget(v_es_773_, v_j_776_);
v___x_783_ = lean_box(0);
v_xs_x27_784_ = lean_array_fset(v_es_773_, v_j_776_, v___x_783_);
switch(lean_obj_tag(v_v_782_))
{
case 0:
{
lean_object* v_key_791_; lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
v_key_791_ = lean_ctor_get(v_v_782_, 0);
v_val_792_ = lean_ctor_get(v_v_782_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_v_782_);
if (v_isSharedCheck_802_ == 0)
{
v___x_794_ = v_v_782_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_inc(v_key_791_);
lean_dec(v_v_782_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
uint8_t v___x_796_; 
v___x_796_ = lean_name_eq(v_x_771_, v_key_791_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_794_);
v___x_797_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_791_, v_val_792_, v_x_771_, v_x_772_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___y_786_ = v___x_798_;
goto v___jp_785_;
}
else
{
lean_object* v___x_800_; 
lean_dec(v_val_792_);
lean_dec(v_key_791_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_x_772_);
lean_ctor_set(v___x_794_, 0, v_x_771_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_x_771_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_x_772_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v___y_786_ = v___x_800_;
goto v___jp_785_;
}
}
}
}
case 1:
{
lean_object* v_node_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_815_; 
v_node_803_ = lean_ctor_get(v_v_782_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_v_782_);
if (v_isSharedCheck_815_ == 0)
{
v___x_805_ = v_v_782_;
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_node_803_);
lean_dec(v_v_782_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_807_ = ((size_t)5ULL);
v___x_808_ = lean_usize_shift_right(v_x_769_, v___x_807_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_x_770_, v___x_809_);
v___x_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_803_, v___x_808_, v___x_810_, v_x_771_, v_x_772_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v___y_786_ = v___x_813_;
goto v___jp_785_;
}
}
}
default: 
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_x_771_);
lean_ctor_set(v___x_816_, 1, v_x_772_);
v___y_786_ = v___x_816_;
goto v___jp_785_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_array_fset(v_xs_x27_784_, v_j_776_, v___y_786_);
lean_dec(v_j_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_787_);
v___x_789_ = v___x_780_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_object* v_ks_819_; lean_object* v_vs_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_840_; 
v_ks_819_ = lean_ctor_get(v_x_768_, 0);
v_vs_820_ = lean_ctor_get(v_x_768_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_840_ == 0)
{
v___x_822_ = v_x_768_;
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_vs_820_);
lean_inc(v_ks_819_);
lean_dec(v_x_768_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_ks_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_vs_820_);
v___x_825_ = v_reuseFailAlloc_839_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v_newNode_826_; uint8_t v___y_828_; size_t v___x_834_; uint8_t v___x_835_; 
v_newNode_826_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_825_, v_x_771_, v_x_772_);
v___x_834_ = ((size_t)7ULL);
v___x_835_ = lean_usize_dec_le(v___x_834_, v_x_770_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_826_);
v___x_837_ = lean_unsigned_to_nat(4u);
v___x_838_ = lean_nat_dec_lt(v___x_836_, v___x_837_);
lean_dec(v___x_836_);
v___y_828_ = v___x_838_;
goto v___jp_827_;
}
else
{
v___y_828_ = v___x_835_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_object* v_ks_829_; lean_object* v_vs_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_ks_829_ = lean_ctor_get(v_newNode_826_, 0);
lean_inc_ref(v_ks_829_);
v_vs_830_ = lean_ctor_get(v_newNode_826_, 1);
lean_inc_ref(v_vs_830_);
lean_dec_ref(v_newNode_826_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_770_, v_ks_829_, v_vs_830_, v___x_831_, v___x_832_);
lean_dec_ref(v_vs_830_);
lean_dec_ref(v_ks_829_);
return v___x_833_;
}
else
{
return v_newNode_826_;
}
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
size_t v_x_2768__boxed_876_; size_t v_x_2769__boxed_877_; lean_object* v_res_878_; 
v_x_2768__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_2769__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_871_, v_x_2768__boxed_876_, v_x_2769__boxed_877_, v_x_874_, v_x_875_);
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
size_t v_x_3054__boxed_987_; uint8_t v_res_988_; lean_object* v_r_989_; 
v_x_3054__boxed_987_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_res_988_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_983_, v_x_984_, v_x_3054__boxed_987_, v_x_986_);
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
size_t v_x_3065__boxed_1003_; size_t v_x_3066__boxed_1004_; lean_object* v_res_1005_; 
v_x_3065__boxed_1003_ = lean_unbox_usize(v_x_999_);
lean_dec(v_x_999_);
v_x_3066__boxed_1004_ = lean_unbox_usize(v_x_1000_);
lean_dec(v_x_1000_);
v_res_1005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_997_, v_x_998_, v_x_3065__boxed_1003_, v_x_3066__boxed_1004_, v_x_1001_, v_x_1002_);
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
lean_object* v___x_1077_; lean_object* v_toEnvExtension_1078_; lean_object* v_name_1079_; lean_object* v_asyncMode_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___y_1085_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v_irDecls_1115_; lean_object* v___x_1116_; lean_object* v___y_1118_; lean_object* v___y_1119_; uint8_t v___x_1121_; 
v___x_1077_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1078_ = lean_ctor_get(v___x_1077_, 0);
v_name_1079_ = lean_ctor_get(v___x_1077_, 1);
v_asyncMode_1080_ = lean_ctor_get(v_toEnvExtension_1078_, 2);
v___x_1081_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1082_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
v___x_1083_ = lean_box(0);
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1076_);
v___x_1114_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1081_, v___x_1077_, v_env_1076_, v_asyncMode_1080_);
v_irDecls_1115_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_array_get_size(v_irDecls_1115_);
v___x_1121_ = lean_nat_dec_eq(v___x_1116_, v___x_1112_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___y_1125_; uint8_t v___x_1127_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_sub(v___x_1116_, v___x_1122_);
v___x_1127_ = lean_nat_dec_le(v___x_1112_, v___x_1123_);
if (v___x_1127_ == 0)
{
lean_inc(v___x_1123_);
v___y_1125_ = v___x_1123_;
goto v___jp_1124_;
}
else
{
v___y_1125_ = v___x_1112_;
goto v___jp_1124_;
}
v___jp_1124_:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_nat_dec_le(v___y_1125_, v___x_1123_);
if (v___x_1126_ == 0)
{
lean_dec(v___x_1123_);
lean_inc(v___y_1125_);
v___y_1118_ = v___y_1125_;
v___y_1119_ = v___y_1125_;
goto v___jp_1117_;
}
else
{
v___y_1118_ = v___y_1125_;
v___y_1119_ = v___x_1123_;
goto v___jp_1117_;
}
}
}
else
{
v___y_1085_ = v_irDecls_1115_;
goto v___jp_1084_;
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v_ext_1087_; lean_object* v_toEnvExtension_1088_; lean_object* v_name_1089_; lean_object* v_exportEntriesFn_1090_; lean_object* v_asyncMode_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_private_1095_; lean_object* v___x_1096_; lean_object* v_toEnvExtension_1097_; lean_object* v_name_1098_; lean_object* v_exportEntriesFn_1099_; lean_object* v_asyncMode_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_private_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1086_ = l_Lean_regularInitAttr;
v_ext_1087_ = lean_ctor_get(v___x_1086_, 1);
v_toEnvExtension_1088_ = lean_ctor_get(v_ext_1087_, 0);
v_name_1089_ = lean_ctor_get(v_ext_1087_, 1);
v_exportEntriesFn_1090_ = lean_ctor_get(v_ext_1087_, 4);
v_asyncMode_1091_ = lean_ctor_get(v_toEnvExtension_1088_, 2);
v___x_1092_ = lean_box(0);
lean_inc_ref_n(v_env_1076_, 3);
v___x_1093_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1082_, v_ext_1087_, v_env_1076_, v_asyncMode_1091_, v___x_1092_);
lean_inc_ref(v_exportEntriesFn_1090_);
v___x_1094_ = lean_apply_2(v_exportEntriesFn_1090_, v_env_1076_, v___x_1093_);
v_private_1095_ = lean_ctor_get(v___x_1094_, 2);
lean_inc(v_private_1095_);
lean_dec_ref(v___x_1094_);
v___x_1096_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1097_ = lean_ctor_get(v___x_1096_, 0);
v_name_1098_ = lean_ctor_get(v___x_1096_, 1);
v_exportEntriesFn_1099_ = lean_ctor_get(v___x_1096_, 4);
v_asyncMode_1100_ = lean_ctor_get(v_toEnvExtension_1097_, 2);
v___x_1101_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1083_, v___x_1096_, v_env_1076_, v_asyncMode_1100_, v___x_1092_);
lean_inc_ref(v_exportEntriesFn_1099_);
v___x_1102_ = lean_apply_2(v_exportEntriesFn_1099_, v_env_1076_, v___x_1101_);
v_private_1103_ = lean_ctor_get(v___x_1102_, 2);
lean_inc(v_private_1103_);
lean_dec_ref(v___x_1102_);
lean_inc(v_name_1079_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_name_1079_);
lean_ctor_set(v___x_1104_, 1, v___y_1085_);
lean_inc(v_name_1089_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_name_1089_);
lean_ctor_set(v___x_1105_, 1, v_private_1095_);
lean_inc(v_name_1098_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_name_1098_);
lean_ctor_set(v___x_1106_, 1, v_private_1103_);
v___x_1107_ = lean_unsigned_to_nat(3u);
v___x_1108_ = lean_mk_empty_array_with_capacity(v___x_1107_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1104_);
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1105_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1106_);
return v___x_1111_;
}
v___jp_1117_:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1116_, v_irDecls_1115_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
v___y_1085_ = v___x_1120_;
goto v___jp_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1128_, lean_object* v_k_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_m_1134_; lean_object* v_a_1135_; uint8_t v___x_1136_; 
v___x_1132_ = lean_nat_add(v_x_1130_, v_x_1131_);
v___x_1133_ = lean_unsigned_to_nat(1u);
v_m_1134_ = lean_nat_shiftr(v___x_1132_, v___x_1133_);
lean_dec(v___x_1132_);
v_a_1135_ = lean_array_fget_borrowed(v_as_1128_, v_m_1134_);
v___x_1136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1135_, v_k_1129_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; 
lean_dec(v_x_1131_);
v___x_1137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1129_, v_a_1135_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v_m_1134_);
lean_dec(v_x_1130_);
lean_inc(v_a_1135_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_a_1135_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_nat_dec_eq(v_m_1134_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_nat_sub(v_m_1134_, v___x_1133_);
lean_dec(v_m_1134_);
v___x_1142_ = lean_nat_dec_lt(v___x_1141_, v_x_1130_);
if (v___x_1142_ == 0)
{
v_x_1131_ = v___x_1141_;
goto _start;
}
else
{
lean_object* v___x_1144_; 
lean_dec(v___x_1141_);
lean_dec(v_x_1130_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
}
else
{
lean_object* v___x_1145_; 
lean_dec(v_m_1134_);
lean_dec(v_x_1130_);
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
}
}
else
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
lean_dec(v_x_1130_);
v___x_1146_ = lean_nat_add(v_m_1134_, v___x_1133_);
lean_dec(v_m_1134_);
v___x_1147_ = lean_nat_dec_le(v___x_1146_, v_x_1131_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec(v___x_1146_);
lean_dec(v_x_1131_);
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
else
{
v_x_1130_ = v___x_1146_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1150_, lean_object* v_k_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1150_, v_k_1151_, v_x_1152_, v_x_1153_);
lean_dec_ref(v_k_1151_);
lean_dec_ref(v_as_1150_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_i_1157_, lean_object* v_k_1158_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_array_get_size(v_keys_1155_);
v___x_1160_ = lean_nat_dec_lt(v_i_1157_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_i_1157_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
else
{
lean_object* v_k_x27_1162_; uint8_t v___x_1163_; 
v_k_x27_1162_ = lean_array_fget_borrowed(v_keys_1155_, v_i_1157_);
v___x_1163_ = lean_name_eq(v_k_1158_, v_k_x27_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_i_1157_, v___x_1164_);
lean_dec(v_i_1157_);
v_i_1157_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_array_fget_borrowed(v_vals_1156_, v_i_1157_);
lean_dec(v_i_1157_);
lean_inc(v___x_1167_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1169_, lean_object* v_vals_1170_, lean_object* v_i_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1169_, v_vals_1170_, v_i_1171_, v_k_1172_);
lean_dec(v_k_1172_);
lean_dec_ref(v_vals_1170_);
lean_dec_ref(v_keys_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1174_, size_t v_x_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_es_1177_; lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v_j_1181_; lean_object* v___x_1182_; 
v_es_1177_ = lean_ctor_get(v_x_1174_, 0);
v___x_1178_ = lean_box(2);
v___x_1179_ = ((size_t)31ULL);
v___x_1180_ = lean_usize_land(v_x_1175_, v___x_1179_);
v_j_1181_ = lean_usize_to_nat(v___x_1180_);
v___x_1182_ = lean_array_get_borrowed(v___x_1178_, v_es_1177_, v_j_1181_);
lean_dec(v_j_1181_);
switch(lean_obj_tag(v___x_1182_))
{
case 0:
{
lean_object* v_key_1183_; lean_object* v_val_1184_; uint8_t v___x_1185_; 
v_key_1183_ = lean_ctor_get(v___x_1182_, 0);
v_val_1184_ = lean_ctor_get(v___x_1182_, 1);
v___x_1185_ = lean_name_eq(v_x_1176_, v_key_1183_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_box(0);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_inc(v_val_1184_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_val_1184_);
return v___x_1187_;
}
}
case 1:
{
lean_object* v_node_1188_; size_t v___x_1189_; size_t v___x_1190_; 
v_node_1188_ = lean_ctor_get(v___x_1182_, 0);
v___x_1189_ = ((size_t)5ULL);
v___x_1190_ = lean_usize_shift_right(v_x_1175_, v___x_1189_);
v_x_1174_ = v_node_1188_;
v_x_1175_ = v___x_1190_;
goto _start;
}
default: 
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
}
}
else
{
lean_object* v_ks_1193_; lean_object* v_vs_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_ks_1193_ = lean_ctor_get(v_x_1174_, 0);
v_vs_1194_ = lean_ctor_get(v_x_1174_, 1);
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1193_, v_vs_1194_, v___x_1195_, v_x_1176_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
size_t v_x_405__boxed_1200_; lean_object* v_res_1201_; 
v_x_405__boxed_1200_ = lean_unbox_usize(v_x_1198_);
lean_dec(v_x_1198_);
v_res_1201_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1197_, v_x_405__boxed_1200_, v_x_1199_);
lean_dec(v_x_1199_);
lean_dec_ref(v_x_1197_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1202_, lean_object* v_x_1203_){
_start:
{
uint64_t v___y_1205_; 
if (lean_obj_tag(v_x_1203_) == 0)
{
uint64_t v___x_1208_; 
v___x_1208_ = 1723ULL;
v___y_1205_ = v___x_1208_;
goto v___jp_1204_;
}
else
{
uint64_t v_hash_1209_; 
v_hash_1209_ = lean_ctor_get_uint64(v_x_1203_, sizeof(void*)*2);
v___y_1205_ = v_hash_1209_;
goto v___jp_1204_;
}
v___jp_1204_:
{
size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_uint64_to_usize(v___y_1205_);
v___x_1207_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1202_, v___x_1206_, v_x_1203_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1210_, v_x_1211_);
lean_dec(v_x_1211_);
lean_dec_ref(v_x_1210_);
return v_res_1212_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1216_, lean_object* v_declName_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1228_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1220_ = l_Lean_IR_declMapExt;
v___x_1228_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1216_, v_declName_1217_);
if (lean_obj_tag(v___x_1228_) == 0)
{
goto v___jp_1221_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1243_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1219_, v___x_1220_, v_env_1216_, v_val_1229_);
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
lean_inc(v_declName_1217_);
v_tmpDecl_1252_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1252_, 0, v_declName_1217_);
lean_ctor_set(v_tmpDecl_1252_, 1, v___x_1250_);
lean_ctor_set(v_tmpDecl_1252_, 2, v___x_1251_);
lean_ctor_set(v_tmpDecl_1252_, 3, v___x_1218_);
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
lean_dec(v_declName_1217_);
lean_dec_ref(v_env_1216_);
return v___x_1253_;
}
}
}
v___jp_1230_:
{
uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1231_ = 0;
v___x_1232_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1219_, v___x_1220_, v_env_1216_, v_val_1229_, v___x_1231_);
lean_dec(v_val_1229_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_array_get_size(v___x_1232_);
v___x_1235_ = lean_nat_dec_lt(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v___x_1232_);
goto v___jp_1221_;
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
goto v___jp_1221_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_tmpDecl_1241_; lean_object* v___x_1242_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1240_ = lean_box(0);
lean_inc(v_declName_1217_);
v_tmpDecl_1241_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1241_, 0, v_declName_1217_);
lean_ctor_set(v_tmpDecl_1241_, 1, v___x_1239_);
lean_ctor_set(v_tmpDecl_1241_, 2, v___x_1240_);
lean_ctor_set(v_tmpDecl_1241_, 3, v___x_1218_);
v___x_1242_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1232_, v_tmpDecl_1241_, v___x_1233_, v___x_1237_);
lean_dec_ref_known(v_tmpDecl_1241_, 4);
lean_dec_ref(v___x_1232_);
if (lean_obj_tag(v___x_1242_) == 0)
{
goto v___jp_1221_;
}
else
{
lean_dec(v_declName_1217_);
lean_dec_ref(v_env_1216_);
return v___x_1242_;
}
}
}
}
}
v___jp_1221_:
{
lean_object* v_toEnvExtension_1222_; lean_object* v_asyncMode_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_snd_1226_; lean_object* v___x_1227_; 
v_toEnvExtension_1222_ = lean_ctor_get(v___x_1220_, 0);
v_asyncMode_1223_ = lean_ctor_get(v_toEnvExtension_1222_, 2);
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1219_, v___x_1220_, v_env_1216_, v_asyncMode_1223_, v___x_1224_);
v_snd_1226_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_snd_1226_);
lean_dec(v___x_1225_);
v___x_1227_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1226_, v_declName_1217_);
lean_dec(v_declName_1217_);
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
size_t v_x_569__boxed_1283_; lean_object* v_res_1284_; 
v_x_569__boxed_1283_ = lean_unbox_usize(v_x_1281_);
lean_dec(v_x_1281_);
v_res_1284_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1279_, v_x_1280_, v_x_569__boxed_1283_, v_x_1282_);
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
v___x_1301_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
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
v___x_1342_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
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
v___x_1388_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
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
v_ref_1457_ = lean_ctor_get(v___y_1454_, 5);
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
lean_object* v___x_1518_; lean_object* v_env_1519_; lean_object* v___x_1520_; lean_object* v_toEnvExtension_1521_; lean_object* v_asyncMode_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1518_ = lean_st_ref_get(v_a_1516_);
v_env_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_ref(v_env_1519_);
lean_dec(v___x_1518_);
v___x_1520_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1521_ = lean_ctor_get(v___x_1520_, 0);
v_asyncMode_1522_ = lean_ctor_get(v_toEnvExtension_1521_, 2);
v___x_1523_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1524_ = lean_box(0);
v___x_1525_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1523_, v___x_1520_, v_env_1519_, v_asyncMode_1522_, v___x_1524_);
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
v___x_1546_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1547_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1546_, v___x_1543_, v_env_1542_, v_asyncMode_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v_env_1557_; lean_object* v_nextMacroScope_1558_; lean_object* v_ngen_1559_; lean_object* v_auxDeclNGen_1560_; lean_object* v_traceState_1561_; lean_object* v_messages_1562_; lean_object* v_infoState_1563_; lean_object* v_snapshotTasks_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1580_; 
v___x_1556_ = lean_st_ref_take(v_a_1554_);
v_env_1557_ = lean_ctor_get(v___x_1556_, 0);
v_nextMacroScope_1558_ = lean_ctor_get(v___x_1556_, 1);
v_ngen_1559_ = lean_ctor_get(v___x_1556_, 2);
v_auxDeclNGen_1560_ = lean_ctor_get(v___x_1556_, 3);
v_traceState_1561_ = lean_ctor_get(v___x_1556_, 4);
v_messages_1562_ = lean_ctor_get(v___x_1556_, 6);
v_infoState_1563_ = lean_ctor_get(v___x_1556_, 7);
v_snapshotTasks_1564_ = lean_ctor_get(v___x_1556_, 8);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1556_, 5);
lean_dec(v_unused_1581_);
v___x_1566_ = v___x_1556_;
v_isShared_1567_ = v_isSharedCheck_1580_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snapshotTasks_1564_);
lean_inc(v_infoState_1563_);
lean_inc(v_messages_1562_);
lean_inc(v_traceState_1561_);
lean_inc(v_auxDeclNGen_1560_);
lean_inc(v_ngen_1559_);
lean_inc(v_nextMacroScope_1558_);
lean_inc(v_env_1557_);
lean_dec(v___x_1556_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1580_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v_toEnvExtension_1569_; lean_object* v_asyncMode_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1568_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1569_ = lean_ctor_get(v___x_1568_, 0);
v_asyncMode_1570_ = lean_ctor_get(v_toEnvExtension_1569_, 2);
v___x_1571_ = lean_box(0);
v___x_1572_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1568_, v_env_1557_, v_decl_1553_, v_asyncMode_1570_, v___x_1571_);
v___x_1573_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 5, v___x_1573_);
lean_ctor_set(v___x_1566_, 0, v___x_1572_);
v___x_1575_ = v___x_1566_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_nextMacroScope_1558_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_ngen_1559_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_auxDeclNGen_1560_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_traceState_1561_);
lean_ctor_set(v_reuseFailAlloc_1579_, 5, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1579_, 6, v_messages_1562_);
lean_ctor_set(v_reuseFailAlloc_1579_, 7, v_infoState_1563_);
lean_ctor_set(v_reuseFailAlloc_1579_, 8, v_snapshotTasks_1564_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_st_ref_set(v_a_1554_, v___x_1575_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_IR_addDecl___redArg(v_decl_1582_, v_a_1583_);
lean_dec(v_a_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_IR_addDecl___redArg(v_decl_1586_, v_a_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_IR_addDecl(v_decl_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1596_, size_t v_i_1597_, size_t v_stop_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_usize_dec_eq(v_i_1597_, v_stop_1598_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_array_uget_borrowed(v_as_1596_, v_i_1597_);
lean_inc(v___x_1603_);
v___x_1604_ = l_Lean_IR_addDecl___redArg(v___x_1603_, v___y_1600_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; size_t v___x_1606_; size_t v___x_1607_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = ((size_t)1ULL);
v___x_1607_ = lean_usize_add(v_i_1597_, v___x_1606_);
v_i_1597_ = v___x_1607_;
v_b_1599_ = v_a_1605_;
goto _start;
}
else
{
return v___x_1604_;
}
}
else
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_b_1599_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1610_, lean_object* v_i_1611_, lean_object* v_stop_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
size_t v_i_boxed_1616_; size_t v_stop_boxed_1617_; lean_object* v_res_1618_; 
v_i_boxed_1616_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_stop_boxed_1617_ = lean_unbox_usize(v_stop_1612_);
lean_dec(v_stop_1612_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1610_, v_i_boxed_1616_, v_stop_boxed_1617_, v_b_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v_as_1610_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_array_get_size(v_decls_1619_);
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_nat_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
return v___x_1627_;
}
else
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_nat_dec_le(v___x_1624_, v___x_1624_);
if (v___x_1628_ == 0)
{
if (v___x_1626_ == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1625_);
return v___x_1629_;
}
else
{
size_t v___x_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((size_t)0ULL);
v___x_1631_ = lean_usize_of_nat(v___x_1624_);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1619_, v___x_1630_, v___x_1631_, v___x_1625_, v_a_1621_);
return v___x_1632_;
}
}
else
{
size_t v___x_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = lean_usize_of_nat(v___x_1624_);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1619_, v___x_1633_, v___x_1634_, v___x_1625_, v_a_1621_);
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_IR_addDecls(v_decls_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec_ref(v_decls_1636_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1641_, size_t v_i_1642_, size_t v_stop_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1641_, v_i_1642_, v_stop_1643_, v_b_1644_, v___y_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1649_, lean_object* v_i_1650_, lean_object* v_stop_1651_, lean_object* v_b_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
size_t v_i_boxed_1656_; size_t v_stop_boxed_1657_; lean_object* v_res_1658_; 
v_i_boxed_1656_ = lean_unbox_usize(v_i_1650_);
lean_dec(v_i_1650_);
v_stop_boxed_1657_ = lean_unbox_usize(v_stop_1651_);
lean_dec(v_stop_1651_);
v_res_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1649_, v_i_boxed_1656_, v_stop_boxed_1657_, v_b_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_as_1649_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1662_, lean_object* v_as_1663_, size_t v_sz_1664_, size_t v_i_1665_, lean_object* v_b_1666_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_usize_dec_lt(v_i_1665_, v_sz_1664_);
if (v___x_1667_ == 0)
{
lean_inc_ref(v_b_1666_);
return v_b_1666_;
}
else
{
lean_object* v___x_1668_; lean_object* v_a_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1668_ = lean_box(0);
v_a_1669_ = lean_array_uget_borrowed(v_as_1663_, v_i_1665_);
v___x_1670_ = l_Lean_IR_Decl_name(v_a_1669_);
v___x_1671_ = lean_name_eq(v___x_1670_, v_n_1662_);
lean_dec(v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; 
v___x_1672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1673_ = ((size_t)1ULL);
v___x_1674_ = lean_usize_add(v_i_1665_, v___x_1673_);
v_i_1665_ = v___x_1674_;
v_b_1666_ = v___x_1672_;
goto _start;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_inc(v_a_1669_);
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_a_1669_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v___x_1668_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1679_, lean_object* v_as_1680_, lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_b_1683_){
_start:
{
size_t v_sz_boxed_1684_; size_t v_i_boxed_1685_; lean_object* v_res_1686_; 
v_sz_boxed_1684_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1685_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1679_, v_as_1680_, v_sz_boxed_1684_, v_i_boxed_1685_, v_b_1683_);
lean_dec_ref(v_b_1683_);
lean_dec_ref(v_as_1680_);
lean_dec(v_n_1679_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1687_, lean_object* v_n_1688_, lean_object* v_decls_1689_){
_start:
{
lean_object* v___x_1690_; size_t v_sz_1691_; size_t v___x_1692_; lean_object* v___x_1693_; lean_object* v_fst_1694_; 
v___x_1690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1691_ = lean_array_size(v_decls_1689_);
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1688_, v_decls_1689_, v_sz_1691_, v___x_1692_, v___x_1690_);
v_fst_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_fst_1694_);
lean_dec_ref(v___x_1693_);
if (lean_obj_tag(v_fst_1694_) == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_IR_findEnvDecl(v_env_1687_, v_n_1688_);
return v___x_1695_;
}
else
{
lean_object* v_val_1696_; 
v_val_1696_ = lean_ctor_get(v_fst_1694_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_fst_1694_, 1);
if (lean_obj_tag(v_val_1696_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_IR_findEnvDecl(v_env_1687_, v_n_1688_);
return v___x_1697_;
}
else
{
lean_dec(v_n_1688_);
lean_dec_ref(v_env_1687_);
return v_val_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1698_, lean_object* v_n_1699_, lean_object* v_decls_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_IR_findEnvDecl_x27(v_env_1698_, v_n_1699_, v_decls_1700_);
lean_dec_ref(v_decls_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1702_, lean_object* v_decls_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_env_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = lean_st_ref_get(v_a_1704_);
v_env_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc_ref(v_env_1707_);
lean_dec(v___x_1706_);
v___x_1708_ = l_Lean_IR_findEnvDecl_x27(v_env_1707_, v_n_1702_, v_decls_1703_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1710_, lean_object* v_decls_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_IR_findDecl_x27___redArg(v_n_1710_, v_decls_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_decls_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1715_, lean_object* v_decls_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_IR_findDecl_x27___redArg(v_n_1715_, v_decls_1716_, v_a_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1721_, lean_object* v_decls_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_IR_findDecl_x27(v_n_1721_, v_decls_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec_ref(v_decls_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1727_, lean_object* v_as_1728_, size_t v_i_1729_, size_t v_stop_1730_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_eq(v_i_1729_, v_stop_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = lean_array_uget_borrowed(v_as_1728_, v_i_1729_);
v___x_1733_ = l_Lean_IR_Decl_name(v___x_1732_);
v___x_1734_ = lean_name_eq(v___x_1733_, v_n_1727_);
lean_dec(v___x_1733_);
if (v___x_1734_ == 0)
{
size_t v___x_1735_; size_t v___x_1736_; 
v___x_1735_ = ((size_t)1ULL);
v___x_1736_ = lean_usize_add(v_i_1729_, v___x_1735_);
v_i_1729_ = v___x_1736_;
goto _start;
}
else
{
return v___x_1734_;
}
}
else
{
uint8_t v___x_1738_; 
v___x_1738_ = 0;
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1739_, lean_object* v_as_1740_, lean_object* v_i_1741_, lean_object* v_stop_1742_){
_start:
{
size_t v_i_boxed_1743_; size_t v_stop_boxed_1744_; uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_i_boxed_1743_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_stop_boxed_1744_ = lean_unbox_usize(v_stop_1742_);
lean_dec(v_stop_1742_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1739_, v_as_1740_, v_i_boxed_1743_, v_stop_boxed_1744_);
lean_dec_ref(v_as_1740_);
lean_dec(v_n_1739_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1747_, lean_object* v_decls_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_array_get_size(v_decls_1748_);
v___x_1753_ = lean_nat_dec_lt(v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_IR_containsDecl___redArg(v_n_1747_, v_a_1749_);
return v___x_1754_;
}
else
{
if (v___x_1753_ == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_IR_containsDecl___redArg(v_n_1747_, v_a_1749_);
return v___x_1755_;
}
else
{
size_t v___x_1756_; size_t v___x_1757_; uint8_t v___x_1758_; 
v___x_1756_ = ((size_t)0ULL);
v___x_1757_ = lean_usize_of_nat(v___x_1752_);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1747_, v_decls_1748_, v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_IR_containsDecl___redArg(v_n_1747_, v_a_1749_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_n_1747_);
v___x_1760_ = lean_box(v___x_1758_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1762_, lean_object* v_decls_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1762_, v_decls_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_decls_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1767_, lean_object* v_decls_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1767_, v_decls_1768_, v_a_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1773_, lean_object* v_decls_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_IR_containsDecl_x27(v_n_1773_, v_decls_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec_ref(v_decls_1774_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1779_, lean_object* v_decls_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1802_; 
lean_inc(v_n_1779_);
v___x_1784_ = l_Lean_IR_findDecl_x27___redArg(v_n_1779_, v_decls_1780_, v_a_1782_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1802_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1802_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
if (lean_obj_tag(v_a_1785_) == 1)
{
lean_object* v_val_1789_; lean_object* v___x_1791_; 
lean_dec(v_n_1779_);
v_val_1789_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v_a_1785_, 1);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v_val_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_val_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_del_object(v___x_1787_);
lean_dec(v_a_1785_);
v___x_1793_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1794_ = 1;
v___x_1795_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1779_, v___x_1794_);
v___x_1796_ = lean_string_append(v___x_1793_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1798_ = lean_string_append(v___x_1796_, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
v___x_1800_ = l_Lean_MessageData_ofFormat(v___x_1799_);
v___x_1801_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1800_, v_a_1781_, v_a_1782_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1803_, lean_object* v_decls_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_IR_getDecl_x27(v_n_1803_, v_decls_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec_ref(v_decls_1804_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1809_, lean_object* v_declName_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_IR_findEnvDecl(v_env_1809_, v_declName_1810_);
if (lean_obj_tag(v___x_1811_) == 1)
{
lean_object* v_val_1812_; 
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1812_);
lean_dec_ref_known(v___x_1811_, 1);
if (lean_obj_tag(v_val_1812_) == 0)
{
lean_object* v_info_1813_; 
v_info_1813_ = lean_ctor_get(v_val_1812_, 4);
lean_inc(v_info_1813_);
lean_dec_ref_known(v_val_1812_, 5);
return v_info_1813_;
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_val_1812_);
v___x_1814_ = lean_box(0);
return v___x_1814_;
}
}
else
{
lean_object* v___x_1815_; 
lean_dec(v___x_1811_);
v___x_1815_ = lean_box(0);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1816_, uint8_t v_level_1817_, uint8_t v_includeDecls_1818_, lean_object* v_as_1819_, size_t v_i_1820_, size_t v_stop_1821_, lean_object* v_b_1822_){
_start:
{
lean_object* v___y_1824_; uint8_t v___x_1828_; 
v___x_1828_ = lean_usize_dec_eq(v_i_1820_, v_stop_1821_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; uint8_t v___y_1831_; 
v___x_1829_ = lean_array_uget_borrowed(v_as_1819_, v_i_1820_);
if (v_includeDecls_1818_ == 0)
{
uint8_t v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = 1;
lean_inc(v___x_1829_);
lean_inc_ref(v_env_1816_);
v___x_1840_ = l_Lean_Environment_contains(v_env_1816_, v___x_1829_, v___x_1839_);
if (v___x_1840_ == 0)
{
goto v___jp_1835_;
}
else
{
v___y_1824_ = v_b_1822_;
goto v___jp_1823_;
}
}
else
{
goto v___jp_1835_;
}
v___jp_1830_:
{
if (v___y_1831_ == 0)
{
uint8_t v___x_1832_; 
lean_inc_ref(v_env_1816_);
v___x_1832_ = l_Lean_isDeclMeta(v_env_1816_, v___x_1829_);
if (v___x_1832_ == 0)
{
v___y_1824_ = v_b_1822_;
goto v___jp_1823_;
}
else
{
lean_object* v___x_1833_; 
lean_inc(v___x_1829_);
v___x_1833_ = lean_array_push(v_b_1822_, v___x_1829_);
v___y_1824_ = v___x_1833_;
goto v___jp_1823_;
}
}
else
{
lean_object* v___x_1834_; 
lean_inc(v___x_1829_);
v___x_1834_ = lean_array_push(v_b_1822_, v___x_1829_);
v___y_1824_ = v___x_1834_;
goto v___jp_1823_;
}
}
v___jp_1835_:
{
uint8_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = 2;
v___x_1837_ = l_Lean_instDecidableEqOLeanLevel(v_level_1817_, v___x_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
lean_inc_ref(v_env_1816_);
v___x_1838_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1816_, v___x_1829_);
v___y_1831_ = v___x_1838_;
goto v___jp_1830_;
}
else
{
v___y_1831_ = v___x_1837_;
goto v___jp_1830_;
}
}
}
else
{
lean_dec_ref(v_env_1816_);
return v_b_1822_;
}
v___jp_1823_:
{
size_t v___x_1825_; size_t v___x_1826_; 
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_i_1820_, v___x_1825_);
v_i_1820_ = v___x_1826_;
v_b_1822_ = v___y_1824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1841_, lean_object* v_level_1842_, lean_object* v_includeDecls_1843_, lean_object* v_as_1844_, lean_object* v_i_1845_, lean_object* v_stop_1846_, lean_object* v_b_1847_){
_start:
{
uint8_t v_level_boxed_1848_; uint8_t v_includeDecls_boxed_1849_; size_t v_i_boxed_1850_; size_t v_stop_boxed_1851_; lean_object* v_res_1852_; 
v_level_boxed_1848_ = lean_unbox(v_level_1842_);
v_includeDecls_boxed_1849_ = lean_unbox(v_includeDecls_1843_);
v_i_boxed_1850_ = lean_unbox_usize(v_i_1845_);
lean_dec(v_i_1845_);
v_stop_boxed_1851_ = lean_unbox_usize(v_stop_1846_);
lean_dec(v_stop_1846_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1841_, v_level_boxed_1848_, v_includeDecls_boxed_1849_, v_as_1844_, v_i_boxed_1850_, v_stop_boxed_1851_, v_b_1847_);
lean_dec_ref(v_as_1844_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1853_, size_t v_i_1854_, lean_object* v_bs_1855_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_lt(v_i_1854_, v_sz_1853_);
if (v___x_1856_ == 0)
{
return v_bs_1855_;
}
else
{
lean_object* v_v_1857_; lean_object* v___x_1858_; lean_object* v_bs_x27_1859_; lean_object* v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v_v_1857_ = lean_array_uget(v_bs_1855_, v_i_1854_);
v___x_1858_ = lean_unsigned_to_nat(0u);
v_bs_x27_1859_ = lean_array_uset(v_bs_1855_, v_i_1854_, v___x_1858_);
v___x_1860_ = l_Lean_IR_Decl_name(v_v_1857_);
lean_dec(v_v_1857_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1854_, v___x_1861_);
v___x_1863_ = lean_array_uset(v_bs_x27_1859_, v_i_1854_, v___x_1860_);
v_i_1854_ = v___x_1862_;
v_bs_1855_ = v___x_1863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1865_, lean_object* v_i_1866_, lean_object* v_bs_1867_){
_start:
{
size_t v_sz_boxed_1868_; size_t v_i_boxed_1869_; lean_object* v_res_1870_; 
v_sz_boxed_1868_ = lean_unbox_usize(v_sz_1865_);
lean_dec(v_sz_1865_);
v_i_boxed_1869_ = lean_unbox_usize(v_i_1866_);
lean_dec(v_i_1866_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1868_, v_i_boxed_1869_, v_bs_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1873_, uint8_t v_level_1874_, uint8_t v_includeDecls_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v_toEnvExtension_1877_; lean_object* v_asyncMode_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; uint8_t v___x_1881_; lean_object* v_env_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; size_t v_sz_1885_; size_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1876_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1877_ = lean_ctor_get(v___x_1876_, 0);
v_asyncMode_1878_ = lean_ctor_get(v_toEnvExtension_1877_, 2);
v___x_1879_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1880_ = 0;
v___x_1881_ = l_Lean_instDecidableEqOLeanLevel(v_level_1874_, v___x_1880_);
v_env_1882_ = l_Lean_Environment_setExporting(v_env_1873_, v___x_1881_);
lean_inc_ref(v_env_1882_);
v___x_1883_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1879_, v___x_1876_, v_env_1882_, v_asyncMode_1878_);
v___x_1884_ = lean_array_mk(v___x_1883_);
v_sz_1885_ = lean_array_size(v___x_1884_);
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1885_, v___x_1886_, v___x_1884_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_array_get_size(v___x_1887_);
v___x_1890_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1891_ = lean_nat_dec_lt(v___x_1888_, v___x_1889_);
if (v___x_1891_ == 0)
{
lean_dec_ref(v___x_1887_);
lean_dec_ref(v_env_1882_);
return v___x_1890_;
}
else
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_nat_dec_le(v___x_1889_, v___x_1889_);
if (v___x_1892_ == 0)
{
if (v___x_1891_ == 0)
{
lean_dec_ref(v___x_1887_);
lean_dec_ref(v_env_1882_);
return v___x_1890_;
}
else
{
size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_usize_of_nat(v___x_1889_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1882_, v_level_1874_, v_includeDecls_1875_, v___x_1887_, v___x_1886_, v___x_1893_, v___x_1890_);
lean_dec_ref(v___x_1887_);
return v___x_1894_;
}
}
else
{
size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_usize_of_nat(v___x_1889_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1882_, v_level_1874_, v_includeDecls_1875_, v___x_1887_, v___x_1886_, v___x_1895_, v___x_1890_);
lean_dec_ref(v___x_1887_);
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1897_, lean_object* v_level_1898_, lean_object* v_includeDecls_1899_){
_start:
{
uint8_t v_level_boxed_1900_; uint8_t v_includeDecls_boxed_1901_; lean_object* v_res_1902_; 
v_level_boxed_1900_ = lean_unbox(v_level_1898_);
v_includeDecls_boxed_1901_ = lean_unbox(v_includeDecls_1899_);
v_res_1902_ = lean_get_ir_extra_const_names(v_env_1897_, v_level_boxed_1900_, v_includeDecls_boxed_1901_);
return v_res_1902_;
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
