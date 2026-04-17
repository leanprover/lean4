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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1;
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
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_cls_8_, v_decls_9_);
return v___x_10_;
}
else
{
lean_object* v_msg_11_; lean_object* v___x_12_; 
v_msg_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_msg_11_);
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_x_74_);
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
lean_dec_ref(v___x_287_);
if (lean_obj_tag(v_val_288_) == 1)
{
uint8_t v_v_289_; 
v_v_289_ = lean_ctor_get_uint8(v_val_288_, 0);
lean_dec_ref(v_val_288_);
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
lean_dec_ref(v___x_284_);
if (lean_obj_tag(v_val_285_) == 1)
{
uint8_t v_v_286_; 
v_v_286_ = lean_ctor_get_uint8(v_val_285_, 0);
lean_dec_ref(v_val_285_);
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
lean_dec_ref(v___x_576_);
if (lean_obj_tag(v_val_577_) == 1)
{
lean_object* v_str_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_str_578_ = lean_ctor_get(v_val_577_, 1);
lean_inc_ref(v_str_578_);
lean_dec_ref(v_val_577_);
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
lean_inc(v_type_575_);
lean_inc(v_f_573_);
lean_inc_ref(v_xs_574_);
v___y_563_ = v_xs_574_;
v___y_564_ = v_f_573_;
v___y_565_ = v_type_575_;
goto v___jp_562_;
}
}
else
{
lean_dec(v___x_576_);
lean_inc(v_type_575_);
lean_inc(v_f_573_);
lean_inc_ref(v_xs_574_);
v___y_563_ = v_xs_574_;
v___y_564_ = v_f_573_;
v___y_565_ = v_type_575_;
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
lean_ctor_set(v___x_567_, 0, v___y_564_);
lean_ctor_set(v___x_567_, 1, v___y_563_);
lean_ctor_set(v___x_567_, 2, v___y_565_);
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
lean_dec_ref(v_x_625_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; 
v___x_678_ = ((size_t)5ULL);
v___x_679_ = ((size_t)1ULL);
v___x_680_ = lean_usize_shift_left(v___x_679_, v___x_678_);
return v___x_680_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_681_; size_t v___x_682_; size_t v___x_683_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_683_ = lean_usize_sub(v___x_682_, v___x_681_);
return v___x_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_684_, size_t v_x_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_object* v_es_687_; lean_object* v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v_j_692_; lean_object* v___x_693_; 
v_es_687_ = lean_ctor_get(v_x_684_, 0);
v___x_688_ = lean_box(2);
v___x_689_ = ((size_t)5ULL);
v___x_690_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_691_ = lean_usize_land(v_x_685_, v___x_690_);
v_j_692_ = lean_usize_to_nat(v___x_691_);
v___x_693_ = lean_array_get_borrowed(v___x_688_, v_es_687_, v_j_692_);
lean_dec(v_j_692_);
switch(lean_obj_tag(v___x_693_))
{
case 0:
{
lean_object* v_key_694_; uint8_t v___x_695_; 
v_key_694_ = lean_ctor_get(v___x_693_, 0);
v___x_695_ = lean_name_eq(v_x_686_, v_key_694_);
return v___x_695_;
}
case 1:
{
lean_object* v_node_696_; size_t v___x_697_; 
v_node_696_ = lean_ctor_get(v___x_693_, 0);
v___x_697_ = lean_usize_shift_right(v_x_685_, v___x_689_);
v_x_684_ = v_node_696_;
v_x_685_ = v___x_697_;
goto _start;
}
default: 
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
}
else
{
lean_object* v_ks_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_ks_700_ = lean_ctor_get(v_x_684_, 0);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_700_, v___x_701_, v_x_686_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
size_t v_x_2626__boxed_706_; uint8_t v_res_707_; lean_object* v_r_708_; 
v_x_2626__boxed_706_ = lean_unbox_usize(v_x_704_);
lean_dec(v_x_704_);
v_res_707_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_703_, v_x_2626__boxed_706_, v_x_705_);
lean_dec(v_x_705_);
lean_dec_ref(v_x_703_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_709_; uint64_t v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(1723u);
v___x_710_ = lean_uint64_of_nat(v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint64_t v___y_714_; 
if (lean_obj_tag(v_x_712_) == 0)
{
uint64_t v___x_717_; 
v___x_717_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_714_ = v___x_717_;
goto v___jp_713_;
}
else
{
uint64_t v_hash_718_; 
v_hash_718_ = lean_ctor_get_uint64(v_x_712_, sizeof(void*)*2);
v___y_714_ = v_hash_718_;
goto v___jp_713_;
}
v___jp_713_:
{
size_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = lean_uint64_to_usize(v___y_714_);
v___x_716_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_711_, v___x_715_, v_x_712_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_723_, lean_object* v_x2_724_){
_start:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = l_Lean_IR_Decl_name(v_x2_724_);
v___x_726_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_723_, v___x_725_);
lean_dec(v___x_725_);
if (v___x_726_ == 0)
{
uint8_t v___x_727_; 
v___x_727_ = 1;
return v___x_727_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = 0;
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_729_, lean_object* v_x2_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_729_, v_x2_730_);
lean_dec_ref(v_x2_730_);
lean_dec_ref(v_x1_729_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_738_);
lean_dec_ref(v_x_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_ks_744_; lean_object* v_vs_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_769_; 
v_ks_744_ = lean_ctor_get(v_x_740_, 0);
v_vs_745_ = lean_ctor_get(v_x_740_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_769_ == 0)
{
v___x_747_ = v_x_740_;
v_isShared_748_ = v_isSharedCheck_769_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_vs_745_);
lean_inc(v_ks_744_);
lean_dec(v_x_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_769_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_ks_744_);
v___x_750_ = lean_nat_dec_lt(v_x_741_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_x_741_);
v___x_751_ = lean_array_push(v_ks_744_, v_x_742_);
v___x_752_ = lean_array_push(v_vs_745_, v_x_743_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_752_);
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v_k_x27_756_; uint8_t v___x_757_; 
v_k_x27_756_ = lean_array_fget_borrowed(v_ks_744_, v_x_741_);
v___x_757_ = lean_name_eq(v_x_742_, v_k_x27_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_759_; 
if (v_isShared_748_ == 0)
{
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_ks_744_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_vs_745_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_x_741_, v___x_760_);
lean_dec(v_x_741_);
v_x_740_ = v___x_759_;
v_x_741_ = v___x_761_;
goto _start;
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_764_ = lean_array_fset(v_ks_744_, v_x_741_, v_x_742_);
v___x_765_ = lean_array_fset(v_vs_745_, v_x_741_, v_x_743_);
lean_dec(v_x_741_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_765_);
lean_ctor_set(v___x_747_, 0, v___x_764_);
v___x_767_ = v___x_747_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_770_, lean_object* v_k_771_, lean_object* v_v_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_770_, v___x_773_, v_k_771_, v_v_772_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_776_, size_t v_x_777_, size_t v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v_es_781_; size_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v_j_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_es_781_ = lean_ctor_get(v_x_776_, 0);
v___x_782_ = ((size_t)5ULL);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_785_ = lean_usize_land(v_x_777_, v___x_784_);
v_j_786_ = lean_usize_to_nat(v___x_785_);
v___x_787_ = lean_array_get_size(v_es_781_);
v___x_788_ = lean_nat_dec_lt(v_j_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec(v_j_786_);
lean_dec(v_x_780_);
lean_dec(v_x_779_);
return v_x_776_;
}
else
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_825_; 
lean_inc_ref(v_es_781_);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_x_776_, 0);
lean_dec(v_unused_826_);
v___x_790_ = v_x_776_;
v_isShared_791_ = v_isSharedCheck_825_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_x_776_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_825_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_v_792_; lean_object* v___x_793_; lean_object* v_xs_x27_794_; lean_object* v___y_796_; 
v_v_792_ = lean_array_fget(v_es_781_, v_j_786_);
v___x_793_ = lean_box(0);
v_xs_x27_794_ = lean_array_fset(v_es_781_, v_j_786_, v___x_793_);
switch(lean_obj_tag(v_v_792_))
{
case 0:
{
lean_object* v_key_801_; lean_object* v_val_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_812_; 
v_key_801_ = lean_ctor_get(v_v_792_, 0);
v_val_802_ = lean_ctor_get(v_v_792_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_v_792_);
if (v_isSharedCheck_812_ == 0)
{
v___x_804_ = v_v_792_;
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_val_802_);
lean_inc(v_key_801_);
lean_dec(v_v_792_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
uint8_t v___x_806_; 
v___x_806_ = lean_name_eq(v_x_779_, v_key_801_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_804_);
v___x_807_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_801_, v_val_802_, v_x_779_, v_x_780_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___y_796_ = v___x_808_;
goto v___jp_795_;
}
else
{
lean_object* v___x_810_; 
lean_dec(v_val_802_);
lean_dec(v_key_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_x_780_);
lean_ctor_set(v___x_804_, 0, v_x_779_);
v___x_810_ = v___x_804_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_x_779_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_x_780_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v___y_796_ = v___x_810_;
goto v___jp_795_;
}
}
}
}
case 1:
{
lean_object* v_node_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v_node_813_ = lean_ctor_get(v_v_792_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_v_792_);
if (v_isSharedCheck_823_ == 0)
{
v___x_815_ = v_v_792_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_node_813_);
lean_dec(v_v_792_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_817_ = lean_usize_shift_right(v_x_777_, v___x_782_);
v___x_818_ = lean_usize_add(v_x_778_, v___x_783_);
v___x_819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_813_, v___x_817_, v___x_818_, v_x_779_, v_x_780_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v___y_796_ = v___x_821_;
goto v___jp_795_;
}
}
}
default: 
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_x_779_);
lean_ctor_set(v___x_824_, 1, v_x_780_);
v___y_796_ = v___x_824_;
goto v___jp_795_;
}
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_array_fset(v_xs_x27_794_, v_j_786_, v___y_796_);
lean_dec(v_j_786_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_797_);
v___x_799_ = v___x_790_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v_ks_827_; lean_object* v_vs_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_848_; 
v_ks_827_ = lean_ctor_get(v_x_776_, 0);
v_vs_828_ = lean_ctor_get(v_x_776_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_848_ == 0)
{
v___x_830_ = v_x_776_;
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_vs_828_);
lean_inc(v_ks_827_);
lean_dec(v_x_776_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_ks_827_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_vs_828_);
v___x_833_ = v_reuseFailAlloc_847_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v_newNode_834_; uint8_t v___y_836_; size_t v___x_842_; uint8_t v___x_843_; 
v_newNode_834_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_833_, v_x_779_, v_x_780_);
v___x_842_ = ((size_t)7ULL);
v___x_843_ = lean_usize_dec_le(v___x_842_, v_x_778_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_834_);
v___x_845_ = lean_unsigned_to_nat(4u);
v___x_846_ = lean_nat_dec_lt(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
v___y_836_ = v___x_846_;
goto v___jp_835_;
}
else
{
v___y_836_ = v___x_843_;
goto v___jp_835_;
}
v___jp_835_:
{
if (v___y_836_ == 0)
{
lean_object* v_ks_837_; lean_object* v_vs_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_ks_837_ = lean_ctor_get(v_newNode_834_, 0);
lean_inc_ref(v_ks_837_);
v_vs_838_ = lean_ctor_get(v_newNode_834_, 1);
lean_inc_ref(v_vs_838_);
lean_dec_ref(v_newNode_834_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_778_, v_ks_837_, v_vs_838_, v___x_839_, v___x_840_);
lean_dec_ref(v_vs_838_);
lean_dec_ref(v_ks_837_);
return v___x_841_;
}
else
{
return v_newNode_834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_i_852_, lean_object* v_entries_853_){
_start:
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_array_get_size(v_keys_850_);
v___x_855_ = lean_nat_dec_lt(v_i_852_, v___x_854_);
if (v___x_855_ == 0)
{
lean_dec(v_i_852_);
return v_entries_853_;
}
else
{
lean_object* v_k_856_; lean_object* v_v_857_; uint64_t v___y_859_; 
v_k_856_ = lean_array_fget_borrowed(v_keys_850_, v_i_852_);
v_v_857_ = lean_array_fget_borrowed(v_vals_851_, v_i_852_);
if (lean_obj_tag(v_k_856_) == 0)
{
uint64_t v___x_870_; 
v___x_870_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_859_ = v___x_870_;
goto v___jp_858_;
}
else
{
uint64_t v_hash_871_; 
v_hash_871_ = lean_ctor_get_uint64(v_k_856_, sizeof(void*)*2);
v___y_859_ = v_hash_871_;
goto v___jp_858_;
}
v___jp_858_:
{
size_t v_h_860_; size_t v___x_861_; lean_object* v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v_h_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_h_860_ = lean_uint64_to_usize(v___y_859_);
v___x_861_ = ((size_t)5ULL);
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = ((size_t)1ULL);
v___x_864_ = lean_usize_sub(v_depth_849_, v___x_863_);
v___x_865_ = lean_usize_mul(v___x_861_, v___x_864_);
v_h_866_ = lean_usize_shift_right(v_h_860_, v___x_865_);
v___x_867_ = lean_nat_add(v_i_852_, v___x_862_);
lean_dec(v_i_852_);
lean_inc(v_v_857_);
lean_inc(v_k_856_);
v___x_868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_853_, v_h_866_, v_depth_849_, v_k_856_, v_v_857_);
v_i_852_ = v___x_867_;
v_entries_853_ = v___x_868_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_i_875_, lean_object* v_entries_876_){
_start:
{
size_t v_depth_boxed_877_; lean_object* v_res_878_; 
v_depth_boxed_877_ = lean_unbox_usize(v_depth_872_);
lean_dec(v_depth_872_);
v_res_878_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_877_, v_keys_873_, v_vals_874_, v_i_875_, v_entries_876_);
lean_dec_ref(v_vals_874_);
lean_dec_ref(v_keys_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_2810__boxed_884_; size_t v_x_2811__boxed_885_; lean_object* v_res_886_; 
v_x_2810__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_x_2811__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_res_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_879_, v_x_2810__boxed_884_, v_x_2811__boxed_885_, v_x_882_, v_x_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
uint64_t v___y_891_; 
if (lean_obj_tag(v_x_888_) == 0)
{
uint64_t v___x_895_; 
v___x_895_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_891_ = v___x_895_;
goto v___jp_890_;
}
else
{
uint64_t v_hash_896_; 
v_hash_896_ = lean_ctor_get_uint64(v_x_888_, sizeof(void*)*2);
v___y_891_ = v_hash_896_;
goto v___jp_890_;
}
v___jp_890_:
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_uint64_to_usize(v___y_891_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_887_, v___x_892_, v___x_893_, v_x_888_, v_x_889_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_897_, lean_object* v_d_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Lean_IR_Decl_name(v_d_898_);
v___x_900_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_897_, v___x_899_, v_d_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_929_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_932_, lean_object* v_as_933_, lean_object* v_lo_934_, lean_object* v_hi_935_, lean_object* v_w_936_, lean_object* v_hlo_937_, lean_object* v_hhi_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_932_, v_as_933_, v_lo_934_, v_hi_935_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_940_, lean_object* v_as_941_, lean_object* v_lo_942_, lean_object* v_hi_943_, lean_object* v_w_944_, lean_object* v_hlo_945_, lean_object* v_hhi_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_940_, v_as_941_, v_lo_942_, v_hi_943_, v_w_944_, v_hlo_945_, v_hhi_946_);
lean_dec(v_hi_943_);
lean_dec(v_n_940_);
return v_res_947_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_949_, v_x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_952_, v_x_953_, v_x_954_);
lean_dec(v_x_954_);
lean_dec_ref(v_x_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_958_, v_x_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_962_, lean_object* v_lo_963_, lean_object* v_hi_964_, lean_object* v_hhi_965_, lean_object* v_pivot_966_, lean_object* v_as_967_, lean_object* v_i_968_, lean_object* v_k_969_, lean_object* v_ilo_970_, lean_object* v_ik_971_, lean_object* v_w_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_964_, v_pivot_966_, v_as_967_, v_i_968_, v_k_969_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_974_, lean_object* v_lo_975_, lean_object* v_hi_976_, lean_object* v_hhi_977_, lean_object* v_pivot_978_, lean_object* v_as_979_, lean_object* v_i_980_, lean_object* v_k_981_, lean_object* v_ilo_982_, lean_object* v_ik_983_, lean_object* v_w_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_974_, v_lo_975_, v_hi_976_, v_hhi_977_, v_pivot_978_, v_as_979_, v_i_980_, v_k_981_, v_ilo_982_, v_ik_983_, v_w_984_);
lean_dec_ref(v_pivot_978_);
lean_dec(v_hi_976_);
lean_dec(v_lo_975_);
lean_dec(v_n_974_);
return v_res_985_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_986_, lean_object* v_x_987_, size_t v_x_988_, lean_object* v_x_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_987_, v_x_988_, v_x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
size_t v_x_3099__boxed_995_; uint8_t v_res_996_; lean_object* v_r_997_; 
v_x_3099__boxed_995_ = lean_unbox_usize(v_x_993_);
lean_dec(v_x_993_);
v_res_996_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_991_, v_x_992_, v_x_3099__boxed_995_, v_x_994_);
lean_dec(v_x_994_);
lean_dec_ref(v_x_992_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, size_t v_x_1000_, size_t v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_999_, v_x_1000_, v_x_1001_, v_x_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
size_t v_x_3110__boxed_1011_; size_t v_x_3111__boxed_1012_; lean_object* v_res_1013_; 
v_x_3110__boxed_1011_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_x_3111__boxed_1012_ = lean_unbox_usize(v_x_1008_);
lean_dec(v_x_1008_);
v_res_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_1005_, v_x_1006_, v_x_3110__boxed_1011_, v_x_3111__boxed_1012_, v_x_1009_, v_x_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_heq_1017_, lean_object* v_i_1018_, lean_object* v_k_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_1015_, v_i_1018_, v_k_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_keys_1022_, lean_object* v_vals_1023_, lean_object* v_heq_1024_, lean_object* v_i_1025_, lean_object* v_k_1026_){
_start:
{
uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_res_1027_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1021_, v_keys_1022_, v_vals_1023_, v_heq_1024_, v_i_1025_, v_k_1026_);
lean_dec(v_k_1026_);
lean_dec_ref(v_vals_1023_);
lean_dec_ref(v_keys_1022_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1029_, lean_object* v_n_1030_, lean_object* v_k_1031_, lean_object* v_v_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1030_, v_k_1031_, v_v_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1034_, size_t v_depth_1035_, lean_object* v_keys_1036_, lean_object* v_vals_1037_, lean_object* v_heq_1038_, lean_object* v_i_1039_, lean_object* v_entries_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1035_, v_keys_1036_, v_vals_1037_, v_i_1039_, v_entries_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1042_, lean_object* v_depth_1043_, lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_heq_1046_, lean_object* v_i_1047_, lean_object* v_entries_1048_){
_start:
{
size_t v_depth_boxed_1049_; lean_object* v_res_1050_; 
v_depth_boxed_1049_ = lean_unbox_usize(v_depth_1043_);
lean_dec(v_depth_1043_);
v_res_1050_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1042_, v_depth_boxed_1049_, v_keys_1044_, v_vals_1045_, v_heq_1046_, v_i_1047_, v_entries_1048_);
lean_dec_ref(v_vals_1045_);
lean_dec_ref(v_keys_1044_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1052_, v_x_1053_, v_x_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_array_get_size(v_irDecls_1057_);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_nat_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___y_1064_; uint8_t v___x_1068_; 
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_sub(v___x_1058_, v___x_1061_);
v___x_1068_ = lean_nat_dec_le(v___x_1059_, v___x_1062_);
if (v___x_1068_ == 0)
{
lean_inc(v___x_1062_);
v___y_1064_ = v___x_1062_;
goto v___jp_1063_;
}
else
{
v___y_1064_ = v___x_1059_;
goto v___jp_1063_;
}
v___jp_1063_:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_nat_dec_le(v___y_1064_, v___x_1062_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v___x_1062_);
lean_inc(v___y_1064_);
v___x_1066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1058_, v_irDecls_1057_, v___y_1064_, v___y_1064_);
lean_dec(v___y_1064_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1058_, v_irDecls_1057_, v___y_1064_, v___x_1062_);
lean_dec(v___x_1062_);
return v___x_1067_;
}
}
}
else
{
return v_irDecls_1057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1069_){
_start:
{
lean_inc_ref(v_initDecls_1069_);
return v_initDecls_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1070_);
lean_dec_ref(v_initDecls_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1072_){
_start:
{
lean_inc_ref(v_modPkg_1072_);
return v_modPkg_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1073_);
lean_dec_ref(v_modPkg_1073_);
return v_res_1074_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1078_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0));
v___x_1079_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1078_, v___x_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v_toEnvExtension_1085_; lean_object* v_name_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; lean_object* v_ext_1089_; lean_object* v_toEnvExtension_1090_; lean_object* v_name_1091_; lean_object* v_exportEntriesFn_1092_; lean_object* v_asyncMode_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_private_1100_; lean_object* v___x_1101_; lean_object* v_toEnvExtension_1102_; lean_object* v_name_1103_; lean_object* v_exportEntriesFn_1104_; lean_object* v_asyncMode_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_private_1109_; lean_object* v___x_1110_; lean_object* v_irDecls_1111_; lean_object* v_irEntries_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1084_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1085_ = lean_ctor_get(v___x_1084_, 0);
v_name_1086_ = lean_ctor_get(v___x_1084_, 1);
v_asyncMode_1087_ = lean_ctor_get(v_toEnvExtension_1085_, 2);
v___x_1088_ = l_Lean_regularInitAttr;
v_ext_1089_ = lean_ctor_get(v___x_1088_, 1);
v_toEnvExtension_1090_ = lean_ctor_get(v_ext_1089_, 0);
v_name_1091_ = lean_ctor_get(v_ext_1089_, 1);
v_exportEntriesFn_1092_ = lean_ctor_get(v_ext_1089_, 4);
v_asyncMode_1093_ = lean_ctor_get(v_toEnvExtension_1090_, 2);
v___x_1094_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1095_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
lean_inc_ref_n(v_env_1083_, 4);
v___x_1096_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1094_, v___x_1084_, v_env_1083_, v_asyncMode_1087_);
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1095_, v_ext_1089_, v_env_1083_, v_asyncMode_1093_, v___x_1097_);
lean_inc_ref(v_exportEntriesFn_1092_);
v___x_1099_ = lean_apply_2(v_exportEntriesFn_1092_, v_env_1083_, v___x_1098_);
v_private_1100_ = lean_ctor_get(v___x_1099_, 2);
lean_inc(v_private_1100_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1102_ = lean_ctor_get(v___x_1101_, 0);
v_name_1103_ = lean_ctor_get(v___x_1101_, 1);
v_exportEntriesFn_1104_ = lean_ctor_get(v___x_1101_, 4);
v_asyncMode_1105_ = lean_ctor_get(v_toEnvExtension_1102_, 2);
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1106_, v___x_1101_, v_env_1083_, v_asyncMode_1105_, v___x_1097_);
lean_inc_ref(v_exportEntriesFn_1104_);
v___x_1108_ = lean_apply_2(v_exportEntriesFn_1104_, v_env_1083_, v___x_1107_);
v_private_1109_ = lean_ctor_get(v___x_1108_, 2);
lean_inc(v_private_1109_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_irDecls_1111_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1110_, v___x_1096_);
v_irEntries_1112_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(v_irDecls_1111_);
lean_inc(v_name_1086_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_name_1086_);
lean_ctor_set(v___x_1113_, 1, v_irEntries_1112_);
lean_inc(v_name_1091_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_name_1091_);
lean_ctor_set(v___x_1114_, 1, v_private_1100_);
lean_inc(v_name_1103_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_name_1103_);
lean_ctor_set(v___x_1115_, 1, v_private_1109_);
v___x_1116_ = lean_unsigned_to_nat(3u);
v___x_1117_ = lean_mk_empty_array_with_capacity(v___x_1116_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1113_);
v___x_1119_ = lean_array_push(v___x_1118_, v___x_1114_);
v___x_1120_ = lean_array_push(v___x_1119_, v___x_1115_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1121_, lean_object* v_k_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_m_1127_; lean_object* v_a_1128_; uint8_t v___x_1129_; 
v___x_1125_ = lean_nat_add(v_x_1123_, v_x_1124_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v_m_1127_ = lean_nat_shiftr(v___x_1125_, v___x_1126_);
lean_dec(v___x_1125_);
v_a_1128_ = lean_array_fget_borrowed(v_as_1121_, v_m_1127_);
v___x_1129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1128_, v_k_1122_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; 
lean_dec(v_x_1124_);
v___x_1130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1122_, v_a_1128_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec(v_m_1127_);
lean_dec(v_x_1123_);
lean_inc(v_a_1128_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1128_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_nat_dec_eq(v_m_1127_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_nat_sub(v_m_1127_, v___x_1126_);
lean_dec(v_m_1127_);
v___x_1135_ = lean_nat_dec_lt(v___x_1134_, v_x_1123_);
if (v___x_1135_ == 0)
{
v_x_1124_ = v___x_1134_;
goto _start;
}
else
{
lean_object* v___x_1137_; 
lean_dec(v___x_1134_);
lean_dec(v_x_1123_);
v___x_1137_ = lean_box(0);
return v___x_1137_;
}
}
else
{
lean_object* v___x_1138_; 
lean_dec(v_m_1127_);
lean_dec(v_x_1123_);
v___x_1138_ = lean_box(0);
return v___x_1138_;
}
}
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
lean_dec(v_x_1123_);
v___x_1139_ = lean_nat_add(v_m_1127_, v___x_1126_);
lean_dec(v_m_1127_);
v___x_1140_ = lean_nat_dec_le(v___x_1139_, v_x_1124_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v___x_1139_);
lean_dec(v_x_1124_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
else
{
v_x_1123_ = v___x_1139_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1143_, lean_object* v_k_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1143_, v_k_1144_, v_x_1145_, v_x_1146_);
lean_dec_ref(v_k_1144_);
lean_dec_ref(v_as_1143_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_i_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_array_get_size(v_keys_1148_);
v___x_1153_ = lean_nat_dec_lt(v_i_1150_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_dec(v_i_1150_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v_k_x27_1155_; uint8_t v___x_1156_; 
v_k_x27_1155_ = lean_array_fget_borrowed(v_keys_1148_, v_i_1150_);
v___x_1156_ = lean_name_eq(v_k_1151_, v_k_x27_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_add(v_i_1150_, v___x_1157_);
lean_dec(v_i_1150_);
v_i_1150_ = v___x_1158_;
goto _start;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_array_fget_borrowed(v_vals_1149_, v_i_1150_);
lean_dec(v_i_1150_);
lean_inc(v___x_1160_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1162_, lean_object* v_vals_1163_, lean_object* v_i_1164_, lean_object* v_k_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1162_, v_vals_1163_, v_i_1164_, v_k_1165_);
lean_dec(v_k_1165_);
lean_dec_ref(v_vals_1163_);
lean_dec_ref(v_keys_1162_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1167_, size_t v_x_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1167_) == 0)
{
lean_object* v_es_1170_; lean_object* v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v_j_1175_; lean_object* v___x_1176_; 
v_es_1170_ = lean_ctor_get(v_x_1167_, 0);
v___x_1171_ = lean_box(2);
v___x_1172_ = ((size_t)5ULL);
v___x_1173_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_1174_ = lean_usize_land(v_x_1168_, v___x_1173_);
v_j_1175_ = lean_usize_to_nat(v___x_1174_);
v___x_1176_ = lean_array_get_borrowed(v___x_1171_, v_es_1170_, v_j_1175_);
lean_dec(v_j_1175_);
switch(lean_obj_tag(v___x_1176_))
{
case 0:
{
lean_object* v_key_1177_; lean_object* v_val_1178_; uint8_t v___x_1179_; 
v_key_1177_ = lean_ctor_get(v___x_1176_, 0);
v_val_1178_ = lean_ctor_get(v___x_1176_, 1);
v___x_1179_ = lean_name_eq(v_x_1169_, v_key_1177_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_box(0);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; 
lean_inc(v_val_1178_);
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_val_1178_);
return v___x_1181_;
}
}
case 1:
{
lean_object* v_node_1182_; size_t v___x_1183_; 
v_node_1182_ = lean_ctor_get(v___x_1176_, 0);
v___x_1183_ = lean_usize_shift_right(v_x_1168_, v___x_1172_);
v_x_1167_ = v_node_1182_;
v_x_1168_ = v___x_1183_;
goto _start;
}
default: 
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_box(0);
return v___x_1185_;
}
}
}
else
{
lean_object* v_ks_1186_; lean_object* v_vs_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_ks_1186_ = lean_ctor_get(v_x_1167_, 0);
v_vs_1187_ = lean_ctor_get(v_x_1167_, 1);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1186_, v_vs_1187_, v___x_1188_, v_x_1169_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
size_t v_x_416__boxed_1193_; lean_object* v_res_1194_; 
v_x_416__boxed_1193_ = lean_unbox_usize(v_x_1191_);
lean_dec(v_x_1191_);
v_res_1194_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1190_, v_x_416__boxed_1193_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec_ref(v_x_1190_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
uint64_t v___y_1198_; 
if (lean_obj_tag(v_x_1196_) == 0)
{
uint64_t v___x_1201_; 
v___x_1201_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_1198_ = v___x_1201_;
goto v___jp_1197_;
}
else
{
uint64_t v_hash_1202_; 
v_hash_1202_ = lean_ctor_get_uint64(v_x_1196_, sizeof(void*)*2);
v___y_1198_ = v_hash_1202_;
goto v___jp_1197_;
}
v___jp_1197_:
{
size_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_uint64_to_usize(v___y_1198_);
v___x_1200_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1195_, v___x_1199_, v_x_1196_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1203_, v_x_1204_);
lean_dec(v_x_1204_);
lean_dec_ref(v_x_1203_);
return v_res_1205_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1209_, lean_object* v_declName_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1221_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1213_ = l_Lean_IR_declMapExt;
v___x_1221_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1209_, v_declName_1210_);
if (lean_obj_tag(v___x_1221_) == 0)
{
goto v___jp_1214_;
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_val_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref(v___x_1221_);
v___x_1236_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1213_, v_env_1209_, v_val_1222_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_array_get_size(v___x_1236_);
v___x_1239_ = lean_nat_dec_lt(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec_ref(v___x_1236_);
goto v___jp_1223_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_sub(v___x_1238_, v___x_1240_);
v___x_1242_ = lean_nat_dec_le(v___x_1237_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v___x_1241_);
lean_dec_ref(v___x_1236_);
goto v___jp_1223_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_tmpDecl_1245_; lean_object* v___x_1246_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1244_ = lean_box(0);
lean_inc(v_declName_1210_);
v_tmpDecl_1245_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1245_, 0, v_declName_1210_);
lean_ctor_set(v_tmpDecl_1245_, 1, v___x_1243_);
lean_ctor_set(v_tmpDecl_1245_, 2, v___x_1244_);
lean_ctor_set(v_tmpDecl_1245_, 3, v___x_1211_);
v___x_1246_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1236_, v_tmpDecl_1245_, v___x_1237_, v___x_1241_);
lean_dec_ref(v_tmpDecl_1245_);
lean_dec_ref(v___x_1236_);
if (lean_obj_tag(v___x_1246_) == 0)
{
goto v___jp_1223_;
}
else
{
lean_dec(v_val_1222_);
lean_dec(v_declName_1210_);
lean_dec_ref(v_env_1209_);
return v___x_1246_;
}
}
}
v___jp_1223_:
{
uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1224_ = 0;
v___x_1225_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1212_, v___x_1213_, v_env_1209_, v_val_1222_, v___x_1224_);
lean_dec(v_val_1222_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_array_get_size(v___x_1225_);
v___x_1228_ = lean_nat_dec_lt(v___x_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_dec_ref(v___x_1225_);
goto v___jp_1214_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_sub(v___x_1227_, v___x_1229_);
v___x_1231_ = lean_nat_dec_le(v___x_1226_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v___x_1230_);
lean_dec_ref(v___x_1225_);
goto v___jp_1214_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_tmpDecl_1234_; lean_object* v___x_1235_; 
v___x_1232_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1233_ = lean_box(0);
lean_inc(v_declName_1210_);
v_tmpDecl_1234_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1234_, 0, v_declName_1210_);
lean_ctor_set(v_tmpDecl_1234_, 1, v___x_1232_);
lean_ctor_set(v_tmpDecl_1234_, 2, v___x_1233_);
lean_ctor_set(v_tmpDecl_1234_, 3, v___x_1211_);
v___x_1235_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1225_, v_tmpDecl_1234_, v___x_1226_, v___x_1230_);
lean_dec_ref(v_tmpDecl_1234_);
lean_dec_ref(v___x_1225_);
if (lean_obj_tag(v___x_1235_) == 0)
{
goto v___jp_1214_;
}
else
{
lean_dec(v_declName_1210_);
lean_dec_ref(v_env_1209_);
return v___x_1235_;
}
}
}
}
}
v___jp_1214_:
{
lean_object* v_toEnvExtension_1215_; lean_object* v_asyncMode_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_snd_1219_; lean_object* v___x_1220_; 
v_toEnvExtension_1215_ = lean_ctor_get(v___x_1213_, 0);
v_asyncMode_1216_ = lean_ctor_get(v_toEnvExtension_1215_, 2);
v___x_1217_ = lean_box(0);
v___x_1218_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1212_, v___x_1213_, v_env_1209_, v_asyncMode_1216_, v___x_1217_);
v_snd_1219_ = lean_ctor_get(v___x_1218_, 1);
lean_inc(v_snd_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1219_, v_declName_1210_);
lean_dec(v_declName_1210_);
lean_dec(v_snd_1219_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1248_, v_x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1251_, v_x_1252_, v_x_1253_);
lean_dec(v_x_1253_);
lean_dec_ref(v_x_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1255_, lean_object* v_k_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1255_, v_k_1256_, v_x_1257_, v_x_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1261_, lean_object* v_k_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1261_, v_k_1262_, v_x_1263_, v_x_1264_, v_x_1265_);
lean_dec_ref(v_k_1262_);
lean_dec_ref(v_as_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1267_, lean_object* v_x_1268_, size_t v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1268_, v_x_1269_, v_x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
size_t v_x_585__boxed_1276_; lean_object* v_res_1277_; 
v_x_585__boxed_1276_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_res_1277_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1272_, v_x_1273_, v_x_585__boxed_1276_, v_x_1275_);
lean_dec(v_x_1275_);
lean_dec_ref(v_x_1273_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1278_, lean_object* v_keys_1279_, lean_object* v_vals_1280_, lean_object* v_heq_1281_, lean_object* v_i_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1279_, v_vals_1280_, v_i_1282_, v_k_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1285_, lean_object* v_keys_1286_, lean_object* v_vals_1287_, lean_object* v_heq_1288_, lean_object* v_i_1289_, lean_object* v_k_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1285_, v_keys_1286_, v_vals_1287_, v_heq_1288_, v_i_1289_, v_k_1290_);
lean_dec(v_k_1290_);
lean_dec_ref(v_vals_1287_);
lean_dec_ref(v_keys_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1292_, lean_object* v_declName_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1295_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1292_, v_declName_1293_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v___x_1296_; lean_object* v_toEnvExtension_1297_; lean_object* v_asyncMode_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1296_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1297_ = lean_ctor_get(v___x_1296_, 0);
v_asyncMode_1298_ = lean_ctor_get(v_toEnvExtension_1297_, 2);
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1294_, v___x_1296_, v_env_1292_, v_asyncMode_1298_, v___x_1299_);
v___x_1301_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1300_, v_declName_1293_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1300_);
return v___x_1301_;
}
else
{
lean_object* v_val_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___y_1307_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_val_1302_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1302_);
lean_dec_ref(v___x_1295_);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1305_ = l_Lean_IR_declMapExt;
v___x_1320_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1304_, v___x_1305_, v_env_1292_, v_val_1302_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v___x_1320_);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref(v___x_1320_);
v___x_1324_ = lean_box(0);
v___y_1307_ = v___x_1324_;
goto v___jp_1306_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = lean_nat_sub(v___x_1322_, v___x_1325_);
v___x_1327_ = lean_nat_dec_le(v___x_1321_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec(v___x_1326_);
lean_dec_ref(v___x_1320_);
v___x_1328_ = lean_box(0);
v___y_1307_ = v___x_1328_;
goto v___jp_1306_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_tmpDecl_1331_; lean_object* v___x_1332_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1330_ = lean_box(0);
lean_inc(v_declName_1293_);
v_tmpDecl_1331_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1331_, 0, v_declName_1293_);
lean_ctor_set(v_tmpDecl_1331_, 1, v___x_1329_);
lean_ctor_set(v_tmpDecl_1331_, 2, v___x_1330_);
lean_ctor_set(v_tmpDecl_1331_, 3, v___x_1303_);
v___x_1332_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1320_, v_tmpDecl_1331_, v___x_1321_, v___x_1326_);
lean_dec_ref(v_tmpDecl_1331_);
lean_dec_ref(v___x_1320_);
if (lean_obj_tag(v___x_1332_) == 0)
{
v___y_1307_ = v___x_1332_;
goto v___jp_1306_;
}
else
{
lean_dec(v_val_1302_);
lean_dec(v_declName_1293_);
lean_dec_ref(v_env_1292_);
return v___x_1332_;
}
}
}
v___jp_1306_:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1308_ = 0;
v___x_1309_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1304_, v___x_1305_, v_env_1292_, v_val_1302_, v___x_1308_);
lean_dec(v_val_1302_);
lean_dec_ref(v_env_1292_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_array_get_size(v___x_1309_);
v___x_1312_ = lean_nat_dec_lt(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v___x_1309_);
lean_dec(v_declName_1293_);
return v___y_1307_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_nat_sub(v___x_1311_, v___x_1313_);
v___x_1315_ = lean_nat_dec_le(v___x_1310_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec(v___x_1314_);
lean_dec_ref(v___x_1309_);
lean_dec(v_declName_1293_);
return v___y_1307_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_tmpDecl_1318_; lean_object* v___x_1319_; 
lean_dec(v___y_1307_);
v___x_1316_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1317_ = lean_box(0);
v_tmpDecl_1318_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1318_, 0, v_declName_1293_);
lean_ctor_set(v_tmpDecl_1318_, 1, v___x_1316_);
lean_ctor_set(v_tmpDecl_1318_, 2, v___x_1317_);
lean_ctor_set(v_tmpDecl_1318_, 3, v___x_1303_);
v___x_1319_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1309_, v_tmpDecl_1318_, v___x_1310_, v___x_1314_);
lean_dec_ref(v_tmpDecl_1318_);
lean_dec_ref(v___x_1309_);
return v___x_1319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1333_, lean_object* v_declName_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v_boxed_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc(v_declName_1334_);
v_boxed_1336_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1334_);
v___x_1337_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1333_, v_declName_1334_);
lean_dec(v_declName_1334_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1338_; lean_object* v_toEnvExtension_1339_; lean_object* v_asyncMode_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1339_ = lean_ctor_get(v___x_1338_, 0);
v_asyncMode_1340_ = lean_ctor_get(v_toEnvExtension_1339_, 2);
v___x_1341_ = lean_box(0);
v___x_1342_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1335_, v___x_1338_, v_env_1333_, v_asyncMode_1340_, v___x_1341_);
v___x_1343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1342_, v_boxed_1336_);
lean_dec(v_boxed_1336_);
lean_dec(v___x_1342_);
return v___x_1343_;
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___y_1349_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_val_1344_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1344_);
lean_dec_ref(v___x_1337_);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1347_ = l_Lean_IR_declMapExt;
v___x_1362_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1346_, v___x_1347_, v_env_1333_, v_val_1344_);
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_array_get_size(v___x_1362_);
v___x_1365_ = lean_nat_dec_lt(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v___x_1362_);
v___x_1366_ = lean_box(0);
v___y_1349_ = v___x_1366_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_sub(v___x_1364_, v___x_1367_);
v___x_1369_ = lean_nat_dec_le(v___x_1363_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v___x_1368_);
lean_dec_ref(v___x_1362_);
v___x_1370_ = lean_box(0);
v___y_1349_ = v___x_1370_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_tmpDecl_1373_; lean_object* v___x_1374_; 
v___x_1371_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1372_ = lean_box(0);
lean_inc(v_boxed_1336_);
v_tmpDecl_1373_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1373_, 0, v_boxed_1336_);
lean_ctor_set(v_tmpDecl_1373_, 1, v___x_1371_);
lean_ctor_set(v_tmpDecl_1373_, 2, v___x_1372_);
lean_ctor_set(v_tmpDecl_1373_, 3, v___x_1345_);
v___x_1374_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1362_, v_tmpDecl_1373_, v___x_1363_, v___x_1368_);
lean_dec_ref(v_tmpDecl_1373_);
lean_dec_ref(v___x_1362_);
if (lean_obj_tag(v___x_1374_) == 0)
{
v___y_1349_ = v___x_1374_;
goto v___jp_1348_;
}
else
{
lean_dec(v_val_1344_);
lean_dec(v_boxed_1336_);
lean_dec_ref(v_env_1333_);
return v___x_1374_;
}
}
}
v___jp_1348_:
{
uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1350_ = 0;
v___x_1351_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1346_, v___x_1347_, v_env_1333_, v_val_1344_, v___x_1350_);
lean_dec(v_val_1344_);
lean_dec_ref(v_env_1333_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_array_get_size(v___x_1351_);
v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v___x_1351_);
lean_dec(v_boxed_1336_);
return v___y_1349_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_sub(v___x_1353_, v___x_1355_);
v___x_1357_ = lean_nat_dec_le(v___x_1352_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v___x_1356_);
lean_dec_ref(v___x_1351_);
lean_dec(v_boxed_1336_);
return v___y_1349_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_tmpDecl_1360_; lean_object* v___x_1361_; 
lean_dec(v___y_1349_);
v___x_1358_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1359_ = lean_box(0);
v_tmpDecl_1360_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1360_, 0, v_boxed_1336_);
lean_ctor_set(v_tmpDecl_1360_, 1, v___x_1358_);
lean_ctor_set(v_tmpDecl_1360_, 2, v___x_1359_);
lean_ctor_set(v_tmpDecl_1360_, 3, v___x_1345_);
v___x_1361_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1351_, v_tmpDecl_1360_, v___x_1352_, v___x_1356_);
lean_dec_ref(v_tmpDecl_1360_);
lean_dec_ref(v___x_1351_);
return v___x_1361_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1375_, lean_object* v_constName_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1375_, v_constName_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; lean_object* v_toEnvExtension_1379_; lean_object* v_asyncMode_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1378_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1379_ = lean_ctor_get(v___x_1378_, 0);
v_asyncMode_1380_ = lean_ctor_get(v_toEnvExtension_1379_, 2);
v___x_1381_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1381_, v___x_1378_, v_env_1375_, v_asyncMode_1380_, v___x_1382_);
v___x_1384_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1383_, v_constName_1376_);
lean_dec(v_constName_1376_);
lean_dec(v___x_1383_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; 
v___x_1385_ = 1;
return v___x_1385_;
}
else
{
uint8_t v___x_1386_; 
v___x_1386_ = 0;
return v___x_1386_;
}
}
else
{
uint8_t v___x_1387_; 
lean_dec_ref(v___x_1377_);
lean_dec(v_constName_1376_);
lean_dec_ref(v_env_1375_);
v___x_1387_ = 0;
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1388_, lean_object* v_constName_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = lean_has_compile_error(v_env_1388_, v_constName_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; lean_object* v_env_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1395_ = lean_st_ref_get(v_a_1393_);
v_env_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc_ref(v_env_1396_);
lean_dec(v___x_1395_);
v___x_1397_ = l_Lean_IR_findEnvDecl(v_env_1396_, v_n_1392_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_IR_findDecl___redArg(v_n_1399_, v_a_1400_);
lean_dec(v_a_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_IR_findDecl___redArg(v_n_1403_, v_a_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_IR_findDecl(v_n_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1431_; 
v___x_1416_ = l_Lean_IR_findDecl___redArg(v_n_1413_, v_a_1414_);
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
if (lean_obj_tag(v_a_1417_) == 0)
{
uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = 0;
v___x_1422_ = lean_box(v___x_1421_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1422_);
v___x_1424_ = v___x_1419_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_dec_ref(v_a_1417_);
v___x_1426_ = 1;
v___x_1427_ = lean_box(v___x_1426_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1427_);
v___x_1429_ = v___x_1419_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_IR_containsDecl___redArg(v_n_1432_, v_a_1433_);
lean_dec(v_a_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_IR_containsDecl___redArg(v_n_1436_, v_a_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_IR_containsDecl(v_n_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_ref_1450_; lean_object* v___x_1451_; lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1460_; 
v_ref_1450_ = lean_ctor_get(v___y_1447_, 5);
v___x_1451_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1446_, v___y_1447_, v___y_1448_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_inc(v_ref_1450_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_ref_1450_);
lean_ctor_set(v___x_1456_, 1, v_a_1452_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 1);
lean_ctor_set(v___x_1454_, 0, v___x_1456_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1490_; 
lean_inc(v_n_1468_);
v___x_1472_ = l_Lean_IR_findDecl___redArg(v_n_1468_, v_a_1470_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1490_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1490_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
if (lean_obj_tag(v_a_1473_) == 1)
{
lean_object* v_val_1477_; lean_object* v___x_1479_; 
lean_dec(v_n_1468_);
v_val_1477_ = lean_ctor_get(v_a_1473_, 0);
lean_inc(v_val_1477_);
lean_dec_ref(v_a_1473_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_val_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_val_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_del_object(v___x_1475_);
lean_dec(v_a_1473_);
v___x_1481_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1482_ = 1;
v___x_1483_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1468_, v___x_1482_);
v___x_1484_ = lean_string_append(v___x_1481_, v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1486_ = lean_string_append(v___x_1484_, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
v___x_1488_ = l_Lean_MessageData_ofFormat(v___x_1487_);
v___x_1489_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1488_, v_a_1469_, v_a_1470_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_IR_getDecl(v_n_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1496_, lean_object* v_msg_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1497_, v___y_1498_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1502_, v_msg_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v_env_1512_; lean_object* v___x_1513_; lean_object* v_toEnvExtension_1514_; lean_object* v_asyncMode_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1511_ = lean_st_ref_get(v_a_1509_);
v_env_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_env_1512_);
lean_dec(v___x_1511_);
v___x_1513_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1514_ = lean_ctor_get(v___x_1513_, 0);
v_asyncMode_1515_ = lean_ctor_get(v_toEnvExtension_1514_, 2);
v___x_1516_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1517_ = lean_box(0);
v___x_1518_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1516_, v___x_1513_, v_env_1512_, v_asyncMode_1515_, v___x_1517_);
v___x_1519_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1518_, v_n_1508_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_IR_findLocalDecl___redArg(v_n_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec(v_n_1521_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_IR_findLocalDecl___redArg(v_n_1525_, v_a_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_IR_findLocalDecl(v_n_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_n_1530_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v_toEnvExtension_1537_; lean_object* v_asyncMode_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1536_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1537_ = lean_ctor_get(v___x_1536_, 0);
v_asyncMode_1538_ = lean_ctor_get(v_toEnvExtension_1537_, 2);
v___x_1539_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1540_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1539_, v___x_1536_, v_env_1535_, v_asyncMode_1538_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v_env_1550_; lean_object* v_nextMacroScope_1551_; lean_object* v_ngen_1552_; lean_object* v_auxDeclNGen_1553_; lean_object* v_traceState_1554_; lean_object* v_messages_1555_; lean_object* v_infoState_1556_; lean_object* v_snapshotTasks_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1573_; 
v___x_1549_ = lean_st_ref_take(v_a_1547_);
v_env_1550_ = lean_ctor_get(v___x_1549_, 0);
v_nextMacroScope_1551_ = lean_ctor_get(v___x_1549_, 1);
v_ngen_1552_ = lean_ctor_get(v___x_1549_, 2);
v_auxDeclNGen_1553_ = lean_ctor_get(v___x_1549_, 3);
v_traceState_1554_ = lean_ctor_get(v___x_1549_, 4);
v_messages_1555_ = lean_ctor_get(v___x_1549_, 6);
v_infoState_1556_ = lean_ctor_get(v___x_1549_, 7);
v_snapshotTasks_1557_ = lean_ctor_get(v___x_1549_, 8);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1549_, 5);
lean_dec(v_unused_1574_);
v___x_1559_ = v___x_1549_;
v_isShared_1560_ = v_isSharedCheck_1573_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snapshotTasks_1557_);
lean_inc(v_infoState_1556_);
lean_inc(v_messages_1555_);
lean_inc(v_traceState_1554_);
lean_inc(v_auxDeclNGen_1553_);
lean_inc(v_ngen_1552_);
lean_inc(v_nextMacroScope_1551_);
lean_inc(v_env_1550_);
lean_dec(v___x_1549_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1573_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v_toEnvExtension_1562_; lean_object* v_asyncMode_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1561_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1562_ = lean_ctor_get(v___x_1561_, 0);
v_asyncMode_1563_ = lean_ctor_get(v_toEnvExtension_1562_, 2);
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1561_, v_env_1550_, v_decl_1546_, v_asyncMode_1563_, v___x_1564_);
v___x_1566_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 5, v___x_1566_);
lean_ctor_set(v___x_1559_, 0, v___x_1565_);
v___x_1568_ = v___x_1559_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_nextMacroScope_1551_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_ngen_1552_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_auxDeclNGen_1553_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_traceState_1554_);
lean_ctor_set(v_reuseFailAlloc_1572_, 5, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1572_, 6, v_messages_1555_);
lean_ctor_set(v_reuseFailAlloc_1572_, 7, v_infoState_1556_);
lean_ctor_set(v_reuseFailAlloc_1572_, 8, v_snapshotTasks_1557_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_st_ref_set(v_a_1547_, v___x_1568_);
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_IR_addDecl___redArg(v_decl_1575_, v_a_1576_);
lean_dec(v_a_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_IR_addDecl___redArg(v_decl_1579_, v_a_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_IR_addDecl(v_decl_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1589_, size_t v_i_1590_, size_t v_stop_1591_, lean_object* v_b_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_usize_dec_eq(v_i_1590_, v_stop_1591_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_array_uget_borrowed(v_as_1589_, v_i_1590_);
lean_inc(v___x_1596_);
v___x_1597_ = l_Lean_IR_addDecl___redArg(v___x_1596_, v___y_1593_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; size_t v___x_1599_; size_t v___x_1600_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = ((size_t)1ULL);
v___x_1600_ = lean_usize_add(v_i_1590_, v___x_1599_);
v_i_1590_ = v___x_1600_;
v_b_1592_ = v_a_1598_;
goto _start;
}
else
{
return v___x_1597_;
}
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_b_1592_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1603_, lean_object* v_i_1604_, lean_object* v_stop_1605_, lean_object* v_b_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_i_boxed_1609_; size_t v_stop_boxed_1610_; lean_object* v_res_1611_; 
v_i_boxed_1609_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_stop_boxed_1610_ = lean_unbox_usize(v_stop_1605_);
lean_dec(v_stop_1605_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1603_, v_i_boxed_1609_, v_stop_boxed_1610_, v_b_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v_as_1603_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_array_get_size(v_decls_1612_);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_nat_dec_lt(v___x_1616_, v___x_1617_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
return v___x_1620_;
}
else
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_nat_dec_le(v___x_1617_, v___x_1617_);
if (v___x_1621_ == 0)
{
if (v___x_1619_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1618_);
return v___x_1622_;
}
else
{
size_t v___x_1623_; size_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = lean_usize_of_nat(v___x_1617_);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1612_, v___x_1623_, v___x_1624_, v___x_1618_, v_a_1614_);
return v___x_1625_;
}
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1617_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1612_, v___x_1626_, v___x_1627_, v___x_1618_, v_a_1614_);
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_IR_addDecls(v_decls_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec_ref(v_decls_1629_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1634_, size_t v_i_1635_, size_t v_stop_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1634_, v_i_1635_, v_stop_1636_, v_b_1637_, v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1642_, lean_object* v_i_1643_, lean_object* v_stop_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
size_t v_i_boxed_1649_; size_t v_stop_boxed_1650_; lean_object* v_res_1651_; 
v_i_boxed_1649_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_stop_boxed_1650_ = lean_unbox_usize(v_stop_1644_);
lean_dec(v_stop_1644_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1642_, v_i_boxed_1649_, v_stop_boxed_1650_, v_b_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v_as_1642_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1655_, lean_object* v_as_1656_, size_t v_sz_1657_, size_t v_i_1658_, lean_object* v_b_1659_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_usize_dec_lt(v_i_1658_, v_sz_1657_);
if (v___x_1660_ == 0)
{
lean_inc_ref(v_b_1659_);
return v_b_1659_;
}
else
{
lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1661_ = lean_box(0);
v_a_1662_ = lean_array_uget_borrowed(v_as_1656_, v_i_1658_);
v___x_1663_ = l_Lean_IR_Decl_name(v_a_1662_);
v___x_1664_ = lean_name_eq(v___x_1663_, v_n_1655_);
lean_dec(v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; size_t v___x_1666_; size_t v___x_1667_; 
v___x_1665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1666_ = ((size_t)1ULL);
v___x_1667_ = lean_usize_add(v_i_1658_, v___x_1666_);
v_i_1658_ = v___x_1667_;
v_b_1659_ = v___x_1665_;
goto _start;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_inc(v_a_1662_);
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_a_1662_);
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1661_);
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1672_, lean_object* v_as_1673_, lean_object* v_sz_1674_, lean_object* v_i_1675_, lean_object* v_b_1676_){
_start:
{
size_t v_sz_boxed_1677_; size_t v_i_boxed_1678_; lean_object* v_res_1679_; 
v_sz_boxed_1677_ = lean_unbox_usize(v_sz_1674_);
lean_dec(v_sz_1674_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1675_);
lean_dec(v_i_1675_);
v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1672_, v_as_1673_, v_sz_boxed_1677_, v_i_boxed_1678_, v_b_1676_);
lean_dec_ref(v_b_1676_);
lean_dec_ref(v_as_1673_);
lean_dec(v_n_1672_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1680_, lean_object* v_n_1681_, lean_object* v_decls_1682_){
_start:
{
lean_object* v___x_1683_; size_t v_sz_1684_; size_t v___x_1685_; lean_object* v___x_1686_; lean_object* v_fst_1687_; 
v___x_1683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1684_ = lean_array_size(v_decls_1682_);
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1681_, v_decls_1682_, v_sz_1684_, v___x_1685_, v___x_1683_);
v_fst_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_fst_1687_);
lean_dec_ref(v___x_1686_);
if (lean_obj_tag(v_fst_1687_) == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_IR_findEnvDecl(v_env_1680_, v_n_1681_);
return v___x_1688_;
}
else
{
lean_object* v_val_1689_; 
v_val_1689_ = lean_ctor_get(v_fst_1687_, 0);
lean_inc(v_val_1689_);
lean_dec_ref(v_fst_1687_);
if (lean_obj_tag(v_val_1689_) == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_IR_findEnvDecl(v_env_1680_, v_n_1681_);
return v___x_1690_;
}
else
{
lean_dec(v_n_1681_);
lean_dec_ref(v_env_1680_);
return v_val_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1691_, lean_object* v_n_1692_, lean_object* v_decls_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_IR_findEnvDecl_x27(v_env_1691_, v_n_1692_, v_decls_1693_);
lean_dec_ref(v_decls_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1695_, lean_object* v_decls_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; lean_object* v_env_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1699_ = lean_st_ref_get(v_a_1697_);
v_env_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc_ref(v_env_1700_);
lean_dec(v___x_1699_);
v___x_1701_ = l_Lean_IR_findEnvDecl_x27(v_env_1700_, v_n_1695_, v_decls_1696_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1703_, lean_object* v_decls_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_IR_findDecl_x27___redArg(v_n_1703_, v_decls_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_decls_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1708_, lean_object* v_decls_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_IR_findDecl_x27___redArg(v_n_1708_, v_decls_1709_, v_a_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1714_, lean_object* v_decls_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_IR_findDecl_x27(v_n_1714_, v_decls_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec_ref(v_decls_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1720_, lean_object* v_as_1721_, size_t v_i_1722_, size_t v_stop_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_eq(v_i_1722_, v_stop_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1725_ = lean_array_uget_borrowed(v_as_1721_, v_i_1722_);
v___x_1726_ = l_Lean_IR_Decl_name(v___x_1725_);
v___x_1727_ = lean_name_eq(v___x_1726_, v_n_1720_);
lean_dec(v___x_1726_);
if (v___x_1727_ == 0)
{
size_t v___x_1728_; size_t v___x_1729_; 
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1722_, v___x_1728_);
v_i_1722_ = v___x_1729_;
goto _start;
}
else
{
return v___x_1727_;
}
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = 0;
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1732_, lean_object* v_as_1733_, lean_object* v_i_1734_, lean_object* v_stop_1735_){
_start:
{
size_t v_i_boxed_1736_; size_t v_stop_boxed_1737_; uint8_t v_res_1738_; lean_object* v_r_1739_; 
v_i_boxed_1736_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_stop_boxed_1737_ = lean_unbox_usize(v_stop_1735_);
lean_dec(v_stop_1735_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1732_, v_as_1733_, v_i_boxed_1736_, v_stop_boxed_1737_);
lean_dec_ref(v_as_1733_);
lean_dec(v_n_1732_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1740_, lean_object* v_decls_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_array_get_size(v_decls_1741_);
v___x_1746_ = lean_nat_dec_lt(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_IR_containsDecl___redArg(v_n_1740_, v_a_1742_);
return v___x_1747_;
}
else
{
if (v___x_1746_ == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_IR_containsDecl___redArg(v_n_1740_, v_a_1742_);
return v___x_1748_;
}
else
{
size_t v___x_1749_; size_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = ((size_t)0ULL);
v___x_1750_ = lean_usize_of_nat(v___x_1745_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1740_, v_decls_1741_, v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_IR_containsDecl___redArg(v_n_1740_, v_a_1742_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_n_1740_);
v___x_1753_ = lean_box(v___x_1751_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1755_, lean_object* v_decls_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1755_, v_decls_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_decls_1756_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1760_, lean_object* v_decls_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1760_, v_decls_1761_, v_a_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1766_, lean_object* v_decls_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_IR_containsDecl_x27(v_n_1766_, v_decls_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec_ref(v_decls_1767_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1772_, lean_object* v_decls_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1795_; 
lean_inc(v_n_1772_);
v___x_1777_ = l_Lean_IR_findDecl_x27___redArg(v_n_1772_, v_decls_1773_, v_a_1775_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1795_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1795_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
if (lean_obj_tag(v_a_1778_) == 1)
{
lean_object* v_val_1782_; lean_object* v___x_1784_; 
lean_dec(v_n_1772_);
v_val_1782_ = lean_ctor_get(v_a_1778_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_val_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_val_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_del_object(v___x_1780_);
lean_dec(v_a_1778_);
v___x_1786_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1787_ = 1;
v___x_1788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1772_, v___x_1787_);
v___x_1789_ = lean_string_append(v___x_1786_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
v___x_1793_ = l_Lean_MessageData_ofFormat(v___x_1792_);
v___x_1794_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1793_, v_a_1774_, v_a_1775_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1796_, lean_object* v_decls_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_IR_getDecl_x27(v_n_1796_, v_decls_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec_ref(v_decls_1797_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1802_, lean_object* v_declName_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_IR_findEnvDecl(v_env_1802_, v_declName_1803_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; 
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref(v___x_1804_);
if (lean_obj_tag(v_val_1805_) == 0)
{
lean_object* v_info_1806_; 
v_info_1806_ = lean_ctor_get(v_val_1805_, 4);
lean_inc(v_info_1806_);
lean_dec_ref(v_val_1805_);
return v_info_1806_;
}
else
{
lean_object* v___x_1807_; 
lean_dec(v_val_1805_);
v___x_1807_ = lean_box(0);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1808_; 
lean_dec(v___x_1804_);
v___x_1808_ = lean_box(0);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1809_, uint8_t v_level_1810_, uint8_t v_includeDecls_1811_, lean_object* v_as_1812_, size_t v_i_1813_, size_t v_stop_1814_, lean_object* v_b_1815_){
_start:
{
lean_object* v___y_1817_; uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_eq(v_i_1813_, v_stop_1814_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; uint8_t v___y_1824_; 
v___x_1822_ = lean_array_uget_borrowed(v_as_1812_, v_i_1813_);
if (v_includeDecls_1811_ == 0)
{
uint8_t v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = 1;
lean_inc(v___x_1822_);
lean_inc_ref(v_env_1809_);
v___x_1833_ = l_Lean_Environment_contains(v_env_1809_, v___x_1822_, v___x_1832_);
if (v___x_1833_ == 0)
{
goto v___jp_1828_;
}
else
{
v___y_1817_ = v_b_1815_;
goto v___jp_1816_;
}
}
else
{
goto v___jp_1828_;
}
v___jp_1823_:
{
if (v___y_1824_ == 0)
{
uint8_t v___x_1825_; 
lean_inc_ref(v_env_1809_);
v___x_1825_ = l_Lean_isDeclMeta(v_env_1809_, v___x_1822_);
if (v___x_1825_ == 0)
{
v___y_1817_ = v_b_1815_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1826_; 
lean_inc(v___x_1822_);
v___x_1826_ = lean_array_push(v_b_1815_, v___x_1822_);
v___y_1817_ = v___x_1826_;
goto v___jp_1816_;
}
}
else
{
lean_object* v___x_1827_; 
lean_inc(v___x_1822_);
v___x_1827_ = lean_array_push(v_b_1815_, v___x_1822_);
v___y_1817_ = v___x_1827_;
goto v___jp_1816_;
}
}
v___jp_1828_:
{
uint8_t v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = 2;
v___x_1830_ = l_Lean_instDecidableEqOLeanLevel(v_level_1810_, v___x_1829_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
lean_inc_ref(v_env_1809_);
v___x_1831_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1809_, v___x_1822_);
v___y_1824_ = v___x_1831_;
goto v___jp_1823_;
}
else
{
v___y_1824_ = v___x_1830_;
goto v___jp_1823_;
}
}
}
else
{
lean_dec_ref(v_env_1809_);
return v_b_1815_;
}
v___jp_1816_:
{
size_t v___x_1818_; size_t v___x_1819_; 
v___x_1818_ = ((size_t)1ULL);
v___x_1819_ = lean_usize_add(v_i_1813_, v___x_1818_);
v_i_1813_ = v___x_1819_;
v_b_1815_ = v___y_1817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1834_, lean_object* v_level_1835_, lean_object* v_includeDecls_1836_, lean_object* v_as_1837_, lean_object* v_i_1838_, lean_object* v_stop_1839_, lean_object* v_b_1840_){
_start:
{
uint8_t v_level_boxed_1841_; uint8_t v_includeDecls_boxed_1842_; size_t v_i_boxed_1843_; size_t v_stop_boxed_1844_; lean_object* v_res_1845_; 
v_level_boxed_1841_ = lean_unbox(v_level_1835_);
v_includeDecls_boxed_1842_ = lean_unbox(v_includeDecls_1836_);
v_i_boxed_1843_ = lean_unbox_usize(v_i_1838_);
lean_dec(v_i_1838_);
v_stop_boxed_1844_ = lean_unbox_usize(v_stop_1839_);
lean_dec(v_stop_1839_);
v_res_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1834_, v_level_boxed_1841_, v_includeDecls_boxed_1842_, v_as_1837_, v_i_boxed_1843_, v_stop_boxed_1844_, v_b_1840_);
lean_dec_ref(v_as_1837_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1846_, size_t v_i_1847_, lean_object* v_bs_1848_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_usize_dec_lt(v_i_1847_, v_sz_1846_);
if (v___x_1849_ == 0)
{
return v_bs_1848_;
}
else
{
lean_object* v_v_1850_; lean_object* v___x_1851_; lean_object* v_bs_x27_1852_; lean_object* v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v_v_1850_ = lean_array_uget(v_bs_1848_, v_i_1847_);
v___x_1851_ = lean_unsigned_to_nat(0u);
v_bs_x27_1852_ = lean_array_uset(v_bs_1848_, v_i_1847_, v___x_1851_);
v___x_1853_ = l_Lean_IR_Decl_name(v_v_1850_);
lean_dec(v_v_1850_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1847_, v___x_1854_);
v___x_1856_ = lean_array_uset(v_bs_x27_1852_, v_i_1847_, v___x_1853_);
v_i_1847_ = v___x_1855_;
v_bs_1848_ = v___x_1856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1858_, lean_object* v_i_1859_, lean_object* v_bs_1860_){
_start:
{
size_t v_sz_boxed_1861_; size_t v_i_boxed_1862_; lean_object* v_res_1863_; 
v_sz_boxed_1861_ = lean_unbox_usize(v_sz_1858_);
lean_dec(v_sz_1858_);
v_i_boxed_1862_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_res_1863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1861_, v_i_boxed_1862_, v_bs_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1866_, uint8_t v_level_1867_, uint8_t v_includeDecls_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v_toEnvExtension_1870_; lean_object* v_asyncMode_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; size_t v_sz_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1869_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1870_ = lean_ctor_get(v___x_1869_, 0);
v_asyncMode_1871_ = lean_ctor_get(v_toEnvExtension_1870_, 2);
v___x_1872_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc_ref(v_env_1866_);
v___x_1873_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1872_, v___x_1869_, v_env_1866_, v_asyncMode_1871_);
v___x_1874_ = lean_array_mk(v___x_1873_);
v_sz_1875_ = lean_array_size(v___x_1874_);
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1875_, v___x_1876_, v___x_1874_);
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_array_get_size(v___x_1877_);
v___x_1880_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1881_ = lean_nat_dec_lt(v___x_1878_, v___x_1879_);
if (v___x_1881_ == 0)
{
lean_dec_ref(v___x_1877_);
lean_dec_ref(v_env_1866_);
return v___x_1880_;
}
else
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_nat_dec_le(v___x_1879_, v___x_1879_);
if (v___x_1882_ == 0)
{
if (v___x_1881_ == 0)
{
lean_dec_ref(v___x_1877_);
lean_dec_ref(v_env_1866_);
return v___x_1880_;
}
else
{
size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_usize_of_nat(v___x_1879_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1866_, v_level_1867_, v_includeDecls_1868_, v___x_1877_, v___x_1876_, v___x_1883_, v___x_1880_);
lean_dec_ref(v___x_1877_);
return v___x_1884_;
}
}
else
{
size_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_usize_of_nat(v___x_1879_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1866_, v_level_1867_, v_includeDecls_1868_, v___x_1877_, v___x_1876_, v___x_1885_, v___x_1880_);
lean_dec_ref(v___x_1877_);
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1887_, lean_object* v_level_1888_, lean_object* v_includeDecls_1889_){
_start:
{
uint8_t v_level_boxed_1890_; uint8_t v_includeDecls_boxed_1891_; lean_object* v_res_1892_; 
v_level_boxed_1890_ = lean_unbox(v_level_1888_);
v_includeDecls_boxed_1891_ = lean_unbox(v_includeDecls_1889_);
v_res_1892_ = lean_get_ir_extra_const_names(v_env_1887_, v_level_boxed_1890_, v_includeDecls_boxed_1891_);
return v_res_1892_;
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
