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
lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_246_; 
v_ref_199_ = lean_ctor_get(v___y_196_, 5);
v___x_200_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_195_, v___y_196_, v___y_197_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_246_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_246_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_246_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v_traceState_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_cache_211_; lean_object* v_messages_212_; lean_object* v_infoState_213_; lean_object* v_snapshotTasks_214_; lean_object* v_newDecls_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_245_; 
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
v_newDecls_215_ = lean_ctor_get(v___x_205_, 9);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_245_ == 0)
{
v___x_217_ = v___x_205_;
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_newDecls_215_);
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
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint64_t v_tid_219_; lean_object* v_traces_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_244_; 
v_tid_219_ = lean_ctor_get_uint64(v_traceState_206_, sizeof(void*)*1);
v_traces_220_ = lean_ctor_get(v_traceState_206_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_traceState_206_);
if (v_isSharedCheck_244_ == 0)
{
v___x_222_ = v_traceState_206_;
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_traces_220_);
lean_dec(v_traceState_206_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; double v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_224_ = lean_box(0);
v___x_225_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_226_ = 0;
v___x_227_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_228_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_228_, 0, v_cls_194_);
lean_ctor_set(v___x_228_, 1, v___x_224_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
lean_ctor_set_float(v___x_228_, sizeof(void*)*3, v___x_225_);
lean_ctor_set_float(v___x_228_, sizeof(void*)*3 + 8, v___x_225_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*3 + 16, v___x_226_);
v___x_229_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_230_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v_a_201_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_inc(v_ref_199_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_ref_199_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_PersistentArray_push___redArg(v_traces_220_, v___x_231_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_232_);
v___x_234_ = v___x_222_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_232_);
lean_ctor_set_uint64(v_reuseFailAlloc_243_, sizeof(void*)*1, v_tid_219_);
v___x_234_ = v_reuseFailAlloc_243_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v___x_234_);
v___x_236_ = v___x_217_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_env_207_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_cache_211_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_messages_212_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v_infoState_213_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_snapshotTasks_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 9, v_newDecls_215_);
v___x_236_ = v_reuseFailAlloc_242_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_237_ = lean_st_ref_set(v___y_197_, v___x_236_);
v___x_238_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_238_);
v___x_240_ = v___x_203_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
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
lean_dec_ref(v___x_288_);
if (lean_obj_tag(v_val_289_) == 1)
{
uint8_t v_v_290_; 
v_v_290_ = lean_ctor_get_uint8(v_val_289_, 0);
lean_dec_ref(v_val_289_);
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
lean_dec_ref(v___x_285_);
if (lean_obj_tag(v_val_286_) == 1)
{
uint8_t v_v_287_; 
v_v_287_ = lean_ctor_get_uint8(v_val_286_, 0);
lean_dec_ref(v_val_286_);
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
lean_object* v_options_301_; uint8_t v___x_302_; 
v_options_301_ = lean_ctor_get(v_a_298_, 2);
v___x_302_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_301_, v_optName_295_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref(v_decls_297_);
lean_dec(v_cls_296_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_cls_296_);
lean_ctor_set(v___x_305_, 1, v_decls_297_);
v___x_306_ = l_Lean_IR_log(v___x_305_, v_a_298_, v_a_299_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_307_, lean_object* v_cls_308_, lean_object* v_decls_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_307_, v_cls_308_, v_decls_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_optName_307_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_314_, lean_object* v_decl_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_314_);
v___x_320_ = l_Lean_Name_append(v___x_319_, v_cls_314_);
v___x_321_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_320_, v_cls_314_, v_decl_315_, v_a_316_, v_a_317_);
lean_dec(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_322_, lean_object* v_decl_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_IR_logDecls(v_cls_322_, v_decl_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_328_, lean_object* v_optName_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_options_334_; uint8_t v___x_335_; 
v_options_334_ = lean_ctor_get(v_a_331_, 2);
v___x_335_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_334_, v_optName_329_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_a_330_);
lean_dec_ref(v_inst_328_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_apply_1(v_inst_328_, v_a_330_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = l_Lean_IR_log(v___x_339_, v_a_331_, v_a_332_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_341_, lean_object* v_optName_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_341_, v_optName_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_optName_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_optName_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_349_, v_optName_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_optName_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_356_, v_inst_357_, v_optName_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_optName_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_364_, lean_object* v_cls_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_371_ = l_Lean_Name_append(v___x_370_, v_cls_365_);
v___x_372_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_364_, v___x_371_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_373_, lean_object* v_cls_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_IR_logMessageIf___redArg(v_inst_373_, v_cls_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_380_, lean_object* v_inst_381_, lean_object* v_cls_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_388_ = l_Lean_Name_append(v___x_387_, v_cls_382_);
v___x_389_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_381_, v___x_388_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_390_, lean_object* v_inst_391_, lean_object* v_cls_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_IR_logMessageIf(v_00_u03b1_390_, v_inst_391_, v_cls_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_404_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_398_, v___x_403_, v_a_399_, v_a_400_, v_a_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_IR_logMessage___redArg(v_inst_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_411_, lean_object* v_inst_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_418_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_412_, v___x_417_, v_a_413_, v_a_414_, v_a_415_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_419_, lean_object* v_inst_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_IR_logMessage(v_00_u03b1_419_, v_inst_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_426_, lean_object* v_b_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_428_ = l_Lean_IR_Decl_name(v_a_426_);
v___x_429_ = l_Lean_IR_Decl_name(v_b_427_);
v___x_430_ = l_Lean_Name_quickLt(v___x_428_, v___x_429_);
lean_dec(v___x_429_);
lean_dec(v___x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_431_, v_b_432_);
lean_dec_ref(v_b_432_);
lean_dec_ref(v_a_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_array_get_size(v_decls_436_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___y_444_; uint8_t v___x_448_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_sub(v___x_437_, v___x_441_);
v___x_448_ = lean_nat_dec_le(v___x_438_, v___x_442_);
if (v___x_448_ == 0)
{
lean_inc(v___x_442_);
v___y_444_ = v___x_442_;
goto v___jp_443_;
}
else
{
v___y_444_ = v___x_438_;
goto v___jp_443_;
}
v___jp_443_:
{
uint8_t v___x_445_; 
v___x_445_ = lean_nat_dec_le(v___y_444_, v___x_442_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_dec(v___x_442_);
lean_inc(v___y_444_);
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_440_, v___x_437_, v_decls_436_, v___y_444_, v___y_444_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_444_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_440_, v___x_437_, v_decls_436_, v___y_444_, v___x_442_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_442_);
return v___x_447_;
}
}
}
else
{
return v_decls_436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_452_, lean_object* v_declName_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_array_get_size(v_decls_452_);
v___x_456_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v_declName_453_);
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_sub(v___x_455_, v___x_458_);
v___x_460_ = lean_nat_dec_le(v___x_454_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v___x_459_);
lean_dec(v_declName_453_);
v___x_461_ = lean_box(0);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_tmpDecl_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_463_ = lean_box(0);
v___x_464_ = lean_box(0);
v_tmpDecl_465_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_465_, 0, v_declName_453_);
lean_ctor_set(v_tmpDecl_465_, 1, v___x_462_);
lean_ctor_set(v_tmpDecl_465_, 2, v___x_463_);
lean_ctor_set(v_tmpDecl_465_, 3, v___x_464_);
v___x_466_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_467_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_468_ = l_Array_binSearchAux___redArg(v___x_466_, v___x_467_, v_decls_452_, v_tmpDecl_465_, v___x_454_, v___x_459_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_469_, lean_object* v_declName_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_469_, v_declName_470_);
lean_dec_ref(v_decls_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_472_, lean_object* v_pivot_473_, lean_object* v_as_474_, lean_object* v_i_475_, lean_object* v_k_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_lt(v_k_476_, v_hi_472_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_k_476_);
v___x_478_ = lean_array_fswap(v_as_474_, v_i_475_, v_hi_472_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_i_475_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_480_ = lean_array_fget_borrowed(v_as_474_, v_k_476_);
v___x_481_ = l_Lean_IR_Decl_name(v___x_480_);
v___x_482_ = l_Lean_IR_Decl_name(v_pivot_473_);
v___x_483_ = l_Lean_Name_quickLt(v___x_481_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_k_476_, v___x_484_);
lean_dec(v_k_476_);
v_k_476_ = v___x_485_;
goto _start;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_array_fswap(v_as_474_, v_i_475_, v_k_476_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_i_475_, v___x_488_);
lean_dec(v_i_475_);
v___x_490_ = lean_nat_add(v_k_476_, v___x_488_);
lean_dec(v_k_476_);
v_as_474_ = v___x_487_;
v_i_475_ = v___x_489_;
v_k_476_ = v___x_490_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_492_, lean_object* v_pivot_493_, lean_object* v_as_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_492_, v_pivot_493_, v_as_494_, v_i_495_, v_k_496_);
lean_dec_ref(v_pivot_493_);
lean_dec(v_hi_492_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = l_Lean_IR_Decl_name(v___y_498_);
v___x_501_ = l_Lean_IR_Decl_name(v___y_499_);
v___x_502_ = l_Lean_Name_quickLt(v___x_500_, v___x_501_);
lean_dec(v___x_501_);
lean_dec(v___x_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_503_, v___y_504_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v___y_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_507_, lean_object* v_as_508_, lean_object* v_lo_509_, lean_object* v_hi_510_){
_start:
{
lean_object* v___y_512_; uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_lt(v_lo_509_, v_hi_510_);
if (v___x_522_ == 0)
{
lean_dec(v_lo_509_);
return v_as_508_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_mid_525_; lean_object* v___y_527_; lean_object* v___y_533_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_523_ = lean_nat_add(v_lo_509_, v_hi_510_);
v___x_524_ = lean_unsigned_to_nat(1u);
v_mid_525_ = lean_nat_shiftr(v___x_523_, v___x_524_);
lean_dec(v___x_523_);
v___x_538_ = lean_array_fget_borrowed(v_as_508_, v_mid_525_);
v___x_539_ = lean_array_fget_borrowed(v_as_508_, v_lo_509_);
v___x_540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
v___y_533_ = v_as_508_;
goto v___jp_532_;
}
else
{
lean_object* v___x_541_; 
v___x_541_ = lean_array_fswap(v_as_508_, v_lo_509_, v_mid_525_);
v___y_533_ = v___x_541_;
goto v___jp_532_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_528_ = lean_array_fget_borrowed(v___y_527_, v_mid_525_);
v___x_529_ = lean_array_fget_borrowed(v___y_527_, v_hi_510_);
v___x_530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_mid_525_);
v___y_512_ = v___y_527_;
goto v___jp_511_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_array_fswap(v___y_527_, v_mid_525_, v_hi_510_);
lean_dec(v_mid_525_);
v___y_512_ = v___x_531_;
goto v___jp_511_;
}
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_array_fget_borrowed(v___y_533_, v_hi_510_);
v___x_535_ = lean_array_fget_borrowed(v___y_533_, v_lo_509_);
v___x_536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
v___y_527_ = v___y_533_;
goto v___jp_526_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_array_fswap(v___y_533_, v_lo_509_, v_hi_510_);
v___y_527_ = v___x_537_;
goto v___jp_526_;
}
}
}
v___jp_511_:
{
lean_object* v_pivot_513_; lean_object* v___x_514_; lean_object* v_fst_515_; lean_object* v_snd_516_; uint8_t v___x_517_; 
v_pivot_513_ = lean_array_fget(v___y_512_, v_hi_510_);
lean_inc_n(v_lo_509_, 2);
v___x_514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_510_, v_pivot_513_, v___y_512_, v_lo_509_, v_lo_509_);
lean_dec(v_pivot_513_);
v_fst_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_fst_515_);
v_snd_516_ = lean_ctor_get(v___x_514_, 1);
lean_inc(v_snd_516_);
lean_dec_ref(v___x_514_);
v___x_517_ = lean_nat_dec_le(v_hi_510_, v_fst_515_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_507_, v_snd_516_, v_lo_509_, v_fst_515_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_fst_515_, v___x_519_);
lean_dec(v_fst_515_);
v_as_508_ = v___x_518_;
v_lo_509_ = v___x_520_;
goto _start;
}
else
{
lean_dec(v_fst_515_);
lean_dec(v_lo_509_);
return v_snd_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_542_, lean_object* v_as_543_, lean_object* v_lo_544_, lean_object* v_hi_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_542_, v_as_543_, v_lo_544_, v_hi_545_);
lean_dec(v_hi_545_);
lean_dec(v_n_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_553_, lean_object* v_as_554_, size_t v_i_555_, size_t v_stop_556_, lean_object* v_b_557_){
_start:
{
lean_object* v___y_559_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_555_, v_stop_556_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___y_573_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_571_ = lean_array_uget_borrowed(v_as_554_, v_i_555_);
v___x_588_ = l_Lean_IR_Decl_name(v___x_571_);
lean_inc_ref(v_env_553_);
v___x_589_ = l_Lean_isDeclMeta(v_env_553_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
lean_inc_ref(v_env_553_);
v___x_590_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_553_, v___x_588_);
if (v___x_590_ == 0)
{
lean_dec(v___x_588_);
v___y_559_ = v_b_557_;
goto v___jp_558_;
}
else
{
uint8_t v___x_591_; 
v___x_591_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_588_);
if (v___x_591_ == 0)
{
lean_dec(v___x_588_);
v___y_573_ = v___x_591_;
goto v___jp_572_;
}
else
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = l_Lean_Name_getPrefix(v___x_588_);
lean_dec(v___x_588_);
lean_inc_ref(v_env_553_);
v___x_593_ = l_Lean_isExtern(v_env_553_, v___x_592_);
v___y_573_ = v___x_593_;
goto v___jp_572_;
}
}
}
else
{
lean_object* v___x_594_; 
lean_dec(v___x_588_);
lean_inc(v___x_571_);
v___x_594_ = lean_array_push(v_b_557_, v___x_571_);
v___y_559_ = v___x_594_;
goto v___jp_558_;
}
v___jp_572_:
{
if (v___y_573_ == 0)
{
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_f_574_; lean_object* v_xs_575_; lean_object* v_type_576_; lean_object* v___x_577_; 
v_f_574_ = lean_ctor_get(v___x_571_, 0);
v_xs_575_ = lean_ctor_get(v___x_571_, 1);
v_type_576_ = lean_ctor_get(v___x_571_, 2);
lean_inc(v_f_574_);
lean_inc_ref(v_env_553_);
v___x_577_ = lean_get_export_name_for(v_env_553_, v_f_574_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref(v___x_577_);
if (lean_obj_tag(v_val_578_) == 1)
{
lean_object* v_str_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_str_579_ = lean_ctor_get(v_val_578_, 1);
lean_inc_ref(v_str_579_);
lean_dec_ref(v_val_578_);
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_str_579_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_inc(v_type_576_);
lean_inc_ref(v_xs_575_);
lean_inc(v_f_574_);
v___x_584_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_584_, 0, v_f_574_);
lean_ctor_set(v___x_584_, 1, v_xs_575_);
lean_ctor_set(v___x_584_, 2, v_type_576_);
lean_ctor_set(v___x_584_, 3, v___x_583_);
v___x_585_ = lean_array_push(v_b_557_, v___x_584_);
v___y_559_ = v___x_585_;
goto v___jp_558_;
}
else
{
lean_dec(v_val_578_);
lean_inc(v_type_576_);
lean_inc_ref(v_xs_575_);
lean_inc(v_f_574_);
v___y_564_ = v_f_574_;
v___y_565_ = v_xs_575_;
v___y_566_ = v_type_576_;
goto v___jp_563_;
}
}
else
{
lean_dec(v___x_577_);
lean_inc(v_type_576_);
lean_inc_ref(v_xs_575_);
lean_inc(v_f_574_);
v___y_564_ = v_f_574_;
v___y_565_ = v_xs_575_;
v___y_566_ = v_type_576_;
goto v___jp_563_;
}
}
else
{
lean_object* v___x_586_; 
lean_inc(v___x_571_);
v___x_586_ = lean_array_push(v_b_557_, v___x_571_);
v___y_559_ = v___x_586_;
goto v___jp_558_;
}
}
else
{
lean_object* v___x_587_; 
lean_inc(v___x_571_);
v___x_587_ = lean_array_push(v_b_557_, v___x_571_);
v___y_559_ = v___x_587_;
goto v___jp_558_;
}
}
}
else
{
lean_dec_ref(v_env_553_);
return v_b_557_;
}
v___jp_558_:
{
size_t v___x_560_; size_t v___x_561_; 
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_555_, v___x_560_);
v_i_555_ = v___x_561_;
v_b_557_ = v___y_559_;
goto _start;
}
v___jp_563_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_568_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_568_, 0, v___y_564_);
lean_ctor_set(v___x_568_, 1, v___y_565_);
lean_ctor_set(v___x_568_, 2, v___y_566_);
lean_ctor_set(v___x_568_, 3, v___x_567_);
v___x_569_ = lean_array_push(v_b_557_, v___x_568_);
v___y_559_ = v___x_569_;
goto v___jp_558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_595_, lean_object* v_as_596_, lean_object* v_i_597_, lean_object* v_stop_598_, lean_object* v_b_599_){
_start:
{
size_t v_i_boxed_600_; size_t v_stop_boxed_601_; lean_object* v_res_602_; 
v_i_boxed_600_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_stop_boxed_601_ = lean_unbox_usize(v_stop_598_);
lean_dec(v_stop_598_);
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_595_, v_as_596_, v_i_boxed_600_, v_stop_boxed_601_, v_b_599_);
lean_dec_ref(v_as_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_605_, lean_object* v_as_606_, lean_object* v_start_607_, lean_object* v_stop_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_610_ = lean_nat_dec_lt(v_start_607_, v_stop_608_);
if (v___x_610_ == 0)
{
lean_dec_ref(v_env_605_);
return v___x_609_;
}
else
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_array_get_size(v_as_606_);
v___x_612_ = lean_nat_dec_le(v_stop_608_, v___x_611_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_lt(v_start_607_, v___x_611_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_env_605_);
return v___x_609_;
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_usize_of_nat(v_start_607_);
v___x_615_ = lean_usize_of_nat(v___x_611_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_605_, v_as_606_, v___x_614_, v___x_615_, v___x_609_);
return v___x_616_;
}
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_usize_of_nat(v_start_607_);
v___x_618_ = lean_usize_of_nat(v_stop_608_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_605_, v_as_606_, v___x_617_, v___x_618_, v___x_609_);
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_620_, lean_object* v_as_621_, lean_object* v_start_622_, lean_object* v_stop_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_620_, v_as_621_, v_start_622_, v_stop_623_);
lean_dec(v_stop_623_);
lean_dec(v_start_622_);
lean_dec_ref(v_as_621_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
return v_x_625_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; lean_object* v___x_629_; 
v_head_627_ = lean_ctor_get(v_x_626_, 0);
lean_inc(v_head_627_);
v_tail_628_ = lean_ctor_get(v_x_626_, 1);
lean_inc(v_tail_628_);
lean_dec_ref(v_x_626_);
v___x_629_ = lean_array_push(v_x_625_, v_head_627_);
v_x_625_ = v___x_629_;
v_x_626_ = v_tail_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_631_, lean_object* v_s_632_, lean_object* v_entries_633_){
_start:
{
lean_object* v___y_635_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_decls_645_; lean_object* v___x_646_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___x_651_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_645_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_644_, v_entries_633_);
v___x_646_ = lean_array_get_size(v_decls_645_);
v___x_651_ = lean_nat_dec_eq(v___x_646_, v___x_643_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___y_655_; uint8_t v___x_657_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_sub(v___x_646_, v___x_652_);
v___x_657_ = lean_nat_dec_le(v___x_643_, v___x_653_);
if (v___x_657_ == 0)
{
lean_inc(v___x_653_);
v___y_655_ = v___x_653_;
goto v___jp_654_;
}
else
{
v___y_655_ = v___x_643_;
goto v___jp_654_;
}
v___jp_654_:
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_le(v___y_655_, v___x_653_);
if (v___x_656_ == 0)
{
lean_dec(v___x_653_);
lean_inc(v___y_655_);
v___y_648_ = v___y_655_;
v___y_649_ = v___y_655_;
goto v___jp_647_;
}
else
{
v___y_648_ = v___y_655_;
v___y_649_ = v___x_653_;
goto v___jp_647_;
}
}
}
else
{
v___y_635_ = v_decls_645_;
goto v___jp_634_;
}
v___jp_634_:
{
lean_object* v___x_636_; uint8_t v_isModule_637_; 
v___x_636_ = l_Lean_Environment_header(v_env_631_);
v_isModule_637_ = lean_ctor_get_uint8(v___x_636_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_636_);
if (v_isModule_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v_env_631_);
lean_inc_ref_n(v___y_635_, 2);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___y_635_);
lean_ctor_set(v___x_638_, 1, v___y_635_);
lean_ctor_set(v___x_638_, 2, v___y_635_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_array_get_size(v___y_635_);
v___x_641_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_631_, v___y_635_, v___x_639_, v___x_640_);
lean_dec_ref(v___y_635_);
lean_inc_ref_n(v___x_641_, 2);
v___x_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
return v___x_642_;
}
}
v___jp_647_:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_646_, v_decls_645_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
v___y_635_ = v___x_650_;
goto v___jp_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_658_, lean_object* v_s_659_, lean_object* v_entries_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_658_, v_s_659_, v_entries_660_);
lean_dec_ref(v_s_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_array_mk(v_es_662_);
return v___x_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object* v_keys_664_, lean_object* v_i_665_, lean_object* v_k_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_array_get_size(v_keys_664_);
v___x_668_ = lean_nat_dec_lt(v_i_665_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_i_665_);
return v___x_668_;
}
else
{
lean_object* v_k_x27_669_; uint8_t v___x_670_; 
v_k_x27_669_ = lean_array_fget_borrowed(v_keys_664_, v_i_665_);
v___x_670_ = lean_name_eq(v_k_666_, v_k_x27_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_i_665_, v___x_671_);
lean_dec(v_i_665_);
v_i_665_ = v___x_672_;
goto _start;
}
else
{
lean_dec(v_i_665_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_674_, lean_object* v_i_675_, lean_object* v_k_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_674_, v_i_675_, v_k_676_);
lean_dec(v_k_676_);
lean_dec_ref(v_keys_674_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_679_; size_t v___x_680_; size_t v___x_681_; 
v___x_679_ = ((size_t)5ULL);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_shift_left(v___x_680_, v___x_679_);
return v___x_681_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; 
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_684_ = lean_usize_sub(v___x_683_, v___x_682_);
return v___x_684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_685_, size_t v_x_686_, lean_object* v_x_687_){
_start:
{
if (lean_obj_tag(v_x_685_) == 0)
{
lean_object* v_es_688_; lean_object* v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v_j_693_; lean_object* v___x_694_; 
v_es_688_ = lean_ctor_get(v_x_685_, 0);
v___x_689_ = lean_box(2);
v___x_690_ = ((size_t)5ULL);
v___x_691_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_692_ = lean_usize_land(v_x_686_, v___x_691_);
v_j_693_ = lean_usize_to_nat(v___x_692_);
v___x_694_ = lean_array_get_borrowed(v___x_689_, v_es_688_, v_j_693_);
lean_dec(v_j_693_);
switch(lean_obj_tag(v___x_694_))
{
case 0:
{
lean_object* v_key_695_; uint8_t v___x_696_; 
v_key_695_ = lean_ctor_get(v___x_694_, 0);
v___x_696_ = lean_name_eq(v_x_687_, v_key_695_);
return v___x_696_;
}
case 1:
{
lean_object* v_node_697_; size_t v___x_698_; 
v_node_697_ = lean_ctor_get(v___x_694_, 0);
v___x_698_ = lean_usize_shift_right(v_x_686_, v___x_690_);
v_x_685_ = v_node_697_;
v_x_686_ = v___x_698_;
goto _start;
}
default: 
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
}
}
else
{
lean_object* v_ks_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_ks_701_ = lean_ctor_get(v_x_685_, 0);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_701_, v___x_702_, v_x_687_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
size_t v_x_2626__boxed_707_; uint8_t v_res_708_; lean_object* v_r_709_; 
v_x_2626__boxed_707_ = lean_unbox_usize(v_x_705_);
lean_dec(v_x_705_);
v_res_708_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_704_, v_x_2626__boxed_707_, v_x_706_);
lean_dec(v_x_706_);
lean_dec_ref(v_x_704_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_710_; uint64_t v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1723u);
v___x_711_ = lean_uint64_of_nat(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
uint64_t v___y_715_; 
if (lean_obj_tag(v_x_713_) == 0)
{
uint64_t v___x_718_; 
v___x_718_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_715_ = v___x_718_;
goto v___jp_714_;
}
else
{
uint64_t v_hash_719_; 
v_hash_719_ = lean_ctor_get_uint64(v_x_713_, sizeof(void*)*2);
v___y_715_ = v_hash_719_;
goto v___jp_714_;
}
v___jp_714_:
{
size_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_uint64_to_usize(v___y_715_);
v___x_717_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_712_, v___x_716_, v_x_713_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_720_, v_x_721_);
lean_dec(v_x_721_);
lean_dec_ref(v_x_720_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_724_, lean_object* v_x2_725_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = l_Lean_IR_Decl_name(v_x2_725_);
v___x_727_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_724_, v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; 
v___x_728_ = 1;
return v___x_728_;
}
else
{
uint8_t v___x_729_; 
v___x_729_ = 0;
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_730_, lean_object* v_x2_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_730_, v_x2_731_);
lean_dec_ref(v_x2_731_);
lean_dec_ref(v_x1_730_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_734_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_739_);
lean_dec_ref(v_x_739_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_ks_745_; lean_object* v_vs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_770_; 
v_ks_745_ = lean_ctor_get(v_x_741_, 0);
v_vs_746_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_770_ == 0)
{
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_vs_746_);
lean_inc(v_ks_745_);
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_get_size(v_ks_745_);
v___x_751_ = lean_nat_dec_lt(v_x_742_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_x_742_);
v___x_752_ = lean_array_push(v_ks_745_, v_x_743_);
v___x_753_ = lean_array_push(v_vs_746_, v_x_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_753_);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_ks_745_, v_x_742_);
v___x_758_ = lean_name_eq(v_x_743_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; 
if (v_isShared_749_ == 0)
{
v___x_760_ = v___x_748_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_ks_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_vs_746_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_x_742_, v___x_761_);
lean_dec(v_x_742_);
v_x_741_ = v___x_760_;
v_x_742_ = v___x_762_;
goto _start;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = lean_array_fset(v_ks_745_, v_x_742_, v_x_743_);
v___x_766_ = lean_array_fset(v_vs_746_, v_x_742_, v_x_744_);
lean_dec(v_x_742_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_766_);
lean_ctor_set(v___x_748_, 0, v___x_765_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_771_, v___x_774_, v_k_772_, v_v_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_777_, size_t v_x_778_, size_t v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_es_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v_j_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_es_782_ = lean_ctor_get(v_x_777_, 0);
v___x_783_ = ((size_t)5ULL);
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_786_ = lean_usize_land(v_x_778_, v___x_785_);
v_j_787_ = lean_usize_to_nat(v___x_786_);
v___x_788_ = lean_array_get_size(v_es_782_);
v___x_789_ = lean_nat_dec_lt(v_j_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_j_787_);
lean_dec(v_x_781_);
lean_dec(v_x_780_);
return v_x_777_;
}
else
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_826_; 
lean_inc_ref(v_es_782_);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_x_777_, 0);
lean_dec(v_unused_827_);
v___x_791_ = v_x_777_;
v_isShared_792_ = v_isSharedCheck_826_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_x_777_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_826_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_v_793_; lean_object* v___x_794_; lean_object* v_xs_x27_795_; lean_object* v___y_797_; 
v_v_793_ = lean_array_fget(v_es_782_, v_j_787_);
v___x_794_ = lean_box(0);
v_xs_x27_795_ = lean_array_fset(v_es_782_, v_j_787_, v___x_794_);
switch(lean_obj_tag(v_v_793_))
{
case 0:
{
lean_object* v_key_802_; lean_object* v_val_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v_key_802_ = lean_ctor_get(v_v_793_, 0);
v_val_803_ = lean_ctor_get(v_v_793_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_v_793_);
if (v_isSharedCheck_813_ == 0)
{
v___x_805_ = v_v_793_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_val_803_);
lean_inc(v_key_802_);
lean_dec(v_v_793_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_name_eq(v_x_780_, v_key_802_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_del_object(v___x_805_);
v___x_808_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_802_, v_val_803_, v_x_780_, v_x_781_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___y_797_ = v___x_809_;
goto v___jp_796_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_val_803_);
lean_dec(v_key_802_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_x_781_);
lean_ctor_set(v___x_805_, 0, v_x_780_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_x_780_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_x_781_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_797_ = v___x_811_;
goto v___jp_796_;
}
}
}
}
case 1:
{
lean_object* v_node_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_824_; 
v_node_814_ = lean_ctor_get(v_v_793_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_v_793_);
if (v_isSharedCheck_824_ == 0)
{
v___x_816_ = v_v_793_;
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_node_814_);
lean_dec(v_v_793_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_818_ = lean_usize_shift_right(v_x_778_, v___x_783_);
v___x_819_ = lean_usize_add(v_x_779_, v___x_784_);
v___x_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_814_, v___x_818_, v___x_819_, v_x_780_, v_x_781_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v___y_797_ = v___x_822_;
goto v___jp_796_;
}
}
}
default: 
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_x_780_);
lean_ctor_set(v___x_825_, 1, v_x_781_);
v___y_797_ = v___x_825_;
goto v___jp_796_;
}
}
v___jp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_array_fset(v_xs_x27_795_, v_j_787_, v___y_797_);
lean_dec(v_j_787_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_798_);
v___x_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
else
{
lean_object* v_ks_828_; lean_object* v_vs_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_849_; 
v_ks_828_ = lean_ctor_get(v_x_777_, 0);
v_vs_829_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_849_ == 0)
{
v___x_831_ = v_x_777_;
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_vs_829_);
lean_inc(v_ks_828_);
lean_dec(v_x_777_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_ks_828_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_vs_829_);
v___x_834_ = v_reuseFailAlloc_848_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v_newNode_835_; uint8_t v___y_837_; size_t v___x_843_; uint8_t v___x_844_; 
v_newNode_835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_834_, v_x_780_, v_x_781_);
v___x_843_ = ((size_t)7ULL);
v___x_844_ = lean_usize_dec_le(v___x_843_, v_x_779_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_835_);
v___x_846_ = lean_unsigned_to_nat(4u);
v___x_847_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
lean_dec(v___x_845_);
v___y_837_ = v___x_847_;
goto v___jp_836_;
}
else
{
v___y_837_ = v___x_844_;
goto v___jp_836_;
}
v___jp_836_:
{
if (v___y_837_ == 0)
{
lean_object* v_ks_838_; lean_object* v_vs_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_ks_838_ = lean_ctor_get(v_newNode_835_, 0);
lean_inc_ref(v_ks_838_);
v_vs_839_ = lean_ctor_get(v_newNode_835_, 1);
lean_inc_ref(v_vs_839_);
lean_dec_ref(v_newNode_835_);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_779_, v_ks_838_, v_vs_839_, v___x_840_, v___x_841_);
lean_dec_ref(v_vs_839_);
lean_dec_ref(v_ks_838_);
return v___x_842_;
}
else
{
return v_newNode_835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t v_depth_850_, lean_object* v_keys_851_, lean_object* v_vals_852_, lean_object* v_i_853_, lean_object* v_entries_854_){
_start:
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = lean_array_get_size(v_keys_851_);
v___x_856_ = lean_nat_dec_lt(v_i_853_, v___x_855_);
if (v___x_856_ == 0)
{
lean_dec(v_i_853_);
return v_entries_854_;
}
else
{
lean_object* v_k_857_; lean_object* v_v_858_; uint64_t v___y_860_; 
v_k_857_ = lean_array_fget_borrowed(v_keys_851_, v_i_853_);
v_v_858_ = lean_array_fget_borrowed(v_vals_852_, v_i_853_);
if (lean_obj_tag(v_k_857_) == 0)
{
uint64_t v___x_871_; 
v___x_871_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_860_ = v___x_871_;
goto v___jp_859_;
}
else
{
uint64_t v_hash_872_; 
v_hash_872_ = lean_ctor_get_uint64(v_k_857_, sizeof(void*)*2);
v___y_860_ = v_hash_872_;
goto v___jp_859_;
}
v___jp_859_:
{
size_t v_h_861_; size_t v___x_862_; lean_object* v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v_h_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_h_861_ = lean_uint64_to_usize(v___y_860_);
v___x_862_ = ((size_t)5ULL);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_sub(v_depth_850_, v___x_864_);
v___x_866_ = lean_usize_mul(v___x_862_, v___x_865_);
v_h_867_ = lean_usize_shift_right(v_h_861_, v___x_866_);
v___x_868_ = lean_nat_add(v_i_853_, v___x_863_);
lean_dec(v_i_853_);
lean_inc(v_v_858_);
lean_inc(v_k_857_);
v___x_869_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_854_, v_h_867_, v_depth_850_, v_k_857_, v_v_858_);
v_i_853_ = v___x_868_;
v_entries_854_ = v___x_869_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_873_, lean_object* v_keys_874_, lean_object* v_vals_875_, lean_object* v_i_876_, lean_object* v_entries_877_){
_start:
{
size_t v_depth_boxed_878_; lean_object* v_res_879_; 
v_depth_boxed_878_ = lean_unbox_usize(v_depth_873_);
lean_dec(v_depth_873_);
v_res_879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_878_, v_keys_874_, v_vals_875_, v_i_876_, v_entries_877_);
lean_dec_ref(v_vals_875_);
lean_dec_ref(v_keys_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
size_t v_x_2810__boxed_885_; size_t v_x_2811__boxed_886_; lean_object* v_res_887_; 
v_x_2810__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_x_2811__boxed_886_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_res_887_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_880_, v_x_2810__boxed_885_, v_x_2811__boxed_886_, v_x_883_, v_x_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
uint64_t v___y_892_; 
if (lean_obj_tag(v_x_889_) == 0)
{
uint64_t v___x_896_; 
v___x_896_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_892_ = v___x_896_;
goto v___jp_891_;
}
else
{
uint64_t v_hash_897_; 
v_hash_897_ = lean_ctor_get_uint64(v_x_889_, sizeof(void*)*2);
v___y_892_ = v_hash_897_;
goto v___jp_891_;
}
v___jp_891_:
{
size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_uint64_to_usize(v___y_892_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_888_, v___x_893_, v___x_894_, v_x_889_, v_x_890_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_898_, lean_object* v_d_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = l_Lean_IR_Decl_name(v_d_899_);
v___x_901_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_898_, v___x_900_, v_d_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_930_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_933_, lean_object* v_as_934_, lean_object* v_lo_935_, lean_object* v_hi_936_, lean_object* v_w_937_, lean_object* v_hlo_938_, lean_object* v_hhi_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_933_, v_as_934_, v_lo_935_, v_hi_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_941_, lean_object* v_as_942_, lean_object* v_lo_943_, lean_object* v_hi_944_, lean_object* v_w_945_, lean_object* v_hlo_946_, lean_object* v_hhi_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_941_, v_as_942_, v_lo_943_, v_hi_944_, v_w_945_, v_hlo_946_, v_hhi_947_);
lean_dec(v_hi_944_);
lean_dec(v_n_941_);
return v_res_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_950_, v_x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_953_, v_x_954_, v_x_955_);
lean_dec(v_x_955_);
lean_dec_ref(v_x_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_959_, v_x_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_963_, lean_object* v_lo_964_, lean_object* v_hi_965_, lean_object* v_hhi_966_, lean_object* v_pivot_967_, lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_k_970_, lean_object* v_ilo_971_, lean_object* v_ik_972_, lean_object* v_w_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_965_, v_pivot_967_, v_as_968_, v_i_969_, v_k_970_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_975_, lean_object* v_lo_976_, lean_object* v_hi_977_, lean_object* v_hhi_978_, lean_object* v_pivot_979_, lean_object* v_as_980_, lean_object* v_i_981_, lean_object* v_k_982_, lean_object* v_ilo_983_, lean_object* v_ik_984_, lean_object* v_w_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_975_, v_lo_976_, v_hi_977_, v_hhi_978_, v_pivot_979_, v_as_980_, v_i_981_, v_k_982_, v_ilo_983_, v_ik_984_, v_w_985_);
lean_dec_ref(v_pivot_979_);
lean_dec(v_hi_977_);
lean_dec(v_lo_976_);
lean_dec(v_n_975_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, size_t v_x_989_, lean_object* v_x_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_988_, v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
size_t v_x_3099__boxed_996_; uint8_t v_res_997_; lean_object* v_r_998_; 
v_x_3099__boxed_996_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_997_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_992_, v_x_993_, v_x_3099__boxed_996_, v_x_995_);
lean_dec(v_x_995_);
lean_dec_ref(v_x_993_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_999_, lean_object* v_x_1000_, size_t v_x_1001_, size_t v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_1000_, v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
size_t v_x_3110__boxed_1012_; size_t v_x_3111__boxed_1013_; lean_object* v_res_1014_; 
v_x_3110__boxed_1012_ = lean_unbox_usize(v_x_1008_);
lean_dec(v_x_1008_);
v_x_3111__boxed_1013_ = lean_unbox_usize(v_x_1009_);
lean_dec(v_x_1009_);
v_res_1014_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_1006_, v_x_1007_, v_x_3110__boxed_1012_, v_x_3111__boxed_1013_, v_x_1010_, v_x_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1015_, lean_object* v_keys_1016_, lean_object* v_vals_1017_, lean_object* v_heq_1018_, lean_object* v_i_1019_, lean_object* v_k_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_1016_, v_i_1019_, v_k_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1022_, lean_object* v_keys_1023_, lean_object* v_vals_1024_, lean_object* v_heq_1025_, lean_object* v_i_1026_, lean_object* v_k_1027_){
_start:
{
uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_res_1028_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1022_, v_keys_1023_, v_vals_1024_, v_heq_1025_, v_i_1026_, v_k_1027_);
lean_dec(v_k_1027_);
lean_dec_ref(v_vals_1024_);
lean_dec_ref(v_keys_1023_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1030_, lean_object* v_n_1031_, lean_object* v_k_1032_, lean_object* v_v_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1031_, v_k_1032_, v_v_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1035_, size_t v_depth_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_entries_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1036_, v_keys_1037_, v_vals_1038_, v_i_1040_, v_entries_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1043_, lean_object* v_depth_1044_, lean_object* v_keys_1045_, lean_object* v_vals_1046_, lean_object* v_heq_1047_, lean_object* v_i_1048_, lean_object* v_entries_1049_){
_start:
{
size_t v_depth_boxed_1050_; lean_object* v_res_1051_; 
v_depth_boxed_1050_ = lean_unbox_usize(v_depth_1044_);
lean_dec(v_depth_1044_);
v_res_1051_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1043_, v_depth_boxed_1050_, v_keys_1045_, v_vals_1046_, v_heq_1047_, v_i_1048_, v_entries_1049_);
lean_dec_ref(v_vals_1046_);
lean_dec_ref(v_keys_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = lean_array_get_size(v_irDecls_1058_);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_nat_dec_eq(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; uint8_t v___x_1069_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_sub(v___x_1059_, v___x_1062_);
v___x_1069_ = lean_nat_dec_le(v___x_1060_, v___x_1063_);
if (v___x_1069_ == 0)
{
lean_inc(v___x_1063_);
v___y_1065_ = v___x_1063_;
goto v___jp_1064_;
}
else
{
v___y_1065_ = v___x_1060_;
goto v___jp_1064_;
}
v___jp_1064_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_le(v___y_1065_, v___x_1063_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_dec(v___x_1063_);
lean_inc(v___y_1065_);
v___x_1067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1059_, v_irDecls_1058_, v___y_1065_, v___y_1065_);
lean_dec(v___y_1065_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1059_, v_irDecls_1058_, v___y_1065_, v___x_1063_);
lean_dec(v___x_1063_);
return v___x_1068_;
}
}
}
else
{
return v_irDecls_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1070_){
_start:
{
lean_inc_ref(v_initDecls_1070_);
return v_initDecls_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1071_);
lean_dec_ref(v_initDecls_1071_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1073_){
_start:
{
lean_inc_ref(v_modPkg_1073_);
return v_modPkg_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1074_);
lean_dec_ref(v_modPkg_1074_);
return v_res_1075_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1079_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0));
v___x_1080_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1079_, v___x_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v_toEnvExtension_1086_; lean_object* v_name_1087_; lean_object* v_asyncMode_1088_; lean_object* v___x_1089_; lean_object* v_ext_1090_; lean_object* v_toEnvExtension_1091_; lean_object* v_name_1092_; lean_object* v_exportEntriesFn_1093_; lean_object* v_asyncMode_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_private_1101_; lean_object* v___x_1102_; lean_object* v_toEnvExtension_1103_; lean_object* v_name_1104_; lean_object* v_exportEntriesFn_1105_; lean_object* v_asyncMode_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_private_1110_; lean_object* v___x_1111_; lean_object* v_irDecls_1112_; lean_object* v_irEntries_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1085_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1086_ = lean_ctor_get(v___x_1085_, 0);
v_name_1087_ = lean_ctor_get(v___x_1085_, 1);
v_asyncMode_1088_ = lean_ctor_get(v_toEnvExtension_1086_, 2);
v___x_1089_ = l_Lean_regularInitAttr;
v_ext_1090_ = lean_ctor_get(v___x_1089_, 1);
v_toEnvExtension_1091_ = lean_ctor_get(v_ext_1090_, 0);
v_name_1092_ = lean_ctor_get(v_ext_1090_, 1);
v_exportEntriesFn_1093_ = lean_ctor_get(v_ext_1090_, 4);
v_asyncMode_1094_ = lean_ctor_get(v_toEnvExtension_1091_, 2);
v___x_1095_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1096_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
lean_inc_ref_n(v_env_1084_, 4);
v___x_1097_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1095_, v___x_1085_, v_env_1084_, v_asyncMode_1088_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1096_, v_ext_1090_, v_env_1084_, v_asyncMode_1094_, v___x_1098_);
lean_inc_ref(v_exportEntriesFn_1093_);
v___x_1100_ = lean_apply_2(v_exportEntriesFn_1093_, v_env_1084_, v___x_1099_);
v_private_1101_ = lean_ctor_get(v___x_1100_, 2);
lean_inc(v_private_1101_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1103_ = lean_ctor_get(v___x_1102_, 0);
v_name_1104_ = lean_ctor_get(v___x_1102_, 1);
v_exportEntriesFn_1105_ = lean_ctor_get(v___x_1102_, 4);
v_asyncMode_1106_ = lean_ctor_get(v_toEnvExtension_1103_, 2);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1107_, v___x_1102_, v_env_1084_, v_asyncMode_1106_, v___x_1098_);
lean_inc_ref(v_exportEntriesFn_1105_);
v___x_1109_ = lean_apply_2(v_exportEntriesFn_1105_, v_env_1084_, v___x_1108_);
v_private_1110_ = lean_ctor_get(v___x_1109_, 2);
lean_inc(v_private_1110_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_irDecls_1112_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1111_, v___x_1097_);
v_irEntries_1113_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(v_irDecls_1112_);
lean_inc(v_name_1087_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_name_1087_);
lean_ctor_set(v___x_1114_, 1, v_irEntries_1113_);
lean_inc(v_name_1092_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_name_1092_);
lean_ctor_set(v___x_1115_, 1, v_private_1101_);
lean_inc(v_name_1104_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_name_1104_);
lean_ctor_set(v___x_1116_, 1, v_private_1110_);
v___x_1117_ = lean_unsigned_to_nat(3u);
v___x_1118_ = lean_mk_empty_array_with_capacity(v___x_1117_);
v___x_1119_ = lean_array_push(v___x_1118_, v___x_1114_);
v___x_1120_ = lean_array_push(v___x_1119_, v___x_1115_);
v___x_1121_ = lean_array_push(v___x_1120_, v___x_1116_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1122_, lean_object* v_k_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_m_1128_; lean_object* v_a_1129_; uint8_t v___x_1130_; 
v___x_1126_ = lean_nat_add(v_x_1124_, v_x_1125_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v_m_1128_ = lean_nat_shiftr(v___x_1126_, v___x_1127_);
lean_dec(v___x_1126_);
v_a_1129_ = lean_array_fget_borrowed(v_as_1122_, v_m_1128_);
v___x_1130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1129_, v_k_1123_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; 
lean_dec(v_x_1125_);
v___x_1131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1123_, v_a_1129_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec(v_m_1128_);
lean_dec(v_x_1124_);
lean_inc(v_a_1129_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_a_1129_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_nat_dec_eq(v_m_1128_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_nat_sub(v_m_1128_, v___x_1127_);
lean_dec(v_m_1128_);
v___x_1136_ = lean_nat_dec_lt(v___x_1135_, v_x_1124_);
if (v___x_1136_ == 0)
{
v_x_1125_ = v___x_1135_;
goto _start;
}
else
{
lean_object* v___x_1138_; 
lean_dec(v___x_1135_);
lean_dec(v_x_1124_);
v___x_1138_ = lean_box(0);
return v___x_1138_;
}
}
else
{
lean_object* v___x_1139_; 
lean_dec(v_m_1128_);
lean_dec(v_x_1124_);
v___x_1139_ = lean_box(0);
return v___x_1139_;
}
}
}
else
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
lean_dec(v_x_1124_);
v___x_1140_ = lean_nat_add(v_m_1128_, v___x_1127_);
lean_dec(v_m_1128_);
v___x_1141_ = lean_nat_dec_le(v___x_1140_, v_x_1125_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec(v___x_1140_);
lean_dec(v_x_1125_);
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
else
{
v_x_1124_ = v___x_1140_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1144_, lean_object* v_k_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1144_, v_k_1145_, v_x_1146_, v_x_1147_);
lean_dec_ref(v_k_1145_);
lean_dec_ref(v_as_1144_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_i_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_array_get_size(v_keys_1149_);
v___x_1154_ = lean_nat_dec_lt(v_i_1151_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_dec(v_i_1151_);
v___x_1155_ = lean_box(0);
return v___x_1155_;
}
else
{
lean_object* v_k_x27_1156_; uint8_t v___x_1157_; 
v_k_x27_1156_ = lean_array_fget_borrowed(v_keys_1149_, v_i_1151_);
v___x_1157_ = lean_name_eq(v_k_1152_, v_k_x27_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_i_1151_, v___x_1158_);
lean_dec(v_i_1151_);
v_i_1151_ = v___x_1159_;
goto _start;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_array_fget_borrowed(v_vals_1150_, v_i_1151_);
lean_dec(v_i_1151_);
lean_inc(v___x_1161_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1163_, lean_object* v_vals_1164_, lean_object* v_i_1165_, lean_object* v_k_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1163_, v_vals_1164_, v_i_1165_, v_k_1166_);
lean_dec(v_k_1166_);
lean_dec_ref(v_vals_1164_);
lean_dec_ref(v_keys_1163_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1168_, size_t v_x_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_es_1171_; lean_object* v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v_j_1176_; lean_object* v___x_1177_; 
v_es_1171_ = lean_ctor_get(v_x_1168_, 0);
v___x_1172_ = lean_box(2);
v___x_1173_ = ((size_t)5ULL);
v___x_1174_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_1175_ = lean_usize_land(v_x_1169_, v___x_1174_);
v_j_1176_ = lean_usize_to_nat(v___x_1175_);
v___x_1177_ = lean_array_get_borrowed(v___x_1172_, v_es_1171_, v_j_1176_);
lean_dec(v_j_1176_);
switch(lean_obj_tag(v___x_1177_))
{
case 0:
{
lean_object* v_key_1178_; lean_object* v_val_1179_; uint8_t v___x_1180_; 
v_key_1178_ = lean_ctor_get(v___x_1177_, 0);
v_val_1179_ = lean_ctor_get(v___x_1177_, 1);
v___x_1180_ = lean_name_eq(v_x_1170_, v_key_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_box(0);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; 
lean_inc(v_val_1179_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_val_1179_);
return v___x_1182_;
}
}
case 1:
{
lean_object* v_node_1183_; size_t v___x_1184_; 
v_node_1183_ = lean_ctor_get(v___x_1177_, 0);
v___x_1184_ = lean_usize_shift_right(v_x_1169_, v___x_1173_);
v_x_1168_ = v_node_1183_;
v_x_1169_ = v___x_1184_;
goto _start;
}
default: 
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_box(0);
return v___x_1186_;
}
}
}
else
{
lean_object* v_ks_1187_; lean_object* v_vs_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_ks_1187_ = lean_ctor_get(v_x_1168_, 0);
v_vs_1188_ = lean_ctor_get(v_x_1168_, 1);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1187_, v_vs_1188_, v___x_1189_, v_x_1170_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
size_t v_x_416__boxed_1194_; lean_object* v_res_1195_; 
v_x_416__boxed_1194_ = lean_unbox_usize(v_x_1192_);
lean_dec(v_x_1192_);
v_res_1195_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1191_, v_x_416__boxed_1194_, v_x_1193_);
lean_dec(v_x_1193_);
lean_dec_ref(v_x_1191_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
uint64_t v___y_1199_; 
if (lean_obj_tag(v_x_1197_) == 0)
{
uint64_t v___x_1202_; 
v___x_1202_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_1199_ = v___x_1202_;
goto v___jp_1198_;
}
else
{
uint64_t v_hash_1203_; 
v_hash_1203_ = lean_ctor_get_uint64(v_x_1197_, sizeof(void*)*2);
v___y_1199_ = v_hash_1203_;
goto v___jp_1198_;
}
v___jp_1198_:
{
size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_uint64_to_usize(v___y_1199_);
v___x_1201_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1196_, v___x_1200_, v_x_1197_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1204_, v_x_1205_);
lean_dec(v_x_1205_);
lean_dec_ref(v_x_1204_);
return v_res_1206_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1210_, lean_object* v_declName_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1222_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1214_ = l_Lean_IR_declMapExt;
v___x_1222_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1210_, v_declName_1211_);
if (lean_obj_tag(v___x_1222_) == 0)
{
goto v___jp_1215_;
}
else
{
lean_object* v_val_1223_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_val_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1223_);
lean_dec_ref(v___x_1222_);
v___x_1237_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1213_, v___x_1214_, v_env_1210_, v_val_1223_);
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_array_get_size(v___x_1237_);
v___x_1240_ = lean_nat_dec_lt(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v___x_1237_);
goto v___jp_1224_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v___x_1239_, v___x_1241_);
v___x_1243_ = lean_nat_dec_le(v___x_1238_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v___x_1242_);
lean_dec_ref(v___x_1237_);
goto v___jp_1224_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_tmpDecl_1246_; lean_object* v___x_1247_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1245_ = lean_box(0);
lean_inc(v_declName_1211_);
v_tmpDecl_1246_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1246_, 0, v_declName_1211_);
lean_ctor_set(v_tmpDecl_1246_, 1, v___x_1244_);
lean_ctor_set(v_tmpDecl_1246_, 2, v___x_1245_);
lean_ctor_set(v_tmpDecl_1246_, 3, v___x_1212_);
v___x_1247_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1237_, v_tmpDecl_1246_, v___x_1238_, v___x_1242_);
lean_dec_ref(v_tmpDecl_1246_);
lean_dec_ref(v___x_1237_);
if (lean_obj_tag(v___x_1247_) == 0)
{
goto v___jp_1224_;
}
else
{
lean_dec(v_val_1223_);
lean_dec(v_declName_1211_);
lean_dec_ref(v_env_1210_);
return v___x_1247_;
}
}
}
v___jp_1224_:
{
uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1225_ = 0;
v___x_1226_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1213_, v___x_1214_, v_env_1210_, v_val_1223_, v___x_1225_);
lean_dec(v_val_1223_);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_array_get_size(v___x_1226_);
v___x_1229_ = lean_nat_dec_lt(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec_ref(v___x_1226_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_sub(v___x_1228_, v___x_1230_);
v___x_1232_ = lean_nat_dec_le(v___x_1227_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v___x_1231_);
lean_dec_ref(v___x_1226_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_tmpDecl_1235_; lean_object* v___x_1236_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1234_ = lean_box(0);
lean_inc(v_declName_1211_);
v_tmpDecl_1235_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1235_, 0, v_declName_1211_);
lean_ctor_set(v_tmpDecl_1235_, 1, v___x_1233_);
lean_ctor_set(v_tmpDecl_1235_, 2, v___x_1234_);
lean_ctor_set(v_tmpDecl_1235_, 3, v___x_1212_);
v___x_1236_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1226_, v_tmpDecl_1235_, v___x_1227_, v___x_1231_);
lean_dec_ref(v_tmpDecl_1235_);
lean_dec_ref(v___x_1226_);
if (lean_obj_tag(v___x_1236_) == 0)
{
goto v___jp_1215_;
}
else
{
lean_dec(v_declName_1211_);
lean_dec_ref(v_env_1210_);
return v___x_1236_;
}
}
}
}
}
v___jp_1215_:
{
lean_object* v_toEnvExtension_1216_; lean_object* v_asyncMode_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_snd_1220_; lean_object* v___x_1221_; 
v_toEnvExtension_1216_ = lean_ctor_get(v___x_1214_, 0);
v_asyncMode_1217_ = lean_ctor_get(v_toEnvExtension_1216_, 2);
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1213_, v___x_1214_, v_env_1210_, v_asyncMode_1217_, v___x_1218_);
v_snd_1220_ = lean_ctor_get(v___x_1219_, 1);
lean_inc(v_snd_1220_);
lean_dec(v___x_1219_);
v___x_1221_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1220_, v_declName_1211_);
lean_dec(v_declName_1211_);
lean_dec(v_snd_1220_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1249_, v_x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1252_, v_x_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_x_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1256_, lean_object* v_k_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1256_, v_k_1257_, v_x_1258_, v_x_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1262_, lean_object* v_k_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1262_, v_k_1263_, v_x_1264_, v_x_1265_, v_x_1266_);
lean_dec_ref(v_k_1263_);
lean_dec_ref(v_as_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, size_t v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1269_, v_x_1270_, v_x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
size_t v_x_585__boxed_1277_; lean_object* v_res_1278_; 
v_x_585__boxed_1277_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_res_1278_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1273_, v_x_1274_, v_x_585__boxed_1277_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec_ref(v_x_1274_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1279_, lean_object* v_keys_1280_, lean_object* v_vals_1281_, lean_object* v_heq_1282_, lean_object* v_i_1283_, lean_object* v_k_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1280_, v_vals_1281_, v_i_1283_, v_k_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1286_, lean_object* v_keys_1287_, lean_object* v_vals_1288_, lean_object* v_heq_1289_, lean_object* v_i_1290_, lean_object* v_k_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1286_, v_keys_1287_, v_vals_1288_, v_heq_1289_, v_i_1290_, v_k_1291_);
lean_dec(v_k_1291_);
lean_dec_ref(v_vals_1288_);
lean_dec_ref(v_keys_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1293_, lean_object* v_declName_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1296_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1293_, v_declName_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1297_; lean_object* v_toEnvExtension_1298_; lean_object* v_asyncMode_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1297_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1298_ = lean_ctor_get(v___x_1297_, 0);
v_asyncMode_1299_ = lean_ctor_get(v_toEnvExtension_1298_, 2);
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1295_, v___x_1297_, v_env_1293_, v_asyncMode_1299_, v___x_1300_);
v___x_1302_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1301_, v_declName_1294_);
lean_dec(v_declName_1294_);
lean_dec(v___x_1301_);
return v___x_1302_;
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___y_1308_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_val_1303_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1303_);
lean_dec_ref(v___x_1296_);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1306_ = l_Lean_IR_declMapExt;
v___x_1321_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1305_, v___x_1306_, v_env_1293_, v_val_1303_);
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_array_get_size(v___x_1321_);
v___x_1324_ = lean_nat_dec_lt(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref(v___x_1321_);
v___x_1325_ = lean_box(0);
v___y_1308_ = v___x_1325_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = lean_nat_sub(v___x_1323_, v___x_1326_);
v___x_1328_ = lean_nat_dec_le(v___x_1322_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v___x_1327_);
lean_dec_ref(v___x_1321_);
v___x_1329_ = lean_box(0);
v___y_1308_ = v___x_1329_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_tmpDecl_1332_; lean_object* v___x_1333_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1331_ = lean_box(0);
lean_inc(v_declName_1294_);
v_tmpDecl_1332_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1332_, 0, v_declName_1294_);
lean_ctor_set(v_tmpDecl_1332_, 1, v___x_1330_);
lean_ctor_set(v_tmpDecl_1332_, 2, v___x_1331_);
lean_ctor_set(v_tmpDecl_1332_, 3, v___x_1304_);
v___x_1333_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1321_, v_tmpDecl_1332_, v___x_1322_, v___x_1327_);
lean_dec_ref(v_tmpDecl_1332_);
lean_dec_ref(v___x_1321_);
if (lean_obj_tag(v___x_1333_) == 0)
{
v___y_1308_ = v___x_1333_;
goto v___jp_1307_;
}
else
{
lean_dec(v_val_1303_);
lean_dec(v_declName_1294_);
lean_dec_ref(v_env_1293_);
return v___x_1333_;
}
}
}
v___jp_1307_:
{
uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1309_ = 0;
v___x_1310_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1305_, v___x_1306_, v_env_1293_, v_val_1303_, v___x_1309_);
lean_dec(v_val_1303_);
lean_dec_ref(v_env_1293_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v___x_1310_);
v___x_1313_ = lean_nat_dec_lt(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec_ref(v___x_1310_);
lean_dec(v_declName_1294_);
return v___y_1308_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = lean_nat_sub(v___x_1312_, v___x_1314_);
v___x_1316_ = lean_nat_dec_le(v___x_1311_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec(v___x_1315_);
lean_dec_ref(v___x_1310_);
lean_dec(v_declName_1294_);
return v___y_1308_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_tmpDecl_1319_; lean_object* v___x_1320_; 
lean_dec(v___y_1308_);
v___x_1317_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1318_ = lean_box(0);
v_tmpDecl_1319_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1319_, 0, v_declName_1294_);
lean_ctor_set(v_tmpDecl_1319_, 1, v___x_1317_);
lean_ctor_set(v_tmpDecl_1319_, 2, v___x_1318_);
lean_ctor_set(v_tmpDecl_1319_, 3, v___x_1304_);
v___x_1320_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1310_, v_tmpDecl_1319_, v___x_1311_, v___x_1315_);
lean_dec_ref(v_tmpDecl_1319_);
lean_dec_ref(v___x_1310_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1334_, lean_object* v_declName_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v_boxed_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc(v_declName_1335_);
v_boxed_1337_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1335_);
v___x_1338_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1334_, v_declName_1335_);
lean_dec(v_declName_1335_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; lean_object* v_toEnvExtension_1340_; lean_object* v_asyncMode_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1339_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1340_ = lean_ctor_get(v___x_1339_, 0);
v_asyncMode_1341_ = lean_ctor_get(v_toEnvExtension_1340_, 2);
v___x_1342_ = lean_box(0);
v___x_1343_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1336_, v___x_1339_, v_env_1334_, v_asyncMode_1341_, v___x_1342_);
v___x_1344_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1343_, v_boxed_1337_);
lean_dec(v_boxed_1337_);
lean_dec(v___x_1343_);
return v___x_1344_;
}
else
{
lean_object* v_val_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___y_1350_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_val_1345_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_val_1345_);
lean_dec_ref(v___x_1338_);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1348_ = l_Lean_IR_declMapExt;
v___x_1363_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1347_, v___x_1348_, v_env_1334_, v_val_1345_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_array_get_size(v___x_1363_);
v___x_1366_ = lean_nat_dec_lt(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref(v___x_1363_);
v___x_1367_ = lean_box(0);
v___y_1350_ = v___x_1367_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_sub(v___x_1365_, v___x_1368_);
v___x_1370_ = lean_nat_dec_le(v___x_1364_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v___x_1369_);
lean_dec_ref(v___x_1363_);
v___x_1371_ = lean_box(0);
v___y_1350_ = v___x_1371_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_tmpDecl_1374_; lean_object* v___x_1375_; 
v___x_1372_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1373_ = lean_box(0);
lean_inc(v_boxed_1337_);
v_tmpDecl_1374_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1374_, 0, v_boxed_1337_);
lean_ctor_set(v_tmpDecl_1374_, 1, v___x_1372_);
lean_ctor_set(v_tmpDecl_1374_, 2, v___x_1373_);
lean_ctor_set(v_tmpDecl_1374_, 3, v___x_1346_);
v___x_1375_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1363_, v_tmpDecl_1374_, v___x_1364_, v___x_1369_);
lean_dec_ref(v_tmpDecl_1374_);
lean_dec_ref(v___x_1363_);
if (lean_obj_tag(v___x_1375_) == 0)
{
v___y_1350_ = v___x_1375_;
goto v___jp_1349_;
}
else
{
lean_dec(v_val_1345_);
lean_dec(v_boxed_1337_);
lean_dec_ref(v_env_1334_);
return v___x_1375_;
}
}
}
v___jp_1349_:
{
uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1351_ = 0;
v___x_1352_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1347_, v___x_1348_, v_env_1334_, v_val_1345_, v___x_1351_);
lean_dec(v_val_1345_);
lean_dec_ref(v_env_1334_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_array_get_size(v___x_1352_);
v___x_1355_ = lean_nat_dec_lt(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v___x_1352_);
lean_dec(v_boxed_1337_);
return v___y_1350_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_sub(v___x_1354_, v___x_1356_);
v___x_1358_ = lean_nat_dec_le(v___x_1353_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec(v___x_1357_);
lean_dec_ref(v___x_1352_);
lean_dec(v_boxed_1337_);
return v___y_1350_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_tmpDecl_1361_; lean_object* v___x_1362_; 
lean_dec(v___y_1350_);
v___x_1359_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1360_ = lean_box(0);
v_tmpDecl_1361_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1361_, 0, v_boxed_1337_);
lean_ctor_set(v_tmpDecl_1361_, 1, v___x_1359_);
lean_ctor_set(v_tmpDecl_1361_, 2, v___x_1360_);
lean_ctor_set(v_tmpDecl_1361_, 3, v___x_1346_);
v___x_1362_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1352_, v_tmpDecl_1361_, v___x_1353_, v___x_1357_);
lean_dec_ref(v_tmpDecl_1361_);
lean_dec_ref(v___x_1352_);
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1376_, lean_object* v_constName_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1376_, v_constName_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; lean_object* v_toEnvExtension_1380_; lean_object* v_asyncMode_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1379_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1380_ = lean_ctor_get(v___x_1379_, 0);
v_asyncMode_1381_ = lean_ctor_get(v_toEnvExtension_1380_, 2);
v___x_1382_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1382_, v___x_1379_, v_env_1376_, v_asyncMode_1381_, v___x_1383_);
v___x_1385_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1384_, v_constName_1377_);
lean_dec(v_constName_1377_);
lean_dec(v___x_1384_);
if (v___x_1385_ == 0)
{
uint8_t v___x_1386_; 
v___x_1386_ = 1;
return v___x_1386_;
}
else
{
uint8_t v___x_1387_; 
v___x_1387_ = 0;
return v___x_1387_;
}
}
else
{
uint8_t v___x_1388_; 
lean_dec_ref(v___x_1378_);
lean_dec(v_constName_1377_);
lean_dec_ref(v_env_1376_);
v___x_1388_ = 0;
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1389_, lean_object* v_constName_1390_){
_start:
{
uint8_t v_res_1391_; lean_object* v_r_1392_; 
v_res_1391_ = lean_has_compile_error(v_env_1389_, v_constName_1390_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v_env_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_st_ref_get(v_a_1394_);
v_env_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_env_1397_);
lean_dec(v___x_1396_);
v___x_1398_ = l_Lean_IR_findEnvDecl(v_env_1397_, v_n_1393_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_IR_findDecl___redArg(v_n_1400_, v_a_1401_);
lean_dec(v_a_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_IR_findDecl___redArg(v_n_1404_, v_a_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_IR_findDecl(v_n_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1432_; 
v___x_1417_ = l_Lean_IR_findDecl___redArg(v_n_1414_, v_a_1415_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1432_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1432_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
if (lean_obj_tag(v_a_1418_) == 0)
{
uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1422_ = 0;
v___x_1423_ = lean_box(v___x_1422_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1423_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec_ref(v_a_1418_);
v___x_1427_ = 1;
v___x_1428_ = lean_box(v___x_1427_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1428_);
v___x_1430_ = v___x_1420_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_IR_containsDecl___redArg(v_n_1433_, v_a_1434_);
lean_dec(v_a_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_IR_containsDecl___redArg(v_n_1437_, v_a_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_IR_containsDecl(v_n_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_ref_1451_; lean_object* v___x_1452_; lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1461_; 
v_ref_1451_ = lean_ctor_get(v___y_1448_, 5);
v___x_1452_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1447_, v___y_1448_, v___y_1449_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_inc(v_ref_1451_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_ref_1451_);
lean_ctor_set(v___x_1457_, 1, v_a_1453_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 1);
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1491_; 
lean_inc(v_n_1469_);
v___x_1473_ = l_Lean_IR_findDecl___redArg(v_n_1469_, v_a_1471_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1491_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1491_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
if (lean_obj_tag(v_a_1474_) == 1)
{
lean_object* v_val_1478_; lean_object* v___x_1480_; 
lean_dec(v_n_1469_);
v_val_1478_ = lean_ctor_get(v_a_1474_, 0);
lean_inc(v_val_1478_);
lean_dec_ref(v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v_val_1478_);
v___x_1480_ = v___x_1476_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_val_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
else
{
lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_del_object(v___x_1476_);
lean_dec(v_a_1474_);
v___x_1482_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1483_ = 1;
v___x_1484_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1469_, v___x_1483_);
v___x_1485_ = lean_string_append(v___x_1482_, v___x_1484_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1487_ = lean_string_append(v___x_1485_, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
v___x_1489_ = l_Lean_MessageData_ofFormat(v___x_1488_);
v___x_1490_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1489_, v_a_1470_, v_a_1471_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_IR_getDecl(v_n_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1497_, lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1503_, v_msg_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v_env_1513_; lean_object* v___x_1514_; lean_object* v_toEnvExtension_1515_; lean_object* v_asyncMode_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1512_ = lean_st_ref_get(v_a_1510_);
v_env_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc_ref(v_env_1513_);
lean_dec(v___x_1512_);
v___x_1514_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1515_ = lean_ctor_get(v___x_1514_, 0);
v_asyncMode_1516_ = lean_ctor_get(v_toEnvExtension_1515_, 2);
v___x_1517_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1518_ = lean_box(0);
v___x_1519_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1517_, v___x_1514_, v_env_1513_, v_asyncMode_1516_, v___x_1518_);
v___x_1520_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1519_, v_n_1509_);
lean_dec(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_IR_findLocalDecl___redArg(v_n_1522_, v_a_1523_);
lean_dec(v_a_1523_);
lean_dec(v_n_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_IR_findLocalDecl___redArg(v_n_1526_, v_a_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_IR_findLocalDecl(v_n_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_n_1531_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v_toEnvExtension_1538_; lean_object* v_asyncMode_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1537_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1538_ = lean_ctor_get(v___x_1537_, 0);
v_asyncMode_1539_ = lean_ctor_get(v_toEnvExtension_1538_, 2);
v___x_1540_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1541_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1540_, v___x_1537_, v_env_1536_, v_asyncMode_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v_env_1551_; lean_object* v_nextMacroScope_1552_; lean_object* v_ngen_1553_; lean_object* v_auxDeclNGen_1554_; lean_object* v_traceState_1555_; lean_object* v_messages_1556_; lean_object* v_infoState_1557_; lean_object* v_snapshotTasks_1558_; lean_object* v_newDecls_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1575_; 
v___x_1550_ = lean_st_ref_take(v_a_1548_);
v_env_1551_ = lean_ctor_get(v___x_1550_, 0);
v_nextMacroScope_1552_ = lean_ctor_get(v___x_1550_, 1);
v_ngen_1553_ = lean_ctor_get(v___x_1550_, 2);
v_auxDeclNGen_1554_ = lean_ctor_get(v___x_1550_, 3);
v_traceState_1555_ = lean_ctor_get(v___x_1550_, 4);
v_messages_1556_ = lean_ctor_get(v___x_1550_, 6);
v_infoState_1557_ = lean_ctor_get(v___x_1550_, 7);
v_snapshotTasks_1558_ = lean_ctor_get(v___x_1550_, 8);
v_newDecls_1559_ = lean_ctor_get(v___x_1550_, 9);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v___x_1550_, 5);
lean_dec(v_unused_1576_);
v___x_1561_ = v___x_1550_;
v_isShared_1562_ = v_isSharedCheck_1575_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_newDecls_1559_);
lean_inc(v_snapshotTasks_1558_);
lean_inc(v_infoState_1557_);
lean_inc(v_messages_1556_);
lean_inc(v_traceState_1555_);
lean_inc(v_auxDeclNGen_1554_);
lean_inc(v_ngen_1553_);
lean_inc(v_nextMacroScope_1552_);
lean_inc(v_env_1551_);
lean_dec(v___x_1550_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1575_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v_toEnvExtension_1564_; lean_object* v_asyncMode_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1563_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1564_ = lean_ctor_get(v___x_1563_, 0);
v_asyncMode_1565_ = lean_ctor_get(v_toEnvExtension_1564_, 2);
v___x_1566_ = lean_box(0);
v___x_1567_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1563_, v_env_1551_, v_decl_1547_, v_asyncMode_1565_, v___x_1566_);
v___x_1568_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 5, v___x_1568_);
lean_ctor_set(v___x_1561_, 0, v___x_1567_);
v___x_1570_ = v___x_1561_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_nextMacroScope_1552_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_ngen_1553_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_auxDeclNGen_1554_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_traceState_1555_);
lean_ctor_set(v_reuseFailAlloc_1574_, 5, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 6, v_messages_1556_);
lean_ctor_set(v_reuseFailAlloc_1574_, 7, v_infoState_1557_);
lean_ctor_set(v_reuseFailAlloc_1574_, 8, v_snapshotTasks_1558_);
lean_ctor_set(v_reuseFailAlloc_1574_, 9, v_newDecls_1559_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_st_ref_set(v_a_1548_, v___x_1570_);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_IR_addDecl___redArg(v_decl_1577_, v_a_1578_);
lean_dec(v_a_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_IR_addDecl___redArg(v_decl_1581_, v_a_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_IR_addDecl(v_decl_1586_, v_a_1587_, v_a_1588_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1591_, size_t v_i_1592_, size_t v_stop_1593_, lean_object* v_b_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_eq(v_i_1592_, v_stop_1593_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_array_uget_borrowed(v_as_1591_, v_i_1592_);
lean_inc(v___x_1598_);
v___x_1599_ = l_Lean_IR_addDecl___redArg(v___x_1598_, v___y_1595_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; size_t v___x_1601_; size_t v___x_1602_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = ((size_t)1ULL);
v___x_1602_ = lean_usize_add(v_i_1592_, v___x_1601_);
v_i_1592_ = v___x_1602_;
v_b_1594_ = v_a_1600_;
goto _start;
}
else
{
return v___x_1599_;
}
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_b_1594_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1605_, lean_object* v_i_1606_, lean_object* v_stop_1607_, lean_object* v_b_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_i_boxed_1611_; size_t v_stop_boxed_1612_; lean_object* v_res_1613_; 
v_i_boxed_1611_ = lean_unbox_usize(v_i_1606_);
lean_dec(v_i_1606_);
v_stop_boxed_1612_ = lean_unbox_usize(v_stop_1607_);
lean_dec(v_stop_1607_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1605_, v_i_boxed_1611_, v_stop_boxed_1612_, v_b_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v_as_1605_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_array_get_size(v_decls_1614_);
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_nat_dec_lt(v___x_1618_, v___x_1619_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
return v___x_1622_;
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_le(v___x_1619_, v___x_1619_);
if (v___x_1623_ == 0)
{
if (v___x_1621_ == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1620_);
return v___x_1624_;
}
else
{
size_t v___x_1625_; size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = lean_usize_of_nat(v___x_1619_);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1614_, v___x_1625_, v___x_1626_, v___x_1620_, v_a_1616_);
return v___x_1627_;
}
}
else
{
size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = lean_usize_of_nat(v___x_1619_);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1614_, v___x_1628_, v___x_1629_, v___x_1620_, v_a_1616_);
return v___x_1630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_IR_addDecls(v_decls_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_decls_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1636_, size_t v_i_1637_, size_t v_stop_1638_, lean_object* v_b_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1636_, v_i_1637_, v_stop_1638_, v_b_1639_, v___y_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1644_, lean_object* v_i_1645_, lean_object* v_stop_1646_, lean_object* v_b_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
size_t v_i_boxed_1651_; size_t v_stop_boxed_1652_; lean_object* v_res_1653_; 
v_i_boxed_1651_ = lean_unbox_usize(v_i_1645_);
lean_dec(v_i_1645_);
v_stop_boxed_1652_ = lean_unbox_usize(v_stop_1646_);
lean_dec(v_stop_1646_);
v_res_1653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1644_, v_i_boxed_1651_, v_stop_boxed_1652_, v_b_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_as_1644_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1657_, lean_object* v_as_1658_, size_t v_sz_1659_, size_t v_i_1660_, lean_object* v_b_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_usize_dec_lt(v_i_1660_, v_sz_1659_);
if (v___x_1662_ == 0)
{
lean_inc_ref(v_b_1661_);
return v_b_1661_;
}
else
{
lean_object* v___x_1663_; lean_object* v_a_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1663_ = lean_box(0);
v_a_1664_ = lean_array_uget_borrowed(v_as_1658_, v_i_1660_);
v___x_1665_ = l_Lean_IR_Decl_name(v_a_1664_);
v___x_1666_ = lean_name_eq(v___x_1665_, v_n_1657_);
lean_dec(v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; size_t v___x_1668_; size_t v___x_1669_; 
v___x_1667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1668_ = ((size_t)1ULL);
v___x_1669_ = lean_usize_add(v_i_1660_, v___x_1668_);
v_i_1660_ = v___x_1669_;
v_b_1661_ = v___x_1667_;
goto _start;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_inc(v_a_1664_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_a_1664_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v___x_1663_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1674_, lean_object* v_as_1675_, lean_object* v_sz_1676_, lean_object* v_i_1677_, lean_object* v_b_1678_){
_start:
{
size_t v_sz_boxed_1679_; size_t v_i_boxed_1680_; lean_object* v_res_1681_; 
v_sz_boxed_1679_ = lean_unbox_usize(v_sz_1676_);
lean_dec(v_sz_1676_);
v_i_boxed_1680_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1674_, v_as_1675_, v_sz_boxed_1679_, v_i_boxed_1680_, v_b_1678_);
lean_dec_ref(v_b_1678_);
lean_dec_ref(v_as_1675_);
lean_dec(v_n_1674_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1682_, lean_object* v_n_1683_, lean_object* v_decls_1684_){
_start:
{
lean_object* v___x_1685_; size_t v_sz_1686_; size_t v___x_1687_; lean_object* v___x_1688_; lean_object* v_fst_1689_; 
v___x_1685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1686_ = lean_array_size(v_decls_1684_);
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1683_, v_decls_1684_, v_sz_1686_, v___x_1687_, v___x_1685_);
v_fst_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_fst_1689_);
lean_dec_ref(v___x_1688_);
if (lean_obj_tag(v_fst_1689_) == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_IR_findEnvDecl(v_env_1682_, v_n_1683_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; 
v_val_1691_ = lean_ctor_get(v_fst_1689_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v_fst_1689_);
if (lean_obj_tag(v_val_1691_) == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_IR_findEnvDecl(v_env_1682_, v_n_1683_);
return v___x_1692_;
}
else
{
lean_dec(v_n_1683_);
lean_dec_ref(v_env_1682_);
return v_val_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1693_, lean_object* v_n_1694_, lean_object* v_decls_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_IR_findEnvDecl_x27(v_env_1693_, v_n_1694_, v_decls_1695_);
lean_dec_ref(v_decls_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1697_, lean_object* v_decls_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v_env_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1701_ = lean_st_ref_get(v_a_1699_);
v_env_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc_ref(v_env_1702_);
lean_dec(v___x_1701_);
v___x_1703_ = l_Lean_IR_findEnvDecl_x27(v_env_1702_, v_n_1697_, v_decls_1698_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1705_, lean_object* v_decls_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_IR_findDecl_x27___redArg(v_n_1705_, v_decls_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_decls_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1710_, lean_object* v_decls_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_IR_findDecl_x27___redArg(v_n_1710_, v_decls_1711_, v_a_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1716_, lean_object* v_decls_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_IR_findDecl_x27(v_n_1716_, v_decls_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec_ref(v_decls_1717_);
return v_res_1721_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1722_, lean_object* v_as_1723_, size_t v_i_1724_, size_t v_stop_1725_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_eq(v_i_1724_, v_stop_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = lean_array_uget_borrowed(v_as_1723_, v_i_1724_);
v___x_1728_ = l_Lean_IR_Decl_name(v___x_1727_);
v___x_1729_ = lean_name_eq(v___x_1728_, v_n_1722_);
lean_dec(v___x_1728_);
if (v___x_1729_ == 0)
{
size_t v___x_1730_; size_t v___x_1731_; 
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1724_, v___x_1730_);
v_i_1724_ = v___x_1731_;
goto _start;
}
else
{
return v___x_1729_;
}
}
else
{
uint8_t v___x_1733_; 
v___x_1733_ = 0;
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1734_, lean_object* v_as_1735_, lean_object* v_i_1736_, lean_object* v_stop_1737_){
_start:
{
size_t v_i_boxed_1738_; size_t v_stop_boxed_1739_; uint8_t v_res_1740_; lean_object* v_r_1741_; 
v_i_boxed_1738_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_stop_boxed_1739_ = lean_unbox_usize(v_stop_1737_);
lean_dec(v_stop_1737_);
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1734_, v_as_1735_, v_i_boxed_1738_, v_stop_boxed_1739_);
lean_dec_ref(v_as_1735_);
lean_dec(v_n_1734_);
v_r_1741_ = lean_box(v_res_1740_);
return v_r_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1742_, lean_object* v_decls_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_array_get_size(v_decls_1743_);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_IR_containsDecl___redArg(v_n_1742_, v_a_1744_);
return v___x_1749_;
}
else
{
if (v___x_1748_ == 0)
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_IR_containsDecl___redArg(v_n_1742_, v_a_1744_);
return v___x_1750_;
}
else
{
size_t v___x_1751_; size_t v___x_1752_; uint8_t v___x_1753_; 
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = lean_usize_of_nat(v___x_1747_);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1742_, v_decls_1743_, v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_IR_containsDecl___redArg(v_n_1742_, v_a_1744_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_n_1742_);
v___x_1755_ = lean_box(v___x_1753_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1757_, lean_object* v_decls_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1757_, v_decls_1758_, v_a_1759_);
lean_dec(v_a_1759_);
lean_dec_ref(v_decls_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1762_, lean_object* v_decls_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1762_, v_decls_1763_, v_a_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1768_, lean_object* v_decls_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_IR_containsDecl_x27(v_n_1768_, v_decls_1769_, v_a_1770_, v_a_1771_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec_ref(v_decls_1769_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1774_, lean_object* v_decls_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1797_; 
lean_inc(v_n_1774_);
v___x_1779_ = l_Lean_IR_findDecl_x27___redArg(v_n_1774_, v_decls_1775_, v_a_1777_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1797_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1797_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
if (lean_obj_tag(v_a_1780_) == 1)
{
lean_object* v_val_1784_; lean_object* v___x_1786_; 
lean_dec(v_n_1774_);
v_val_1784_ = lean_ctor_get(v_a_1780_, 0);
lean_inc(v_val_1784_);
lean_dec_ref(v_a_1780_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v_val_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_val_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1782_);
lean_dec(v_a_1780_);
v___x_1788_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1789_ = 1;
v___x_1790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1774_, v___x_1789_);
v___x_1791_ = lean_string_append(v___x_1788_, v___x_1790_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = l_Lean_MessageData_ofFormat(v___x_1794_);
v___x_1796_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1795_, v_a_1776_, v_a_1777_);
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1798_, lean_object* v_decls_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_IR_getDecl_x27(v_n_1798_, v_decls_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec_ref(v_decls_1799_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1804_, lean_object* v_declName_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_IR_findEnvDecl(v_env_1804_, v_declName_1805_);
if (lean_obj_tag(v___x_1806_) == 1)
{
lean_object* v_val_1807_; 
v_val_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1807_);
lean_dec_ref(v___x_1806_);
if (lean_obj_tag(v_val_1807_) == 0)
{
lean_object* v_info_1808_; 
v_info_1808_ = lean_ctor_get(v_val_1807_, 4);
lean_inc(v_info_1808_);
lean_dec_ref(v_val_1807_);
return v_info_1808_;
}
else
{
lean_object* v___x_1809_; 
lean_dec(v_val_1807_);
v___x_1809_ = lean_box(0);
return v___x_1809_;
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v___x_1806_);
v___x_1810_ = lean_box(0);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1811_, uint8_t v_level_1812_, uint8_t v_includeDecls_1813_, lean_object* v_as_1814_, size_t v_i_1815_, size_t v_stop_1816_, lean_object* v_b_1817_){
_start:
{
lean_object* v___y_1819_; uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_eq(v_i_1815_, v_stop_1816_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; uint8_t v___y_1826_; 
v___x_1824_ = lean_array_uget_borrowed(v_as_1814_, v_i_1815_);
if (v_includeDecls_1813_ == 0)
{
uint8_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = 1;
lean_inc(v___x_1824_);
lean_inc_ref(v_env_1811_);
v___x_1835_ = l_Lean_Environment_contains(v_env_1811_, v___x_1824_, v___x_1834_);
if (v___x_1835_ == 0)
{
goto v___jp_1830_;
}
else
{
v___y_1819_ = v_b_1817_;
goto v___jp_1818_;
}
}
else
{
goto v___jp_1830_;
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
uint8_t v___x_1827_; 
lean_inc_ref(v_env_1811_);
v___x_1827_ = l_Lean_isDeclMeta(v_env_1811_, v___x_1824_);
if (v___x_1827_ == 0)
{
v___y_1819_ = v_b_1817_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1828_; 
lean_inc(v___x_1824_);
v___x_1828_ = lean_array_push(v_b_1817_, v___x_1824_);
v___y_1819_ = v___x_1828_;
goto v___jp_1818_;
}
}
else
{
lean_object* v___x_1829_; 
lean_inc(v___x_1824_);
v___x_1829_ = lean_array_push(v_b_1817_, v___x_1824_);
v___y_1819_ = v___x_1829_;
goto v___jp_1818_;
}
}
v___jp_1830_:
{
uint8_t v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = 2;
v___x_1832_ = l_Lean_instDecidableEqOLeanLevel(v_level_1812_, v___x_1831_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
lean_inc_ref(v_env_1811_);
v___x_1833_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1811_, v___x_1824_);
v___y_1826_ = v___x_1833_;
goto v___jp_1825_;
}
else
{
v___y_1826_ = v___x_1832_;
goto v___jp_1825_;
}
}
}
else
{
lean_dec_ref(v_env_1811_);
return v_b_1817_;
}
v___jp_1818_:
{
size_t v___x_1820_; size_t v___x_1821_; 
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1815_, v___x_1820_);
v_i_1815_ = v___x_1821_;
v_b_1817_ = v___y_1819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1836_, lean_object* v_level_1837_, lean_object* v_includeDecls_1838_, lean_object* v_as_1839_, lean_object* v_i_1840_, lean_object* v_stop_1841_, lean_object* v_b_1842_){
_start:
{
uint8_t v_level_boxed_1843_; uint8_t v_includeDecls_boxed_1844_; size_t v_i_boxed_1845_; size_t v_stop_boxed_1846_; lean_object* v_res_1847_; 
v_level_boxed_1843_ = lean_unbox(v_level_1837_);
v_includeDecls_boxed_1844_ = lean_unbox(v_includeDecls_1838_);
v_i_boxed_1845_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_stop_boxed_1846_ = lean_unbox_usize(v_stop_1841_);
lean_dec(v_stop_1841_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1836_, v_level_boxed_1843_, v_includeDecls_boxed_1844_, v_as_1839_, v_i_boxed_1845_, v_stop_boxed_1846_, v_b_1842_);
lean_dec_ref(v_as_1839_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1848_, size_t v_i_1849_, lean_object* v_bs_1850_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_usize_dec_lt(v_i_1849_, v_sz_1848_);
if (v___x_1851_ == 0)
{
return v_bs_1850_;
}
else
{
lean_object* v_v_1852_; lean_object* v___x_1853_; lean_object* v_bs_x27_1854_; lean_object* v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_v_1852_ = lean_array_uget(v_bs_1850_, v_i_1849_);
v___x_1853_ = lean_unsigned_to_nat(0u);
v_bs_x27_1854_ = lean_array_uset(v_bs_1850_, v_i_1849_, v___x_1853_);
v___x_1855_ = l_Lean_IR_Decl_name(v_v_1852_);
lean_dec(v_v_1852_);
v___x_1856_ = ((size_t)1ULL);
v___x_1857_ = lean_usize_add(v_i_1849_, v___x_1856_);
v___x_1858_ = lean_array_uset(v_bs_x27_1854_, v_i_1849_, v___x_1855_);
v_i_1849_ = v___x_1857_;
v_bs_1850_ = v___x_1858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1860_, lean_object* v_i_1861_, lean_object* v_bs_1862_){
_start:
{
size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1860_);
lean_dec(v_sz_1860_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1863_, v_i_boxed_1864_, v_bs_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1868_, uint8_t v_level_1869_, uint8_t v_includeDecls_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v_toEnvExtension_1872_; lean_object* v_asyncMode_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; size_t v_sz_1877_; size_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1871_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1872_ = lean_ctor_get(v___x_1871_, 0);
v_asyncMode_1873_ = lean_ctor_get(v_toEnvExtension_1872_, 2);
v___x_1874_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc_ref(v_env_1868_);
v___x_1875_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1874_, v___x_1871_, v_env_1868_, v_asyncMode_1873_);
v___x_1876_ = lean_array_mk(v___x_1875_);
v_sz_1877_ = lean_array_size(v___x_1876_);
v___x_1878_ = ((size_t)0ULL);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1877_, v___x_1878_, v___x_1876_);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_array_get_size(v___x_1879_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1883_ = lean_nat_dec_lt(v___x_1880_, v___x_1881_);
if (v___x_1883_ == 0)
{
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_env_1868_);
return v___x_1882_;
}
else
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_nat_dec_le(v___x_1881_, v___x_1881_);
if (v___x_1884_ == 0)
{
if (v___x_1883_ == 0)
{
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_env_1868_);
return v___x_1882_;
}
else
{
size_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_usize_of_nat(v___x_1881_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1868_, v_level_1869_, v_includeDecls_1870_, v___x_1879_, v___x_1878_, v___x_1885_, v___x_1882_);
lean_dec_ref(v___x_1879_);
return v___x_1886_;
}
}
else
{
size_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_usize_of_nat(v___x_1881_);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1868_, v_level_1869_, v_includeDecls_1870_, v___x_1879_, v___x_1878_, v___x_1887_, v___x_1882_);
lean_dec_ref(v___x_1879_);
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1889_, lean_object* v_level_1890_, lean_object* v_includeDecls_1891_){
_start:
{
uint8_t v_level_boxed_1892_; uint8_t v_includeDecls_boxed_1893_; lean_object* v_res_1894_; 
v_level_boxed_1892_ = lean_unbox(v_level_1890_);
v_includeDecls_boxed_1893_ = lean_unbox(v_includeDecls_1891_);
v_res_1894_ = lean_get_ir_extra_const_names(v_env_1889_, v_level_boxed_1892_, v_includeDecls_boxed_1893_);
return v_res_1894_;
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
