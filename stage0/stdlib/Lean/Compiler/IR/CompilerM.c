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
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExternAttrData_default;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 186, 94, 176, 136, 38, 52, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_IR_log___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 220, 115, 150, 240, 139, 111, 12)}};
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 236, 150, 45, 29, 146, 124, 106)}};
static const lean_object* l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_ctor_set(v___x_158_, 3, v___x_156_);
lean_ctor_set(v___x_158_, 4, v___x_156_);
lean_ctor_set(v___x_158_, 5, v___x_156_);
lean_ctor_set(v___x_158_, 6, v___x_156_);
lean_ctor_set(v___x_158_, 7, v___x_156_);
lean_ctor_set(v___x_158_, 8, v___x_156_);
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
v___x_463_ = l_Lean_instInhabitedExternAttrData_default;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = l_Lean_IR_Decl_name(v___y_471_);
v___x_474_ = l_Lean_IR_Decl_name(v___y_472_);
v___x_475_ = l_Lean_Name_quickLt(v___x_473_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_476_, v___y_477_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v___y_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_481_, lean_object* v_lo_482_, lean_object* v_hi_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_lt(v_lo_482_, v_hi_483_);
if (v___x_484_ == 0)
{
lean_dec(v_lo_482_);
return v_as_481_;
}
else
{
lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; uint8_t v___x_489_; 
v___f_485_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_482_);
v___x_486_ = l_Array_qpartition___redArg(v_as_481_, v___f_485_, v_lo_482_, v_hi_483_);
v_fst_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_fst_487_);
v_snd_488_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_snd_488_);
lean_dec_ref(v___x_486_);
v___x_489_ = lean_nat_dec_le(v_hi_483_, v_fst_487_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_snd_488_, v_lo_482_, v_fst_487_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_fst_487_, v___x_491_);
lean_dec(v_fst_487_);
v_as_481_ = v___x_490_;
v_lo_482_ = v___x_492_;
goto _start;
}
else
{
lean_dec(v_fst_487_);
lean_dec(v_lo_482_);
return v_snd_488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_494_, lean_object* v_lo_495_, lean_object* v_hi_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_as_494_, v_lo_495_, v_hi_496_);
lean_dec(v_hi_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
return v_x_498_;
}
else
{
lean_object* v_head_500_; lean_object* v_tail_501_; lean_object* v___x_502_; 
v_head_500_ = lean_ctor_get(v_x_499_, 0);
lean_inc(v_head_500_);
v_tail_501_ = lean_ctor_get(v_x_499_, 1);
lean_inc(v_tail_501_);
lean_dec_ref(v_x_499_);
v___x_502_ = lean_array_push(v_x_498_, v_head_500_);
v_x_498_ = v___x_502_;
v_x_499_ = v_tail_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_510_, lean_object* v_as_511_, size_t v_i_512_, size_t v_stop_513_, lean_object* v_b_514_){
_start:
{
lean_object* v___y_516_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_eq(v_i_512_, v_stop_513_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; uint8_t v___y_530_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_528_ = lean_array_uget_borrowed(v_as_511_, v_i_512_);
v___x_545_ = l_Lean_IR_Decl_name(v___x_528_);
lean_inc_ref(v_env_510_);
v___x_546_ = l_Lean_isDeclMeta(v_env_510_, v___x_545_);
if (v___x_546_ == 0)
{
uint8_t v___x_547_; 
lean_inc_ref(v_env_510_);
v___x_547_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_510_, v___x_545_);
if (v___x_547_ == 0)
{
lean_dec(v___x_545_);
v___y_516_ = v_b_514_;
goto v___jp_515_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_545_);
if (v___x_548_ == 0)
{
lean_dec(v___x_545_);
v___y_530_ = v___x_548_;
goto v___jp_529_;
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = l_Lean_Name_getPrefix(v___x_545_);
lean_dec(v___x_545_);
lean_inc_ref(v_env_510_);
v___x_550_ = l_Lean_isExtern(v_env_510_, v___x_549_);
v___y_530_ = v___x_550_;
goto v___jp_529_;
}
}
}
else
{
lean_object* v___x_551_; 
lean_dec(v___x_545_);
lean_inc(v___x_528_);
v___x_551_ = lean_array_push(v_b_514_, v___x_528_);
v___y_516_ = v___x_551_;
goto v___jp_515_;
}
v___jp_529_:
{
if (v___y_530_ == 0)
{
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_f_531_; lean_object* v_xs_532_; lean_object* v_type_533_; lean_object* v___x_534_; 
v_f_531_ = lean_ctor_get(v___x_528_, 0);
v_xs_532_ = lean_ctor_get(v___x_528_, 1);
v_type_533_ = lean_ctor_get(v___x_528_, 2);
lean_inc(v_f_531_);
lean_inc_ref(v_env_510_);
v___x_534_ = lean_get_export_name_for(v_env_510_, v_f_531_);
if (lean_obj_tag(v___x_534_) == 1)
{
lean_object* v_val_535_; 
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref(v___x_534_);
if (lean_obj_tag(v_val_535_) == 1)
{
lean_object* v_str_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_str_536_ = lean_ctor_get(v_val_535_, 1);
lean_inc_ref(v_str_536_);
lean_dec_ref(v_val_535_);
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_str_536_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
lean_inc(v_type_533_);
lean_inc_ref(v_xs_532_);
lean_inc(v_f_531_);
v___x_541_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_541_, 0, v_f_531_);
lean_ctor_set(v___x_541_, 1, v_xs_532_);
lean_ctor_set(v___x_541_, 2, v_type_533_);
lean_ctor_set(v___x_541_, 3, v___x_540_);
v___x_542_ = lean_array_push(v_b_514_, v___x_541_);
v___y_516_ = v___x_542_;
goto v___jp_515_;
}
else
{
lean_dec(v_val_535_);
lean_inc(v_f_531_);
lean_inc_ref(v_xs_532_);
lean_inc(v_type_533_);
v___y_521_ = v_type_533_;
v___y_522_ = v_xs_532_;
v___y_523_ = v_f_531_;
goto v___jp_520_;
}
}
else
{
lean_dec(v___x_534_);
lean_inc(v_f_531_);
lean_inc_ref(v_xs_532_);
lean_inc(v_type_533_);
v___y_521_ = v_type_533_;
v___y_522_ = v_xs_532_;
v___y_523_ = v_f_531_;
goto v___jp_520_;
}
}
else
{
lean_object* v___x_543_; 
lean_inc(v___x_528_);
v___x_543_ = lean_array_push(v_b_514_, v___x_528_);
v___y_516_ = v___x_543_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_544_; 
lean_inc(v___x_528_);
v___x_544_ = lean_array_push(v_b_514_, v___x_528_);
v___y_516_ = v___x_544_;
goto v___jp_515_;
}
}
}
else
{
lean_dec_ref(v_env_510_);
return v_b_514_;
}
v___jp_515_:
{
size_t v___x_517_; size_t v___x_518_; 
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_512_, v___x_517_);
v_i_512_ = v___x_518_;
v_b_514_ = v___y_516_;
goto _start;
}
v___jp_520_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_525_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_525_, 0, v___y_523_);
lean_ctor_set(v___x_525_, 1, v___y_522_);
lean_ctor_set(v___x_525_, 2, v___y_521_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
v___x_526_ = lean_array_push(v_b_514_, v___x_525_);
v___y_516_ = v___x_526_;
goto v___jp_515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_552_, lean_object* v_as_553_, lean_object* v_i_554_, lean_object* v_stop_555_, lean_object* v_b_556_){
_start:
{
size_t v_i_boxed_557_; size_t v_stop_boxed_558_; lean_object* v_res_559_; 
v_i_boxed_557_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_stop_boxed_558_ = lean_unbox_usize(v_stop_555_);
lean_dec(v_stop_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_552_, v_as_553_, v_i_boxed_557_, v_stop_boxed_558_, v_b_556_);
lean_dec_ref(v_as_553_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_562_, lean_object* v_as_563_, lean_object* v_start_564_, lean_object* v_stop_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_567_ = lean_nat_dec_lt(v_start_564_, v_stop_565_);
if (v___x_567_ == 0)
{
lean_dec_ref(v_env_562_);
return v___x_566_;
}
else
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_as_563_);
v___x_569_ = lean_nat_dec_le(v_stop_565_, v___x_568_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; 
v___x_570_ = lean_nat_dec_lt(v_start_564_, v___x_568_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_env_562_);
return v___x_566_;
}
else
{
size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_usize_of_nat(v_start_564_);
v___x_572_ = lean_usize_of_nat(v___x_568_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_562_, v_as_563_, v___x_571_, v___x_572_, v___x_566_);
return v___x_573_;
}
}
else
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_usize_of_nat(v_start_564_);
v___x_575_ = lean_usize_of_nat(v_stop_565_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_562_, v_as_563_, v___x_574_, v___x_575_, v___x_566_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_577_, lean_object* v_as_578_, lean_object* v_start_579_, lean_object* v_stop_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_577_, v_as_578_, v_start_579_, v_stop_580_);
lean_dec(v_stop_580_);
lean_dec(v_start_579_);
lean_dec_ref(v_as_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_582_, lean_object* v_s_583_, lean_object* v_entries_584_){
_start:
{
lean_object* v___y_586_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_decls_596_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_596_ = l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_595_, v_entries_584_);
v___x_601_ = lean_array_get_size(v_decls_596_);
v___x_602_ = lean_nat_dec_eq(v___x_601_, v___x_594_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___y_606_; uint8_t v___x_608_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_sub(v___x_601_, v___x_603_);
v___x_608_ = lean_nat_dec_le(v___x_594_, v___x_604_);
if (v___x_608_ == 0)
{
lean_inc(v___x_604_);
v___y_606_ = v___x_604_;
goto v___jp_605_;
}
else
{
v___y_606_ = v___x_594_;
goto v___jp_605_;
}
v___jp_605_:
{
uint8_t v___x_607_; 
v___x_607_ = lean_nat_dec_le(v___y_606_, v___x_604_);
if (v___x_607_ == 0)
{
lean_dec(v___x_604_);
lean_inc(v___y_606_);
v___y_598_ = v___y_606_;
v___y_599_ = v___y_606_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___y_606_;
v___y_599_ = v___x_604_;
goto v___jp_597_;
}
}
}
else
{
v___y_586_ = v_decls_596_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v___x_587_; uint8_t v_isModule_588_; 
v___x_587_ = l_Lean_Environment_header(v_env_582_);
v_isModule_588_ = lean_ctor_get_uint8(v___x_587_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_587_);
if (v_isModule_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v_env_582_);
lean_inc_ref_n(v___y_586_, 2);
v___x_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_589_, 0, v___y_586_);
lean_ctor_set(v___x_589_, 1, v___y_586_);
lean_ctor_set(v___x_589_, 2, v___y_586_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_array_get_size(v___y_586_);
v___x_592_ = l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_582_, v___y_586_, v___x_590_, v___x_591_);
lean_dec_ref(v___y_586_);
lean_inc_ref_n(v___x_592_, 2);
v___x_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
return v___x_593_;
}
}
v___jp_597_:
{
lean_object* v___x_600_; 
v___x_600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_decls_596_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
v___y_586_ = v___x_600_;
goto v___jp_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_609_, lean_object* v_s_610_, lean_object* v_entries_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_609_, v_s_610_, v_entries_611_);
lean_dec_ref(v_s_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_array_mk(v_es_613_);
return v___x_614_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_keys_615_, lean_object* v_i_616_, lean_object* v_k_617_){
_start:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_array_get_size(v_keys_615_);
v___x_619_ = lean_nat_dec_lt(v_i_616_, v___x_618_);
if (v___x_619_ == 0)
{
lean_dec(v_i_616_);
return v___x_619_;
}
else
{
lean_object* v_k_x27_620_; uint8_t v___x_621_; 
v_k_x27_620_ = lean_array_fget_borrowed(v_keys_615_, v_i_616_);
v___x_621_ = lean_name_eq(v_k_617_, v_k_x27_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v_i_616_, v___x_622_);
lean_dec(v_i_616_);
v_i_616_ = v___x_623_;
goto _start;
}
else
{
lean_dec(v_i_616_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_keys_625_, lean_object* v_i_626_, lean_object* v_k_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_keys_625_, v_i_626_, v_k_627_);
lean_dec(v_k_627_);
lean_dec_ref(v_keys_625_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; 
v___x_630_ = ((size_t)5ULL);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_shift_left(v___x_631_, v___x_630_);
return v___x_632_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; 
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0);
v___x_635_ = lean_usize_sub(v___x_634_, v___x_633_);
return v___x_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_x_636_, size_t v_x_637_, lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v_es_639_; lean_object* v___x_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v_j_644_; lean_object* v___x_645_; 
v_es_639_ = lean_ctor_get(v_x_636_, 0);
v___x_640_ = lean_box(2);
v___x_641_ = ((size_t)5ULL);
v___x_642_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_643_ = lean_usize_land(v_x_637_, v___x_642_);
v_j_644_ = lean_usize_to_nat(v___x_643_);
v___x_645_ = lean_array_get_borrowed(v___x_640_, v_es_639_, v_j_644_);
lean_dec(v_j_644_);
switch(lean_obj_tag(v___x_645_))
{
case 0:
{
lean_object* v_key_646_; uint8_t v___x_647_; 
v_key_646_ = lean_ctor_get(v___x_645_, 0);
v___x_647_ = lean_name_eq(v_x_638_, v_key_646_);
return v___x_647_;
}
case 1:
{
lean_object* v_node_648_; size_t v___x_649_; 
v_node_648_ = lean_ctor_get(v___x_645_, 0);
v___x_649_ = lean_usize_shift_right(v_x_637_, v___x_641_);
v_x_636_ = v_node_648_;
v_x_637_ = v___x_649_;
goto _start;
}
default: 
{
uint8_t v___x_651_; 
v___x_651_ = 0;
return v___x_651_;
}
}
}
else
{
lean_object* v_ks_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_ks_652_ = lean_ctor_get(v_x_636_, 0);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ks_652_, v___x_653_, v_x_638_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
size_t v_x_2458__boxed_658_; uint8_t v_res_659_; lean_object* v_r_660_; 
v_x_2458__boxed_658_ = lean_unbox_usize(v_x_656_);
lean_dec(v_x_656_);
v_res_659_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_655_, v_x_2458__boxed_658_, v_x_657_);
lean_dec(v_x_657_);
lean_dec_ref(v_x_655_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_661_; uint64_t v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(1723u);
v___x_662_ = lean_uint64_of_nat(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint64_t v___y_666_; 
if (lean_obj_tag(v_x_664_) == 0)
{
uint64_t v___x_669_; 
v___x_669_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_666_ = v___x_669_;
goto v___jp_665_;
}
else
{
uint64_t v_hash_670_; 
v_hash_670_ = lean_ctor_get_uint64(v_x_664_, sizeof(void*)*2);
v___y_666_ = v_hash_670_;
goto v___jp_665_;
}
v___jp_665_:
{
size_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_uint64_to_usize(v___y_666_);
v___x_668_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_663_, v___x_667_, v_x_664_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec_ref(v_x_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_675_, lean_object* v_x2_676_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = l_Lean_IR_Decl_name(v_x2_676_);
v___x_678_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_675_, v___x_677_);
lean_dec(v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = 1;
return v___x_679_;
}
else
{
uint8_t v___x_680_; 
v___x_680_ = 0;
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_681_, lean_object* v_x2_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_681_, v_x2_682_);
lean_dec_ref(v_x2_682_);
lean_dec_ref(v_x1_681_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_685_;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_obj_once(&l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_690_);
lean_dec_ref(v_x_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
lean_object* v_ks_696_; lean_object* v_vs_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_721_; 
v_ks_696_ = lean_ctor_get(v_x_692_, 0);
v_vs_697_ = lean_ctor_get(v_x_692_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_692_);
if (v_isSharedCheck_721_ == 0)
{
v___x_699_ = v_x_692_;
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_vs_697_);
lean_inc(v_ks_696_);
lean_dec(v_x_692_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_array_get_size(v_ks_696_);
v___x_702_ = lean_nat_dec_lt(v_x_693_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_dec(v_x_693_);
v___x_703_ = lean_array_push(v_ks_696_, v_x_694_);
v___x_704_ = lean_array_push(v_vs_697_, v_x_695_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_704_);
lean_ctor_set(v___x_699_, 0, v___x_703_);
v___x_706_ = v___x_699_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v_k_x27_708_; uint8_t v___x_709_; 
v_k_x27_708_ = lean_array_fget_borrowed(v_ks_696_, v_x_693_);
v___x_709_ = lean_name_eq(v_x_694_, v_k_x27_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_711_; 
if (v_isShared_700_ == 0)
{
v___x_711_ = v___x_699_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_ks_696_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_vs_697_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_x_693_, v___x_712_);
lean_dec(v_x_693_);
v_x_692_ = v___x_711_;
v_x_693_ = v___x_713_;
goto _start;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_716_ = lean_array_fset(v_ks_696_, v_x_693_, v_x_694_);
v___x_717_ = lean_array_fset(v_vs_697_, v_x_693_, v_x_695_);
lean_dec(v_x_693_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_717_);
lean_ctor_set(v___x_699_, 0, v___x_716_);
v___x_719_ = v___x_699_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_n_722_, lean_object* v_k_723_, lean_object* v_v_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(v_n_722_, v___x_725_, v_k_723_, v_v_724_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_x_728_, size_t v_x_729_, size_t v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
lean_object* v_es_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v_j_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_es_733_ = lean_ctor_get(v_x_728_, 0);
v___x_734_ = ((size_t)5ULL);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_737_ = lean_usize_land(v_x_729_, v___x_736_);
v_j_738_ = lean_usize_to_nat(v___x_737_);
v___x_739_ = lean_array_get_size(v_es_733_);
v___x_740_ = lean_nat_dec_lt(v_j_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_j_738_);
lean_dec(v_x_732_);
lean_dec(v_x_731_);
return v_x_728_;
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_777_; 
lean_inc_ref(v_es_733_);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v_x_728_, 0);
lean_dec(v_unused_778_);
v___x_742_ = v_x_728_;
v_isShared_743_ = v_isSharedCheck_777_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_x_728_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_777_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_v_744_; lean_object* v___x_745_; lean_object* v_xs_x27_746_; lean_object* v___y_748_; 
v_v_744_ = lean_array_fget(v_es_733_, v_j_738_);
v___x_745_ = lean_box(0);
v_xs_x27_746_ = lean_array_fset(v_es_733_, v_j_738_, v___x_745_);
switch(lean_obj_tag(v_v_744_))
{
case 0:
{
lean_object* v_key_753_; lean_object* v_val_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_764_; 
v_key_753_ = lean_ctor_get(v_v_744_, 0);
v_val_754_ = lean_ctor_get(v_v_744_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_v_744_);
if (v_isSharedCheck_764_ == 0)
{
v___x_756_ = v_v_744_;
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_val_754_);
lean_inc(v_key_753_);
lean_dec(v_v_744_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
uint8_t v___x_758_; 
v___x_758_ = lean_name_eq(v_x_731_, v_key_753_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_del_object(v___x_756_);
v___x_759_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_753_, v_val_754_, v_x_731_, v_x_732_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___y_748_ = v___x_760_;
goto v___jp_747_;
}
else
{
lean_object* v___x_762_; 
lean_dec(v_val_754_);
lean_dec(v_key_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_x_732_);
lean_ctor_set(v___x_756_, 0, v_x_731_);
v___x_762_ = v___x_756_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_x_731_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_x_732_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v___y_748_ = v___x_762_;
goto v___jp_747_;
}
}
}
}
case 1:
{
lean_object* v_node_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_775_; 
v_node_765_ = lean_ctor_get(v_v_744_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_v_744_);
if (v_isSharedCheck_775_ == 0)
{
v___x_767_ = v_v_744_;
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_node_765_);
lean_dec(v_v_744_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_769_ = lean_usize_shift_right(v_x_729_, v___x_734_);
v___x_770_ = lean_usize_add(v_x_730_, v___x_735_);
v___x_771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(v_node_765_, v___x_769_, v___x_770_, v_x_731_, v_x_732_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_771_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
v___y_748_ = v___x_773_;
goto v___jp_747_;
}
}
}
default: 
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_x_731_);
lean_ctor_set(v___x_776_, 1, v_x_732_);
v___y_748_ = v___x_776_;
goto v___jp_747_;
}
}
v___jp_747_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = lean_array_fset(v_xs_x27_746_, v_j_738_, v___y_748_);
lean_dec(v_j_738_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_749_);
v___x_751_ = v___x_742_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
else
{
lean_object* v_ks_779_; lean_object* v_vs_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_800_; 
v_ks_779_ = lean_ctor_get(v_x_728_, 0);
v_vs_780_ = lean_ctor_get(v_x_728_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_800_ == 0)
{
v___x_782_ = v_x_728_;
v_isShared_783_ = v_isSharedCheck_800_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_vs_780_);
lean_inc(v_ks_779_);
lean_dec(v_x_728_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_800_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_ks_779_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_vs_780_);
v___x_785_ = v_reuseFailAlloc_799_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v_newNode_786_; uint8_t v___y_788_; size_t v___x_794_; uint8_t v___x_795_; 
v_newNode_786_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_785_, v_x_731_, v_x_732_);
v___x_794_ = ((size_t)7ULL);
v___x_795_ = lean_usize_dec_le(v___x_794_, v_x_730_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_786_);
v___x_797_ = lean_unsigned_to_nat(4u);
v___x_798_ = lean_nat_dec_lt(v___x_796_, v___x_797_);
lean_dec(v___x_796_);
v___y_788_ = v___x_798_;
goto v___jp_787_;
}
else
{
v___y_788_ = v___x_795_;
goto v___jp_787_;
}
v___jp_787_:
{
if (v___y_788_ == 0)
{
lean_object* v_ks_789_; lean_object* v_vs_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_ks_789_ = lean_ctor_get(v_newNode_786_, 0);
lean_inc_ref(v_ks_789_);
v_vs_790_ = lean_ctor_get(v_newNode_786_, 1);
lean_inc_ref(v_vs_790_);
lean_dec_ref(v_newNode_786_);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0);
v___x_793_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_x_730_, v_ks_789_, v_vs_790_, v___x_791_, v___x_792_);
lean_dec_ref(v_vs_790_);
lean_dec_ref(v_ks_789_);
return v___x_793_;
}
else
{
return v_newNode_786_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(size_t v_depth_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_i_804_, lean_object* v_entries_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_array_get_size(v_keys_802_);
v___x_807_ = lean_nat_dec_lt(v_i_804_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_i_804_);
return v_entries_805_;
}
else
{
lean_object* v_k_808_; lean_object* v_v_809_; uint64_t v___y_811_; 
v_k_808_ = lean_array_fget_borrowed(v_keys_802_, v_i_804_);
v_v_809_ = lean_array_fget_borrowed(v_vals_803_, v_i_804_);
if (lean_obj_tag(v_k_808_) == 0)
{
uint64_t v___x_822_; 
v___x_822_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_811_ = v___x_822_;
goto v___jp_810_;
}
else
{
uint64_t v_hash_823_; 
v_hash_823_ = lean_ctor_get_uint64(v_k_808_, sizeof(void*)*2);
v___y_811_ = v_hash_823_;
goto v___jp_810_;
}
v___jp_810_:
{
size_t v_h_812_; size_t v___x_813_; lean_object* v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v_h_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_h_812_ = lean_uint64_to_usize(v___y_811_);
v___x_813_ = ((size_t)5ULL);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_sub(v_depth_801_, v___x_815_);
v___x_817_ = lean_usize_mul(v___x_813_, v___x_816_);
v_h_818_ = lean_usize_shift_right(v_h_812_, v___x_817_);
v___x_819_ = lean_nat_add(v_i_804_, v___x_814_);
lean_dec(v_i_804_);
lean_inc(v_v_809_);
lean_inc(v_k_808_);
v___x_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(v_entries_805_, v_h_818_, v_depth_801_, v_k_808_, v_v_809_);
v_i_804_ = v___x_819_;
v_entries_805_ = v___x_820_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_i_827_, lean_object* v_entries_828_){
_start:
{
size_t v_depth_boxed_829_; lean_object* v_res_830_; 
v_depth_boxed_829_ = lean_unbox_usize(v_depth_824_);
lean_dec(v_depth_824_);
v_res_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_depth_boxed_829_, v_keys_825_, v_vals_826_, v_i_827_, v_entries_828_);
lean_dec_ref(v_vals_826_);
lean_dec_ref(v_keys_825_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
size_t v_x_2642__boxed_836_; size_t v_x_2643__boxed_837_; lean_object* v_res_838_; 
v_x_2642__boxed_836_ = lean_unbox_usize(v_x_832_);
lean_dec(v_x_832_);
v_x_2643__boxed_837_ = lean_unbox_usize(v_x_833_);
lean_dec(v_x_833_);
v_res_838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_831_, v_x_2642__boxed_836_, v_x_2643__boxed_837_, v_x_834_, v_x_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint64_t v___y_843_; 
if (lean_obj_tag(v_x_840_) == 0)
{
uint64_t v___x_847_; 
v___x_847_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_843_ = v___x_847_;
goto v___jp_842_;
}
else
{
uint64_t v_hash_848_; 
v_hash_848_ = lean_ctor_get_uint64(v_x_840_, sizeof(void*)*2);
v___y_843_ = v_hash_848_;
goto v___jp_842_;
}
v___jp_842_:
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_uint64_to_usize(v___y_843_);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_839_, v___x_844_, v___x_845_, v_x_840_, v_x_841_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_849_, lean_object* v_d_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = l_Lean_IR_Decl_name(v_d_850_);
v___x_852_ = l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_849_, v___x_851_, v_d_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_881_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_884_, lean_object* v_as_885_, lean_object* v_lo_886_, lean_object* v_hi_887_, lean_object* v_w_888_, lean_object* v_hlo_889_, lean_object* v_hhi_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_as_885_, v_lo_886_, v_hi_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_892_, lean_object* v_as_893_, lean_object* v_lo_894_, lean_object* v_hi_895_, lean_object* v_w_896_, lean_object* v_hlo_897_, lean_object* v_hhi_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_892_, v_as_893_, v_lo_894_, v_hi_895_, v_w_896_, v_hlo_897_, v_hhi_898_);
lean_dec(v_hi_895_);
lean_dec(v_n_892_);
return v_res_899_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_904_, v_x_905_, v_x_906_);
lean_dec(v_x_906_);
lean_dec_ref(v_x_905_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_910_, v_x_911_, v_x_912_);
return v___x_913_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b2_914_, lean_object* v_x_915_, size_t v_x_916_, lean_object* v_x_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_915_, v_x_916_, v_x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
size_t v_x_2929__boxed_923_; uint8_t v_res_924_; lean_object* v_r_925_; 
v_x_2929__boxed_923_ = lean_unbox_usize(v_x_921_);
lean_dec(v_x_921_);
v_res_924_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_919_, v_x_920_, v_x_2929__boxed_923_, v_x_922_);
lean_dec(v_x_922_);
lean_dec_ref(v_x_920_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b2_926_, lean_object* v_x_927_, size_t v_x_928_, size_t v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_927_, v_x_928_, v_x_929_, v_x_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
size_t v_x_2940__boxed_939_; size_t v_x_2941__boxed_940_; lean_object* v_res_941_; 
v_x_2940__boxed_939_ = lean_unbox_usize(v_x_935_);
lean_dec(v_x_935_);
v_x_2941__boxed_940_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b2_933_, v_x_934_, v_x_2940__boxed_939_, v_x_2941__boxed_940_, v_x_937_, v_x_938_);
return v_res_941_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b2_942_, lean_object* v_keys_943_, lean_object* v_vals_944_, lean_object* v_heq_945_, lean_object* v_i_946_, lean_object* v_k_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_keys_943_, v_i_946_, v_k_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b2_949_, v_keys_950_, v_vals_951_, v_heq_952_, v_i_953_, v_k_954_);
lean_dec(v_k_954_);
lean_dec_ref(v_vals_951_);
lean_dec_ref(v_keys_950_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_957_, lean_object* v_n_958_, lean_object* v_k_959_, lean_object* v_v_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_n_958_, v_k_959_, v_v_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_00_u03b2_962_, size_t v_depth_963_, lean_object* v_keys_964_, lean_object* v_vals_965_, lean_object* v_heq_966_, lean_object* v_i_967_, lean_object* v_entries_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_depth_963_, v_keys_964_, v_vals_965_, v_i_967_, v_entries_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b2_970_, lean_object* v_depth_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_heq_974_, lean_object* v_i_975_, lean_object* v_entries_976_){
_start:
{
size_t v_depth_boxed_977_; lean_object* v_res_978_; 
v_depth_boxed_977_ = lean_unbox_usize(v_depth_971_);
lean_dec(v_depth_971_);
v_res_978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_00_u03b2_970_, v_depth_boxed_977_, v_keys_972_, v_vals_973_, v_heq_974_, v_i_975_, v_entries_976_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(v_x_980_, v_x_981_, v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_985_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = lean_array_get_size(v_irDecls_985_);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_nat_dec_eq(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___y_992_; uint8_t v___x_996_; 
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_sub(v___x_986_, v___x_989_);
v___x_996_ = lean_nat_dec_le(v___x_987_, v___x_990_);
if (v___x_996_ == 0)
{
lean_inc(v___x_990_);
v___y_992_ = v___x_990_;
goto v___jp_991_;
}
else
{
v___y_992_ = v___x_987_;
goto v___jp_991_;
}
v___jp_991_:
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_le(v___y_992_, v___x_990_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_dec(v___x_990_);
lean_inc(v___y_992_);
v___x_994_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_irDecls_985_, v___y_992_, v___y_992_);
lean_dec(v___y_992_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_irDecls_985_, v___y_992_, v___x_990_);
lean_dec(v___x_990_);
return v___x_995_;
}
}
}
else
{
return v_irDecls_985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_997_){
_start:
{
lean_inc_ref(v_initDecls_997_);
return v_initDecls_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_998_);
lean_dec_ref(v_initDecls_998_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1000_){
_start:
{
lean_inc_ref(v_modPkg_1000_);
return v_modPkg_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1001_);
lean_dec_ref(v_modPkg_1001_);
return v_res_1002_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1006_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0));
v___x_1007_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1006_, v___x_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v_toEnvExtension_1013_; lean_object* v_name_1014_; lean_object* v_asyncMode_1015_; lean_object* v___x_1016_; lean_object* v_ext_1017_; lean_object* v_toEnvExtension_1018_; lean_object* v_name_1019_; lean_object* v_exportEntriesFn_1020_; lean_object* v_asyncMode_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_private_1028_; lean_object* v___x_1029_; lean_object* v_toEnvExtension_1030_; lean_object* v_name_1031_; lean_object* v_exportEntriesFn_1032_; lean_object* v_asyncMode_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_private_1037_; lean_object* v___x_1038_; lean_object* v_irDecls_1039_; lean_object* v_irEntries_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1012_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1013_ = lean_ctor_get(v___x_1012_, 0);
v_name_1014_ = lean_ctor_get(v___x_1012_, 1);
v_asyncMode_1015_ = lean_ctor_get(v_toEnvExtension_1013_, 2);
v___x_1016_ = l_Lean_regularInitAttr;
v_ext_1017_ = lean_ctor_get(v___x_1016_, 1);
v_toEnvExtension_1018_ = lean_ctor_get(v_ext_1017_, 0);
v_name_1019_ = lean_ctor_get(v_ext_1017_, 1);
v_exportEntriesFn_1020_ = lean_ctor_get(v_ext_1017_, 4);
v_asyncMode_1021_ = lean_ctor_get(v_toEnvExtension_1018_, 2);
v___x_1022_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1023_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
lean_inc_ref_n(v_env_1011_, 4);
v___x_1024_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1022_, v___x_1012_, v_env_1011_, v_asyncMode_1015_);
v___x_1025_ = lean_box(0);
v___x_1026_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1023_, v_ext_1017_, v_env_1011_, v_asyncMode_1021_, v___x_1025_);
lean_inc_ref(v_exportEntriesFn_1020_);
v___x_1027_ = lean_apply_2(v_exportEntriesFn_1020_, v_env_1011_, v___x_1026_);
v_private_1028_ = lean_ctor_get(v___x_1027_, 2);
lean_inc(v_private_1028_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1030_ = lean_ctor_get(v___x_1029_, 0);
v_name_1031_ = lean_ctor_get(v___x_1029_, 1);
v_exportEntriesFn_1032_ = lean_ctor_get(v___x_1029_, 4);
v_asyncMode_1033_ = lean_ctor_get(v_toEnvExtension_1030_, 2);
v___x_1034_ = lean_box(0);
v___x_1035_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1034_, v___x_1029_, v_env_1011_, v_asyncMode_1033_, v___x_1025_);
lean_inc_ref(v_exportEntriesFn_1032_);
v___x_1036_ = lean_apply_2(v_exportEntriesFn_1032_, v_env_1011_, v___x_1035_);
v_private_1037_ = lean_ctor_get(v___x_1036_, 2);
lean_inc(v_private_1037_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_irDecls_1039_ = l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1038_, v___x_1024_);
v_irEntries_1040_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(v_irDecls_1039_);
lean_inc(v_name_1014_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_name_1014_);
lean_ctor_set(v___x_1041_, 1, v_irEntries_1040_);
lean_inc(v_name_1019_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_name_1019_);
lean_ctor_set(v___x_1042_, 1, v_private_1028_);
lean_inc(v_name_1031_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_name_1031_);
lean_ctor_set(v___x_1043_, 1, v_private_1037_);
v___x_1044_ = lean_unsigned_to_nat(3u);
v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1044_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1041_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1042_);
v___x_1048_ = lean_array_push(v___x_1047_, v___x_1043_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1049_, lean_object* v_k_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_m_1055_; lean_object* v_a_1056_; uint8_t v___x_1057_; 
v___x_1053_ = lean_nat_add(v_x_1051_, v_x_1052_);
v___x_1054_ = lean_unsigned_to_nat(1u);
v_m_1055_ = lean_nat_shiftr(v___x_1053_, v___x_1054_);
lean_dec(v___x_1053_);
v_a_1056_ = lean_array_fget_borrowed(v_as_1049_, v_m_1055_);
v___x_1057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1056_, v_k_1050_);
if (v___x_1057_ == 0)
{
uint8_t v___x_1058_; 
lean_dec(v_x_1052_);
v___x_1058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1050_, v_a_1056_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v_m_1055_);
lean_dec(v_x_1051_);
lean_inc(v_a_1056_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_a_1056_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_nat_dec_eq(v_m_1055_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_nat_sub(v_m_1055_, v___x_1054_);
lean_dec(v_m_1055_);
v___x_1063_ = lean_nat_dec_lt(v___x_1062_, v_x_1051_);
if (v___x_1063_ == 0)
{
v_x_1052_ = v___x_1062_;
goto _start;
}
else
{
lean_object* v___x_1065_; 
lean_dec(v___x_1062_);
lean_dec(v_x_1051_);
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_m_1055_);
lean_dec(v_x_1051_);
v___x_1066_ = lean_box(0);
return v___x_1066_;
}
}
}
else
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
lean_dec(v_x_1051_);
v___x_1067_ = lean_nat_add(v_m_1055_, v___x_1054_);
lean_dec(v_m_1055_);
v___x_1068_ = lean_nat_dec_le(v___x_1067_, v_x_1052_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v___x_1067_);
lean_dec(v_x_1052_);
v___x_1069_ = lean_box(0);
return v___x_1069_;
}
else
{
v_x_1051_ = v___x_1067_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1071_, lean_object* v_k_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1071_, v_k_1072_, v_x_1073_, v_x_1074_);
lean_dec_ref(v_k_1072_);
lean_dec_ref(v_as_1071_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1076_, lean_object* v_vals_1077_, lean_object* v_i_1078_, lean_object* v_k_1079_){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_array_get_size(v_keys_1076_);
v___x_1081_ = lean_nat_dec_lt(v_i_1078_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v_i_1078_);
v___x_1082_ = lean_box(0);
return v___x_1082_;
}
else
{
lean_object* v_k_x27_1083_; uint8_t v___x_1084_; 
v_k_x27_1083_ = lean_array_fget_borrowed(v_keys_1076_, v_i_1078_);
v___x_1084_ = lean_name_eq(v_k_1079_, v_k_x27_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_nat_add(v_i_1078_, v___x_1085_);
lean_dec(v_i_1078_);
v_i_1078_ = v___x_1086_;
goto _start;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_array_fget_borrowed(v_vals_1077_, v_i_1078_);
lean_dec(v_i_1078_);
lean_inc(v___x_1088_);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1090_, lean_object* v_vals_1091_, lean_object* v_i_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1090_, v_vals_1091_, v_i_1092_, v_k_1093_);
lean_dec(v_k_1093_);
lean_dec_ref(v_vals_1091_);
lean_dec_ref(v_keys_1090_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1095_, size_t v_x_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_object* v_es_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1119_; 
v_es_1098_ = lean_ctor_get(v_x_1095_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1095_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1100_ = v_x_1095_;
v_isShared_1101_ = v_isSharedCheck_1119_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_es_1098_);
lean_dec(v_x_1095_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1119_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v_j_1106_; lean_object* v___x_1107_; 
v___x_1102_ = lean_box(2);
v___x_1103_ = ((size_t)5ULL);
v___x_1104_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1105_ = lean_usize_land(v_x_1096_, v___x_1104_);
v_j_1106_ = lean_usize_to_nat(v___x_1105_);
v___x_1107_ = lean_array_get(v___x_1102_, v_es_1098_, v_j_1106_);
lean_dec(v_j_1106_);
lean_dec_ref(v_es_1098_);
switch(lean_obj_tag(v___x_1107_))
{
case 0:
{
lean_object* v_key_1108_; lean_object* v_val_1109_; uint8_t v___x_1110_; 
v_key_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_key_1108_);
v_val_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_val_1109_);
lean_dec_ref(v___x_1107_);
v___x_1110_ = lean_name_eq(v_x_1097_, v_key_1108_);
lean_dec(v_key_1108_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_val_1109_);
lean_del_object(v___x_1100_);
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
else
{
lean_object* v___x_1113_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 1);
lean_ctor_set(v___x_1100_, 0, v_val_1109_);
v___x_1113_ = v___x_1100_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_val_1109_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
case 1:
{
lean_object* v_node_1115_; size_t v___x_1116_; 
lean_del_object(v___x_1100_);
v_node_1115_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_node_1115_);
lean_dec_ref(v___x_1107_);
v___x_1116_ = lean_usize_shift_right(v_x_1096_, v___x_1103_);
v_x_1095_ = v_node_1115_;
v_x_1096_ = v___x_1116_;
goto _start;
}
default: 
{
lean_object* v___x_1118_; 
lean_del_object(v___x_1100_);
v___x_1118_ = lean_box(0);
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_ks_1120_; lean_object* v_vs_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_ks_1120_ = lean_ctor_get(v_x_1095_, 0);
lean_inc_ref(v_ks_1120_);
v_vs_1121_ = lean_ctor_get(v_x_1095_, 1);
lean_inc_ref(v_vs_1121_);
lean_dec_ref(v_x_1095_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1120_, v_vs_1121_, v___x_1122_, v_x_1097_);
lean_dec_ref(v_vs_1121_);
lean_dec_ref(v_ks_1120_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
size_t v_x_414__boxed_1127_; lean_object* v_res_1128_; 
v_x_414__boxed_1127_ = lean_unbox_usize(v_x_1125_);
lean_dec(v_x_1125_);
v_res_1128_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1124_, v_x_414__boxed_1127_, v_x_1126_);
lean_dec(v_x_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint64_t v___y_1132_; 
if (lean_obj_tag(v_x_1130_) == 0)
{
uint64_t v___x_1135_; 
v___x_1135_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_1132_ = v___x_1135_;
goto v___jp_1131_;
}
else
{
uint64_t v_hash_1136_; 
v_hash_1136_ = lean_ctor_get_uint64(v_x_1130_, sizeof(void*)*2);
v___y_1132_ = v_hash_1136_;
goto v___jp_1131_;
}
v___jp_1131_:
{
size_t v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_uint64_to_usize(v___y_1132_);
v___x_1134_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1129_, v___x_1133_, v_x_1130_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1137_, v_x_1138_);
lean_dec(v_x_1138_);
return v_res_1139_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1143_, lean_object* v_declName_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1154_; 
v___x_1145_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1146_ = l_Lean_IR_declMapExt;
v___x_1154_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1143_, v_declName_1144_);
if (lean_obj_tag(v___x_1154_) == 0)
{
goto v___jp_1147_;
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_val_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_val_1155_);
lean_dec_ref(v___x_1154_);
v___x_1170_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1145_, v___x_1146_, v_env_1143_, v_val_1155_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_array_get_size(v___x_1170_);
v___x_1173_ = lean_nat_dec_lt(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec_ref(v___x_1170_);
goto v___jp_1156_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_sub(v___x_1172_, v___x_1174_);
v___x_1176_ = lean_nat_dec_le(v___x_1171_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v___x_1175_);
lean_dec_ref(v___x_1170_);
goto v___jp_1156_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_tmpDecl_1180_; lean_object* v___x_1181_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1178_ = lean_box(0);
v___x_1179_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1144_);
v_tmpDecl_1180_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1180_, 0, v_declName_1144_);
lean_ctor_set(v_tmpDecl_1180_, 1, v___x_1177_);
lean_ctor_set(v_tmpDecl_1180_, 2, v___x_1178_);
lean_ctor_set(v_tmpDecl_1180_, 3, v___x_1179_);
v___x_1181_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1170_, v_tmpDecl_1180_, v___x_1171_, v___x_1175_);
lean_dec_ref(v_tmpDecl_1180_);
lean_dec_ref(v___x_1170_);
if (lean_obj_tag(v___x_1181_) == 0)
{
goto v___jp_1156_;
}
else
{
lean_dec(v_val_1155_);
lean_dec(v_declName_1144_);
lean_dec_ref(v_env_1143_);
return v___x_1181_;
}
}
}
v___jp_1156_:
{
uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1157_ = 0;
v___x_1158_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1145_, v___x_1146_, v_env_1143_, v_val_1155_, v___x_1157_);
lean_dec(v_val_1155_);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_array_get_size(v___x_1158_);
v___x_1161_ = lean_nat_dec_lt(v___x_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_dec_ref(v___x_1158_);
goto v___jp_1147_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_sub(v___x_1160_, v___x_1162_);
v___x_1164_ = lean_nat_dec_le(v___x_1159_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_dec(v___x_1163_);
lean_dec_ref(v___x_1158_);
goto v___jp_1147_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_tmpDecl_1168_; lean_object* v___x_1169_; 
v___x_1165_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1144_);
v_tmpDecl_1168_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1168_, 0, v_declName_1144_);
lean_ctor_set(v_tmpDecl_1168_, 1, v___x_1165_);
lean_ctor_set(v_tmpDecl_1168_, 2, v___x_1166_);
lean_ctor_set(v_tmpDecl_1168_, 3, v___x_1167_);
v___x_1169_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1158_, v_tmpDecl_1168_, v___x_1159_, v___x_1163_);
lean_dec_ref(v_tmpDecl_1168_);
lean_dec_ref(v___x_1158_);
if (lean_obj_tag(v___x_1169_) == 0)
{
goto v___jp_1147_;
}
else
{
lean_dec(v_declName_1144_);
lean_dec_ref(v_env_1143_);
return v___x_1169_;
}
}
}
}
}
v___jp_1147_:
{
lean_object* v_toEnvExtension_1148_; lean_object* v_asyncMode_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_snd_1152_; lean_object* v___x_1153_; 
v_toEnvExtension_1148_ = lean_ctor_get(v___x_1146_, 0);
v_asyncMode_1149_ = lean_ctor_get(v_toEnvExtension_1148_, 2);
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1145_, v___x_1146_, v_env_1143_, v_asyncMode_1149_, v___x_1150_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1152_, v_declName_1144_);
lean_dec(v_declName_1144_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1183_, v_x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1186_, v_x_1187_, v_x_1188_);
lean_dec(v_x_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1190_, lean_object* v_k_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1190_, v_k_1191_, v_x_1192_, v_x_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1196_, lean_object* v_k_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1196_, v_k_1197_, v_x_1198_, v_x_1199_, v_x_1200_);
lean_dec_ref(v_k_1197_);
lean_dec_ref(v_as_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1202_, lean_object* v_x_1203_, size_t v_x_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1203_, v_x_1204_, v_x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
size_t v_x_597__boxed_1211_; lean_object* v_res_1212_; 
v_x_597__boxed_1211_ = lean_unbox_usize(v_x_1209_);
lean_dec(v_x_1209_);
v_res_1212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1207_, v_x_1208_, v_x_597__boxed_1211_, v_x_1210_);
lean_dec(v_x_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1213_, lean_object* v_keys_1214_, lean_object* v_vals_1215_, lean_object* v_heq_1216_, lean_object* v_i_1217_, lean_object* v_k_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1214_, v_vals_1215_, v_i_1217_, v_k_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1220_, lean_object* v_keys_1221_, lean_object* v_vals_1222_, lean_object* v_heq_1223_, lean_object* v_i_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1220_, v_keys_1221_, v_vals_1222_, v_heq_1223_, v_i_1224_, v_k_1225_);
lean_dec(v_k_1225_);
lean_dec_ref(v_vals_1222_);
lean_dec_ref(v_keys_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1227_, lean_object* v_declName_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1230_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1227_, v_declName_1228_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; lean_object* v_toEnvExtension_1232_; lean_object* v_asyncMode_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1231_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1232_ = lean_ctor_get(v___x_1231_, 0);
v_asyncMode_1233_ = lean_ctor_get(v_toEnvExtension_1232_, 2);
v___x_1234_ = lean_box(0);
v___x_1235_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1229_, v___x_1231_, v_env_1227_, v_asyncMode_1233_, v___x_1234_);
v___x_1236_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1235_, v_declName_1228_);
lean_dec(v_declName_1228_);
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___y_1241_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_val_1237_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1237_);
lean_dec_ref(v___x_1230_);
v___x_1238_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1239_ = l_Lean_IR_declMapExt;
v___x_1255_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1238_, v___x_1239_, v_env_1227_, v_val_1237_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_get_size(v___x_1255_);
v___x_1258_ = lean_nat_dec_lt(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref(v___x_1255_);
v___x_1259_ = lean_box(0);
v___y_1241_ = v___x_1259_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_sub(v___x_1257_, v___x_1260_);
v___x_1262_ = lean_nat_dec_le(v___x_1256_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec(v___x_1261_);
lean_dec_ref(v___x_1255_);
v___x_1263_ = lean_box(0);
v___y_1241_ = v___x_1263_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_tmpDecl_1267_; lean_object* v___x_1268_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1265_ = lean_box(0);
v___x_1266_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1228_);
v_tmpDecl_1267_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1267_, 0, v_declName_1228_);
lean_ctor_set(v_tmpDecl_1267_, 1, v___x_1264_);
lean_ctor_set(v_tmpDecl_1267_, 2, v___x_1265_);
lean_ctor_set(v_tmpDecl_1267_, 3, v___x_1266_);
v___x_1268_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1255_, v_tmpDecl_1267_, v___x_1256_, v___x_1261_);
lean_dec_ref(v_tmpDecl_1267_);
lean_dec_ref(v___x_1255_);
if (lean_obj_tag(v___x_1268_) == 0)
{
v___y_1241_ = v___x_1268_;
goto v___jp_1240_;
}
else
{
lean_dec(v_val_1237_);
lean_dec(v_declName_1228_);
lean_dec_ref(v_env_1227_);
return v___x_1268_;
}
}
}
v___jp_1240_:
{
uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1242_ = 0;
v___x_1243_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1238_, v___x_1239_, v_env_1227_, v_val_1237_, v___x_1242_);
lean_dec(v_val_1237_);
lean_dec_ref(v_env_1227_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_array_get_size(v___x_1243_);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v___x_1243_);
lean_dec(v_declName_1228_);
return v___y_1241_;
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
lean_dec(v_declName_1228_);
return v___y_1241_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_tmpDecl_1253_; lean_object* v___x_1254_; 
lean_dec(v___y_1241_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_1253_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1253_, 0, v_declName_1228_);
lean_ctor_set(v_tmpDecl_1253_, 1, v___x_1250_);
lean_ctor_set(v_tmpDecl_1253_, 2, v___x_1251_);
lean_ctor_set(v_tmpDecl_1253_, 3, v___x_1252_);
v___x_1254_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1243_, v_tmpDecl_1253_, v___x_1244_, v___x_1248_);
lean_dec_ref(v_tmpDecl_1253_);
lean_dec_ref(v___x_1243_);
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1269_, lean_object* v_declName_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v_boxed_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc(v_declName_1270_);
v_boxed_1272_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1270_);
v___x_1273_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1269_, v_declName_1270_);
lean_dec(v_declName_1270_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; lean_object* v_toEnvExtension_1275_; lean_object* v_asyncMode_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1274_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1275_ = lean_ctor_get(v___x_1274_, 0);
v_asyncMode_1276_ = lean_ctor_get(v_toEnvExtension_1275_, 2);
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1271_, v___x_1274_, v_env_1269_, v_asyncMode_1276_, v___x_1277_);
v___x_1279_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1278_, v_boxed_1272_);
lean_dec(v_boxed_1272_);
return v___x_1279_;
}
else
{
lean_object* v_val_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___y_1284_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_val_1280_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1280_);
lean_dec_ref(v___x_1273_);
v___x_1281_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1282_ = l_Lean_IR_declMapExt;
v___x_1298_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1281_, v___x_1282_, v_env_1269_, v_val_1280_);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_array_get_size(v___x_1298_);
v___x_1301_ = lean_nat_dec_lt(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v___x_1298_);
v___x_1302_ = lean_box(0);
v___y_1284_ = v___x_1302_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_nat_sub(v___x_1300_, v___x_1303_);
v___x_1305_ = lean_nat_dec_le(v___x_1299_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v___x_1304_);
lean_dec_ref(v___x_1298_);
v___x_1306_ = lean_box(0);
v___y_1284_ = v___x_1306_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_tmpDecl_1310_; lean_object* v___x_1311_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1308_ = lean_box(0);
v___x_1309_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_boxed_1272_);
v_tmpDecl_1310_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1310_, 0, v_boxed_1272_);
lean_ctor_set(v_tmpDecl_1310_, 1, v___x_1307_);
lean_ctor_set(v_tmpDecl_1310_, 2, v___x_1308_);
lean_ctor_set(v_tmpDecl_1310_, 3, v___x_1309_);
v___x_1311_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1298_, v_tmpDecl_1310_, v___x_1299_, v___x_1304_);
lean_dec_ref(v_tmpDecl_1310_);
lean_dec_ref(v___x_1298_);
if (lean_obj_tag(v___x_1311_) == 0)
{
v___y_1284_ = v___x_1311_;
goto v___jp_1283_;
}
else
{
lean_dec(v_val_1280_);
lean_dec(v_boxed_1272_);
lean_dec_ref(v_env_1269_);
return v___x_1311_;
}
}
}
v___jp_1283_:
{
uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1285_ = 0;
v___x_1286_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1281_, v___x_1282_, v_env_1269_, v_val_1280_, v___x_1285_);
lean_dec(v_val_1280_);
lean_dec_ref(v_env_1269_);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_array_get_size(v___x_1286_);
v___x_1289_ = lean_nat_dec_lt(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v___x_1286_);
lean_dec(v_boxed_1272_);
return v___y_1284_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_sub(v___x_1288_, v___x_1290_);
v___x_1292_ = lean_nat_dec_le(v___x_1287_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1286_);
lean_dec(v_boxed_1272_);
return v___y_1284_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_tmpDecl_1296_; lean_object* v___x_1297_; 
lean_dec(v___y_1284_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_1296_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1296_, 0, v_boxed_1272_);
lean_ctor_set(v_tmpDecl_1296_, 1, v___x_1293_);
lean_ctor_set(v_tmpDecl_1296_, 2, v___x_1294_);
lean_ctor_set(v_tmpDecl_1296_, 3, v___x_1295_);
v___x_1297_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1286_, v_tmpDecl_1296_, v___x_1287_, v___x_1291_);
lean_dec_ref(v_tmpDecl_1296_);
lean_dec_ref(v___x_1286_);
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1312_, lean_object* v_constName_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1312_, v_constName_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; lean_object* v_toEnvExtension_1316_; lean_object* v_asyncMode_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1315_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1316_ = lean_ctor_get(v___x_1315_, 0);
v_asyncMode_1317_ = lean_ctor_get(v_toEnvExtension_1316_, 2);
v___x_1318_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1319_ = lean_box(0);
v___x_1320_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1318_, v___x_1315_, v_env_1312_, v_asyncMode_1317_, v___x_1319_);
v___x_1321_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1320_, v_constName_1313_);
lean_dec(v_constName_1313_);
lean_dec(v___x_1320_);
if (v___x_1321_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = 1;
return v___x_1322_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
return v___x_1323_;
}
}
else
{
uint8_t v___x_1324_; 
lean_dec_ref(v___x_1314_);
lean_dec(v_constName_1313_);
lean_dec_ref(v_env_1312_);
v___x_1324_ = 0;
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1325_, lean_object* v_constName_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = lean_has_compile_error(v_env_1325_, v_constName_1326_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v_env_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_st_ref_get(v_a_1330_);
v_env_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_ref(v_env_1333_);
lean_dec(v___x_1332_);
v___x_1334_ = l_Lean_IR_findEnvDecl(v_env_1333_, v_n_1329_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_IR_findDecl___redArg(v_n_1336_, v_a_1337_);
lean_dec(v_a_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_IR_findDecl___redArg(v_n_1340_, v_a_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_IR_findDecl(v_n_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1368_; 
v___x_1353_ = l_Lean_IR_findDecl___redArg(v_n_1350_, v_a_1351_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
if (lean_obj_tag(v_a_1354_) == 0)
{
uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1358_ = 0;
v___x_1359_ = lean_box(v___x_1358_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1359_);
v___x_1361_ = v___x_1356_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec_ref(v_a_1354_);
v___x_1363_ = 1;
v___x_1364_ = lean_box(v___x_1363_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1364_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_IR_containsDecl___redArg(v_n_1369_, v_a_1370_);
lean_dec(v_a_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_IR_containsDecl___redArg(v_n_1373_, v_a_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_IR_containsDecl(v_n_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_ref_1387_; lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_ref_1387_ = lean_ctor_get(v___y_1384_, 5);
v___x_1388_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1383_, v___y_1384_, v___y_1385_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_inc(v_ref_1387_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_ref_1387_);
lean_ctor_set(v___x_1393_, 1, v_a_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 1);
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1427_; 
lean_inc(v_n_1405_);
v___x_1409_ = l_Lean_IR_findDecl___redArg(v_n_1405_, v_a_1407_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
if (lean_obj_tag(v_a_1410_) == 1)
{
lean_object* v_val_1414_; lean_object* v___x_1416_; 
lean_dec(v_n_1405_);
v_val_1414_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_val_1414_);
lean_dec_ref(v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v_val_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_val_1414_);
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
lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_del_object(v___x_1412_);
lean_dec(v_a_1410_);
v___x_1418_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1419_ = 1;
v___x_1420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1405_, v___x_1419_);
v___x_1421_ = lean_string_append(v___x_1418_, v___x_1420_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
v___x_1425_ = l_Lean_MessageData_ofFormat(v___x_1424_);
v___x_1426_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1425_, v_a_1406_, v_a_1407_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_IR_getDecl(v_n_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1433_, lean_object* v_msg_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1439_, v_msg_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v_env_1449_; lean_object* v___x_1450_; lean_object* v_toEnvExtension_1451_; lean_object* v_asyncMode_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1448_ = lean_st_ref_get(v_a_1446_);
v_env_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_ref(v_env_1449_);
lean_dec(v___x_1448_);
v___x_1450_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1451_ = lean_ctor_get(v___x_1450_, 0);
v_asyncMode_1452_ = lean_ctor_get(v_toEnvExtension_1451_, 2);
v___x_1453_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1453_, v___x_1450_, v_env_1449_, v_asyncMode_1452_, v___x_1454_);
v___x_1456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1455_, v_n_1445_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_IR_findLocalDecl___redArg(v_n_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec(v_n_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_IR_findLocalDecl___redArg(v_n_1462_, v_a_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_IR_findLocalDecl(v_n_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_n_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v_toEnvExtension_1474_; lean_object* v_asyncMode_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1473_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1474_ = lean_ctor_get(v___x_1473_, 0);
v_asyncMode_1475_ = lean_ctor_get(v_toEnvExtension_1474_, 2);
v___x_1476_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1477_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1476_, v___x_1473_, v_env_1472_, v_asyncMode_1475_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v_env_1487_; lean_object* v_nextMacroScope_1488_; lean_object* v_ngen_1489_; lean_object* v_auxDeclNGen_1490_; lean_object* v_traceState_1491_; lean_object* v_messages_1492_; lean_object* v_infoState_1493_; lean_object* v_snapshotTasks_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1510_; 
v___x_1486_ = lean_st_ref_take(v_a_1484_);
v_env_1487_ = lean_ctor_get(v___x_1486_, 0);
v_nextMacroScope_1488_ = lean_ctor_get(v___x_1486_, 1);
v_ngen_1489_ = lean_ctor_get(v___x_1486_, 2);
v_auxDeclNGen_1490_ = lean_ctor_get(v___x_1486_, 3);
v_traceState_1491_ = lean_ctor_get(v___x_1486_, 4);
v_messages_1492_ = lean_ctor_get(v___x_1486_, 6);
v_infoState_1493_ = lean_ctor_get(v___x_1486_, 7);
v_snapshotTasks_1494_ = lean_ctor_get(v___x_1486_, 8);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v___x_1486_, 5);
lean_dec(v_unused_1511_);
v___x_1496_ = v___x_1486_;
v_isShared_1497_ = v_isSharedCheck_1510_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snapshotTasks_1494_);
lean_inc(v_infoState_1493_);
lean_inc(v_messages_1492_);
lean_inc(v_traceState_1491_);
lean_inc(v_auxDeclNGen_1490_);
lean_inc(v_ngen_1489_);
lean_inc(v_nextMacroScope_1488_);
lean_inc(v_env_1487_);
lean_dec(v___x_1486_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1510_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v_toEnvExtension_1499_; lean_object* v_asyncMode_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1498_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1499_ = lean_ctor_get(v___x_1498_, 0);
v_asyncMode_1500_ = lean_ctor_get(v_toEnvExtension_1499_, 2);
v___x_1501_ = lean_box(0);
v___x_1502_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1498_, v_env_1487_, v_decl_1483_, v_asyncMode_1500_, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 5, v___x_1503_);
lean_ctor_set(v___x_1496_, 0, v___x_1502_);
v___x_1505_ = v___x_1496_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_nextMacroScope_1488_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_ngen_1489_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_auxDeclNGen_1490_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_traceState_1491_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1509_, 6, v_messages_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 7, v_infoState_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 8, v_snapshotTasks_1494_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_st_ref_set(v_a_1484_, v___x_1505_);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_IR_addDecl___redArg(v_decl_1512_, v_a_1513_);
lean_dec(v_a_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_IR_addDecl___redArg(v_decl_1516_, v_a_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_IR_addDecl(v_decl_1521_, v_a_1522_, v_a_1523_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1526_, size_t v_i_1527_, size_t v_stop_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_usize_dec_eq(v_i_1527_, v_stop_1528_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_array_uget_borrowed(v_as_1526_, v_i_1527_);
lean_inc(v___x_1533_);
v___x_1534_ = l_Lean_IR_addDecl___redArg(v___x_1533_, v___y_1530_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; size_t v___x_1536_; size_t v___x_1537_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_add(v_i_1527_, v___x_1536_);
v_i_1527_ = v___x_1537_;
v_b_1529_ = v_a_1535_;
goto _start;
}
else
{
return v___x_1534_;
}
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_b_1529_);
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1540_, lean_object* v_i_1541_, lean_object* v_stop_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
size_t v_i_boxed_1546_; size_t v_stop_boxed_1547_; lean_object* v_res_1548_; 
v_i_boxed_1546_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_stop_boxed_1547_ = lean_unbox_usize(v_stop_1542_);
lean_dec(v_stop_1542_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1540_, v_i_boxed_1546_, v_stop_boxed_1547_, v_b_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v_as_1540_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_get_size(v_decls_1549_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
return v___x_1557_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_nat_dec_le(v___x_1554_, v___x_1554_);
if (v___x_1558_ == 0)
{
if (v___x_1556_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1555_);
return v___x_1559_;
}
else
{
size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = lean_usize_of_nat(v___x_1554_);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1549_, v___x_1560_, v___x_1561_, v___x_1555_, v_a_1551_);
return v___x_1562_;
}
}
else
{
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = lean_usize_of_nat(v___x_1554_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1549_, v___x_1563_, v___x_1564_, v___x_1555_, v_a_1551_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_IR_addDecls(v_decls_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec_ref(v_decls_1566_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1571_, size_t v_i_1572_, size_t v_stop_1573_, lean_object* v_b_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1571_, v_i_1572_, v_stop_1573_, v_b_1574_, v___y_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1579_, lean_object* v_i_1580_, lean_object* v_stop_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
size_t v_i_boxed_1586_; size_t v_stop_boxed_1587_; lean_object* v_res_1588_; 
v_i_boxed_1586_ = lean_unbox_usize(v_i_1580_);
lean_dec(v_i_1580_);
v_stop_boxed_1587_ = lean_unbox_usize(v_stop_1581_);
lean_dec(v_stop_1581_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1579_, v_i_boxed_1586_, v_stop_boxed_1587_, v_b_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v_as_1579_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1592_, lean_object* v_as_1593_, size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_b_1596_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
if (v___x_1597_ == 0)
{
lean_inc_ref(v_b_1596_);
return v_b_1596_;
}
else
{
lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1598_ = lean_box(0);
v_a_1599_ = lean_array_uget_borrowed(v_as_1593_, v_i_1595_);
v___x_1600_ = l_Lean_IR_Decl_name(v_a_1599_);
v___x_1601_ = lean_name_eq(v___x_1600_, v_n_1592_);
lean_dec(v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; 
v___x_1602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_add(v_i_1595_, v___x_1603_);
v_i_1595_ = v___x_1604_;
v_b_1596_ = v___x_1602_;
goto _start;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_inc(v_a_1599_);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1599_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v___x_1598_);
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1609_, lean_object* v_as_1610_, lean_object* v_sz_1611_, lean_object* v_i_1612_, lean_object* v_b_1613_){
_start:
{
size_t v_sz_boxed_1614_; size_t v_i_boxed_1615_; lean_object* v_res_1616_; 
v_sz_boxed_1614_ = lean_unbox_usize(v_sz_1611_);
lean_dec(v_sz_1611_);
v_i_boxed_1615_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1609_, v_as_1610_, v_sz_boxed_1614_, v_i_boxed_1615_, v_b_1613_);
lean_dec_ref(v_b_1613_);
lean_dec_ref(v_as_1610_);
lean_dec(v_n_1609_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1617_, lean_object* v_n_1618_, lean_object* v_decls_1619_){
_start:
{
lean_object* v___x_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; lean_object* v_fst_1624_; 
v___x_1620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1621_ = lean_array_size(v_decls_1619_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1618_, v_decls_1619_, v_sz_1621_, v___x_1622_, v___x_1620_);
v_fst_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_fst_1624_);
lean_dec_ref(v___x_1623_);
if (lean_obj_tag(v_fst_1624_) == 0)
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_IR_findEnvDecl(v_env_1617_, v_n_1618_);
return v___x_1625_;
}
else
{
lean_object* v_val_1626_; 
v_val_1626_ = lean_ctor_get(v_fst_1624_, 0);
lean_inc(v_val_1626_);
lean_dec_ref(v_fst_1624_);
if (lean_obj_tag(v_val_1626_) == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_IR_findEnvDecl(v_env_1617_, v_n_1618_);
return v___x_1627_;
}
else
{
lean_dec(v_n_1618_);
lean_dec_ref(v_env_1617_);
return v_val_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1628_, lean_object* v_n_1629_, lean_object* v_decls_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_IR_findEnvDecl_x27(v_env_1628_, v_n_1629_, v_decls_1630_);
lean_dec_ref(v_decls_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1632_, lean_object* v_decls_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v_env_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1636_ = lean_st_ref_get(v_a_1634_);
v_env_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc_ref(v_env_1637_);
lean_dec(v___x_1636_);
v___x_1638_ = l_Lean_IR_findEnvDecl_x27(v_env_1637_, v_n_1632_, v_decls_1633_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1640_, lean_object* v_decls_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_IR_findDecl_x27___redArg(v_n_1640_, v_decls_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_decls_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1645_, lean_object* v_decls_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_IR_findDecl_x27___redArg(v_n_1645_, v_decls_1646_, v_a_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1651_, lean_object* v_decls_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_IR_findDecl_x27(v_n_1651_, v_decls_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_decls_1652_);
return v_res_1656_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1657_, lean_object* v_as_1658_, size_t v_i_1659_, size_t v_stop_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_eq(v_i_1659_, v_stop_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1662_ = lean_array_uget_borrowed(v_as_1658_, v_i_1659_);
v___x_1663_ = l_Lean_IR_Decl_name(v___x_1662_);
v___x_1664_ = lean_name_eq(v___x_1663_, v_n_1657_);
lean_dec(v___x_1663_);
if (v___x_1664_ == 0)
{
size_t v___x_1665_; size_t v___x_1666_; 
v___x_1665_ = ((size_t)1ULL);
v___x_1666_ = lean_usize_add(v_i_1659_, v___x_1665_);
v_i_1659_ = v___x_1666_;
goto _start;
}
else
{
return v___x_1664_;
}
}
else
{
uint8_t v___x_1668_; 
v___x_1668_ = 0;
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1669_, lean_object* v_as_1670_, lean_object* v_i_1671_, lean_object* v_stop_1672_){
_start:
{
size_t v_i_boxed_1673_; size_t v_stop_boxed_1674_; uint8_t v_res_1675_; lean_object* v_r_1676_; 
v_i_boxed_1673_ = lean_unbox_usize(v_i_1671_);
lean_dec(v_i_1671_);
v_stop_boxed_1674_ = lean_unbox_usize(v_stop_1672_);
lean_dec(v_stop_1672_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1669_, v_as_1670_, v_i_boxed_1673_, v_stop_boxed_1674_);
lean_dec_ref(v_as_1670_);
lean_dec(v_n_1669_);
v_r_1676_ = lean_box(v_res_1675_);
return v_r_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1677_, lean_object* v_decls_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_array_get_size(v_decls_1678_);
v___x_1683_ = lean_nat_dec_lt(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_IR_containsDecl___redArg(v_n_1677_, v_a_1679_);
return v___x_1684_;
}
else
{
if (v___x_1683_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_IR_containsDecl___redArg(v_n_1677_, v_a_1679_);
return v___x_1685_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_of_nat(v___x_1682_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1677_, v_decls_1678_, v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_IR_containsDecl___redArg(v_n_1677_, v_a_1679_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_n_1677_);
v___x_1690_ = lean_box(v___x_1688_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1692_, lean_object* v_decls_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1692_, v_decls_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_decls_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1697_, lean_object* v_decls_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1697_, v_decls_1698_, v_a_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1703_, lean_object* v_decls_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_IR_containsDecl_x27(v_n_1703_, v_decls_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec_ref(v_decls_1704_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1709_, lean_object* v_decls_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1732_; 
lean_inc(v_n_1709_);
v___x_1714_ = l_Lean_IR_findDecl_x27___redArg(v_n_1709_, v_decls_1710_, v_a_1712_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1732_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1732_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
if (lean_obj_tag(v_a_1715_) == 1)
{
lean_object* v_val_1719_; lean_object* v___x_1721_; 
lean_dec(v_n_1709_);
v_val_1719_ = lean_ctor_get(v_a_1715_, 0);
lean_inc(v_val_1719_);
lean_dec_ref(v_a_1715_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_val_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_val_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
else
{
lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_del_object(v___x_1717_);
lean_dec(v_a_1715_);
v___x_1723_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1724_ = 1;
v___x_1725_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1709_, v___x_1724_);
v___x_1726_ = lean_string_append(v___x_1723_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___x_1730_ = l_Lean_MessageData_ofFormat(v___x_1729_);
v___x_1731_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1730_, v_a_1711_, v_a_1712_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1733_, lean_object* v_decls_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_IR_getDecl_x27(v_n_1733_, v_decls_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec_ref(v_decls_1734_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1739_, lean_object* v_declName_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_IR_findEnvDecl(v_env_1739_, v_declName_1740_);
if (lean_obj_tag(v___x_1741_) == 1)
{
lean_object* v_val_1742_; 
v_val_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_val_1742_);
lean_dec_ref(v___x_1741_);
if (lean_obj_tag(v_val_1742_) == 0)
{
lean_object* v_info_1743_; 
v_info_1743_ = lean_ctor_get(v_val_1742_, 4);
lean_inc(v_info_1743_);
lean_dec_ref(v_val_1742_);
return v_info_1743_;
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_val_1742_);
v___x_1744_ = lean_box(0);
return v___x_1744_;
}
}
else
{
lean_object* v___x_1745_; 
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1746_, uint8_t v_level_1747_, uint8_t v_includeDecls_1748_, lean_object* v_as_1749_, size_t v_i_1750_, size_t v_stop_1751_, lean_object* v_b_1752_){
_start:
{
lean_object* v___y_1754_; uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_eq(v_i_1750_, v_stop_1751_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___y_1761_; 
v___x_1759_ = lean_array_uget_borrowed(v_as_1749_, v_i_1750_);
if (v_includeDecls_1748_ == 0)
{
uint8_t v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = 1;
lean_inc(v___x_1759_);
lean_inc_ref(v_env_1746_);
v___x_1770_ = l_Lean_Environment_contains(v_env_1746_, v___x_1759_, v___x_1769_);
if (v___x_1770_ == 0)
{
goto v___jp_1765_;
}
else
{
v___y_1754_ = v_b_1752_;
goto v___jp_1753_;
}
}
else
{
goto v___jp_1765_;
}
v___jp_1760_:
{
if (v___y_1761_ == 0)
{
uint8_t v___x_1762_; 
lean_inc_ref(v_env_1746_);
v___x_1762_ = l_Lean_isDeclMeta(v_env_1746_, v___x_1759_);
if (v___x_1762_ == 0)
{
v___y_1754_ = v_b_1752_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1763_; 
lean_inc(v___x_1759_);
v___x_1763_ = lean_array_push(v_b_1752_, v___x_1759_);
v___y_1754_ = v___x_1763_;
goto v___jp_1753_;
}
}
else
{
lean_object* v___x_1764_; 
lean_inc(v___x_1759_);
v___x_1764_ = lean_array_push(v_b_1752_, v___x_1759_);
v___y_1754_ = v___x_1764_;
goto v___jp_1753_;
}
}
v___jp_1765_:
{
uint8_t v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = 2;
v___x_1767_ = l_Lean_instDecidableEqOLeanLevel(v_level_1747_, v___x_1766_);
if (v___x_1767_ == 0)
{
uint8_t v___x_1768_; 
lean_inc_ref(v_env_1746_);
v___x_1768_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1746_, v___x_1759_);
v___y_1761_ = v___x_1768_;
goto v___jp_1760_;
}
else
{
v___y_1761_ = v___x_1767_;
goto v___jp_1760_;
}
}
}
else
{
lean_dec_ref(v_env_1746_);
return v_b_1752_;
}
v___jp_1753_:
{
size_t v___x_1755_; size_t v___x_1756_; 
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1750_, v___x_1755_);
v_i_1750_ = v___x_1756_;
v_b_1752_ = v___y_1754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1771_, lean_object* v_level_1772_, lean_object* v_includeDecls_1773_, lean_object* v_as_1774_, lean_object* v_i_1775_, lean_object* v_stop_1776_, lean_object* v_b_1777_){
_start:
{
uint8_t v_level_boxed_1778_; uint8_t v_includeDecls_boxed_1779_; size_t v_i_boxed_1780_; size_t v_stop_boxed_1781_; lean_object* v_res_1782_; 
v_level_boxed_1778_ = lean_unbox(v_level_1772_);
v_includeDecls_boxed_1779_ = lean_unbox(v_includeDecls_1773_);
v_i_boxed_1780_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_stop_boxed_1781_ = lean_unbox_usize(v_stop_1776_);
lean_dec(v_stop_1776_);
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1771_, v_level_boxed_1778_, v_includeDecls_boxed_1779_, v_as_1774_, v_i_boxed_1780_, v_stop_boxed_1781_, v_b_1777_);
lean_dec_ref(v_as_1774_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1783_, size_t v_i_1784_, lean_object* v_bs_1785_){
_start:
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_usize_dec_lt(v_i_1784_, v_sz_1783_);
if (v___x_1786_ == 0)
{
return v_bs_1785_;
}
else
{
lean_object* v_v_1787_; lean_object* v___x_1788_; lean_object* v_bs_x27_1789_; lean_object* v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; lean_object* v___x_1793_; 
v_v_1787_ = lean_array_uget(v_bs_1785_, v_i_1784_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v_bs_x27_1789_ = lean_array_uset(v_bs_1785_, v_i_1784_, v___x_1788_);
v___x_1790_ = l_Lean_IR_Decl_name(v_v_1787_);
lean_dec(v_v_1787_);
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_add(v_i_1784_, v___x_1791_);
v___x_1793_ = lean_array_uset(v_bs_x27_1789_, v_i_1784_, v___x_1790_);
v_i_1784_ = v___x_1792_;
v_bs_1785_ = v___x_1793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_bs_1797_){
_start:
{
size_t v_sz_boxed_1798_; size_t v_i_boxed_1799_; lean_object* v_res_1800_; 
v_sz_boxed_1798_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1799_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1798_, v_i_boxed_1799_, v_bs_1797_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1803_, uint8_t v_level_1804_, uint8_t v_includeDecls_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v_toEnvExtension_1807_; lean_object* v_asyncMode_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; size_t v_sz_1812_; size_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1806_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1807_ = lean_ctor_get(v___x_1806_, 0);
v_asyncMode_1808_ = lean_ctor_get(v_toEnvExtension_1807_, 2);
v___x_1809_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc_ref(v_env_1803_);
v___x_1810_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1809_, v___x_1806_, v_env_1803_, v_asyncMode_1808_);
v___x_1811_ = lean_array_mk(v___x_1810_);
v_sz_1812_ = lean_array_size(v___x_1811_);
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1812_, v___x_1813_, v___x_1811_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v___x_1814_);
v___x_1817_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1818_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1818_ == 0)
{
lean_dec_ref(v___x_1814_);
lean_dec_ref(v_env_1803_);
return v___x_1817_;
}
else
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_nat_dec_le(v___x_1816_, v___x_1816_);
if (v___x_1819_ == 0)
{
if (v___x_1818_ == 0)
{
lean_dec_ref(v___x_1814_);
lean_dec_ref(v_env_1803_);
return v___x_1817_;
}
else
{
size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_usize_of_nat(v___x_1816_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1803_, v_level_1804_, v_includeDecls_1805_, v___x_1814_, v___x_1813_, v___x_1820_, v___x_1817_);
lean_dec_ref(v___x_1814_);
return v___x_1821_;
}
}
else
{
size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_usize_of_nat(v___x_1816_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1803_, v_level_1804_, v_includeDecls_1805_, v___x_1814_, v___x_1813_, v___x_1822_, v___x_1817_);
lean_dec_ref(v___x_1814_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1824_, lean_object* v_level_1825_, lean_object* v_includeDecls_1826_){
_start:
{
uint8_t v_level_boxed_1827_; uint8_t v_includeDecls_boxed_1828_; lean_object* v_res_1829_; 
v_level_boxed_1827_ = lean_unbox(v_level_1825_);
v_includeDecls_boxed_1828_ = lean_unbox(v_includeDecls_1826_);
v_res_1829_ = lean_get_ir_extra_const_names(v_env_1824_, v_level_boxed_1827_, v_includeDecls_boxed_1828_);
return v_res_1829_;
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
res = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
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
