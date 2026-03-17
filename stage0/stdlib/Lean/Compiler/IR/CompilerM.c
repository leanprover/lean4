// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: public import Lean.Compiler.IR.Format public import Lean.Compiler.ExportAttr public import Lean.Compiler.LCNF.PublicDeclsExt import Lean.Compiler.InitAttr import Init.Data.Format.Macro import Lean.Compiler.LCNF.Types
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
lean_object* lean_get_export_name_for(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExternAttrData_default;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
size_t lean_array_size(lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 186, 94, 176, 136, 38, 52, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_IR_log___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 220, 115, 150, 240, 139, 111, 12)}};
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 236, 150, 45, 29, 146, 124, 106)}};
static const lean_object* l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_471_, lean_object* v___y_472_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_476_, v___y_477_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v___y_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_481_, lean_object* v_lo_482_, lean_object* v_hi_483_){
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
v___f_485_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___closed__0));
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
v___x_490_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(v_snd_488_, v_lo_482_, v_fst_487_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_494_, lean_object* v_lo_495_, lean_object* v_hi_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(v_as_494_, v_lo_495_, v_hi_496_);
lean_dec(v_hi_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__1(lean_object* v_x_498_, lean_object* v_x_499_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_510_, lean_object* v_as_511_, size_t v_i_512_, size_t v_stop_513_, lean_object* v_b_514_){
_start:
{
lean_object* v___y_516_; uint8_t v___x_520_; 
v___x_520_ = lean_usize_dec_eq(v_i_512_, v_stop_513_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_array_uget_borrowed(v_as_511_, v_i_512_);
v___x_522_ = l_Lean_IR_Decl_name(v___x_521_);
lean_inc_ref(v_env_510_);
v___x_523_ = l_Lean_isDeclMeta(v_env_510_, v___x_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
lean_inc_ref(v_env_510_);
v___x_524_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_510_, v___x_522_);
lean_dec(v___x_522_);
if (v___x_524_ == 0)
{
v___y_516_ = v_b_514_;
goto v___jp_515_;
}
else
{
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_f_525_; lean_object* v_xs_526_; lean_object* v_type_527_; lean_object* v___x_532_; 
v_f_525_ = lean_ctor_get(v___x_521_, 0);
v_xs_526_ = lean_ctor_get(v___x_521_, 1);
v_type_527_ = lean_ctor_get(v___x_521_, 2);
lean_inc(v_f_525_);
lean_inc_ref(v_env_510_);
v___x_532_ = lean_get_export_name_for(v_env_510_, v_f_525_);
if (lean_obj_tag(v___x_532_) == 1)
{
lean_object* v_val_533_; 
v_val_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref(v___x_532_);
if (lean_obj_tag(v_val_533_) == 1)
{
lean_object* v_str_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_str_534_ = lean_ctor_get(v_val_533_, 1);
lean_inc_ref(v_str_534_);
lean_dec_ref(v_val_533_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v_str_534_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_inc(v_type_527_);
lean_inc_ref(v_xs_526_);
lean_inc(v_f_525_);
v___x_539_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_539_, 0, v_f_525_);
lean_ctor_set(v___x_539_, 1, v_xs_526_);
lean_ctor_set(v___x_539_, 2, v_type_527_);
lean_ctor_set(v___x_539_, 3, v___x_538_);
v___x_540_ = lean_array_push(v_b_514_, v___x_539_);
v___y_516_ = v___x_540_;
goto v___jp_515_;
}
else
{
lean_dec(v_val_533_);
goto v___jp_528_;
}
}
else
{
lean_dec(v___x_532_);
goto v___jp_528_;
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___closed__0));
lean_inc(v_type_527_);
lean_inc_ref(v_xs_526_);
lean_inc(v_f_525_);
v___x_530_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_530_, 0, v_f_525_);
lean_ctor_set(v___x_530_, 1, v_xs_526_);
lean_ctor_set(v___x_530_, 2, v_type_527_);
lean_ctor_set(v___x_530_, 3, v___x_529_);
v___x_531_ = lean_array_push(v_b_514_, v___x_530_);
v___y_516_ = v___x_531_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_541_; 
lean_inc(v___x_521_);
v___x_541_ = lean_array_push(v_b_514_, v___x_521_);
v___y_516_ = v___x_541_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v___x_542_; 
lean_dec(v___x_522_);
lean_inc(v___x_521_);
v___x_542_ = lean_array_push(v_b_514_, v___x_521_);
v___y_516_ = v___x_542_;
goto v___jp_515_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_543_, lean_object* v_as_544_, lean_object* v_i_545_, lean_object* v_stop_546_, lean_object* v_b_547_){
_start:
{
size_t v_i_boxed_548_; size_t v_stop_boxed_549_; lean_object* v_res_550_; 
v_i_boxed_548_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_stop_boxed_549_ = lean_unbox_usize(v_stop_546_);
lean_dec(v_stop_546_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0(v_env_543_, v_as_544_, v_i_boxed_548_, v_stop_boxed_549_, v_b_547_);
lean_dec_ref(v_as_544_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0(lean_object* v_env_553_, lean_object* v_as_554_, lean_object* v_start_555_, lean_object* v_stop_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___closed__0));
v___x_558_ = lean_nat_dec_lt(v_start_555_, v_stop_556_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_env_553_);
return v___x_557_;
}
else
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_as_554_);
v___x_560_ = lean_nat_dec_le(v_stop_556_, v___x_559_);
if (v___x_560_ == 0)
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_lt(v_start_555_, v___x_559_);
if (v___x_561_ == 0)
{
lean_dec_ref(v_env_553_);
return v___x_557_;
}
else
{
size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_usize_of_nat(v_start_555_);
v___x_563_ = lean_usize_of_nat(v___x_559_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0(v_env_553_, v_as_554_, v___x_562_, v___x_563_, v___x_557_);
return v___x_564_;
}
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_usize_of_nat(v_start_555_);
v___x_566_ = lean_usize_of_nat(v_stop_556_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0_spec__0(v_env_553_, v_as_554_, v___x_565_, v___x_566_, v___x_557_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_568_, lean_object* v_as_569_, lean_object* v_start_570_, lean_object* v_stop_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0(v_env_568_, v_as_569_, v_start_570_, v_stop_571_);
lean_dec(v_stop_571_);
lean_dec(v_start_570_);
lean_dec_ref(v_as_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object* v_env_573_, lean_object* v_s_574_, lean_object* v_entries_575_, uint8_t v_x_576_){
_start:
{
lean_object* v___y_578_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_decls_586_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___closed__0));
v_decls_586_ = l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__1(v___x_585_, v_entries_575_);
v___x_591_ = lean_array_get_size(v_decls_586_);
v___x_592_ = lean_nat_dec_eq(v___x_591_, v___x_584_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___y_596_; uint8_t v___x_598_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_sub(v___x_591_, v___x_593_);
v___x_598_ = lean_nat_dec_le(v___x_584_, v___x_594_);
if (v___x_598_ == 0)
{
lean_inc(v___x_594_);
v___y_596_ = v___x_594_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_584_;
goto v___jp_595_;
}
v___jp_595_:
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_le(v___y_596_, v___x_594_);
if (v___x_597_ == 0)
{
lean_dec(v___x_594_);
lean_inc(v___y_596_);
v___y_588_ = v___y_596_;
v___y_589_ = v___y_596_;
goto v___jp_587_;
}
else
{
v___y_588_ = v___y_596_;
v___y_589_ = v___x_594_;
goto v___jp_587_;
}
}
}
else
{
v___y_578_ = v_decls_586_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v___x_579_; uint8_t v_isModule_580_; 
v___x_579_ = l_Lean_Environment_header(v_env_573_);
v_isModule_580_ = lean_ctor_get_uint8(v___x_579_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_579_);
if (v_isModule_580_ == 0)
{
lean_dec_ref(v_env_573_);
return v___y_578_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_array_get_size(v___y_578_);
v___x_583_ = l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0(v_env_573_, v___y_578_, v___x_581_, v___x_582_);
lean_dec_ref(v___y_578_);
return v___x_583_;
}
}
v___jp_587_:
{
lean_object* v___x_590_; 
v___x_590_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(v_decls_586_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
v___y_578_ = v___x_590_;
goto v___jp_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object* v_env_599_, lean_object* v_s_600_, lean_object* v_entries_601_, lean_object* v_x_602_){
_start:
{
uint8_t v_x_2062__boxed_603_; lean_object* v_res_604_; 
v_x_2062__boxed_603_ = lean_unbox(v_x_602_);
v_res_604_ = l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(v_env_599_, v_s_600_, v_entries_601_, v_x_2062__boxed_603_);
lean_dec_ref(v_s_600_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object* v_es_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_array_mk(v_es_605_);
return v___x_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_keys_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_607_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v___x_611_;
}
else
{
lean_object* v_k_x27_612_; uint8_t v___x_613_; 
v_k_x27_612_ = lean_array_fget_borrowed(v_keys_607_, v_i_608_);
v___x_613_ = lean_name_eq(v_k_609_, v_k_x27_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_add(v_i_608_, v___x_614_);
lean_dec(v_i_608_);
v_i_608_ = v___x_615_;
goto _start;
}
else
{
lean_dec(v_i_608_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_keys_617_, lean_object* v_i_618_, lean_object* v_k_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_keys_617_, v_i_618_, v_k_619_);
lean_dec(v_k_619_);
lean_dec_ref(v_keys_617_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_622_; size_t v___x_623_; size_t v___x_624_; 
v___x_622_ = ((size_t)5ULL);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_shift_left(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; 
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0);
v___x_627_ = lean_usize_sub(v___x_626_, v___x_625_);
return v___x_627_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_x_628_, size_t v_x_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v_es_631_; lean_object* v___x_632_; size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v_j_636_; lean_object* v___x_637_; 
v_es_631_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_es_631_);
lean_dec_ref(v_x_628_);
v___x_632_ = lean_box(2);
v___x_633_ = ((size_t)5ULL);
v___x_634_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_635_ = lean_usize_land(v_x_629_, v___x_634_);
v_j_636_ = lean_usize_to_nat(v___x_635_);
v___x_637_ = lean_array_get(v___x_632_, v_es_631_, v_j_636_);
lean_dec(v_j_636_);
lean_dec_ref(v_es_631_);
switch(lean_obj_tag(v___x_637_))
{
case 0:
{
lean_object* v_key_638_; uint8_t v___x_639_; 
v_key_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_key_638_);
lean_dec_ref(v___x_637_);
v___x_639_ = lean_name_eq(v_x_630_, v_key_638_);
lean_dec(v_key_638_);
return v___x_639_;
}
case 1:
{
lean_object* v_node_640_; size_t v___x_641_; 
v_node_640_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_node_640_);
lean_dec_ref(v___x_637_);
v___x_641_ = lean_usize_shift_right(v_x_629_, v___x_633_);
v_x_628_ = v_node_640_;
v_x_629_ = v___x_641_;
goto _start;
}
default: 
{
uint8_t v___x_643_; 
v___x_643_ = 0;
return v___x_643_;
}
}
}
else
{
lean_object* v_ks_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_ks_644_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_ks_644_);
lean_dec_ref(v_x_628_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ks_644_, v___x_645_, v_x_630_);
lean_dec_ref(v_ks_644_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
size_t v_x_2132__boxed_650_; uint8_t v_res_651_; lean_object* v_r_652_; 
v_x_2132__boxed_650_ = lean_unbox_usize(v_x_648_);
lean_dec(v_x_648_);
v_res_651_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_647_, v_x_2132__boxed_650_, v_x_649_);
lean_dec(v_x_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_653_; uint64_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1723u);
v___x_654_ = lean_uint64_of_nat(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint64_t v___y_658_; 
if (lean_obj_tag(v_x_656_) == 0)
{
uint64_t v___x_661_; 
v___x_661_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_658_ = v___x_661_;
goto v___jp_657_;
}
else
{
uint64_t v_hash_662_; 
v_hash_662_ = lean_ctor_get_uint64(v_x_656_, sizeof(void*)*2);
v___y_658_ = v_hash_662_;
goto v___jp_657_;
}
v___jp_657_:
{
size_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_uint64_to_usize(v___y_658_);
v___x_660_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_655_, v___x_659_, v_x_656_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg(v_x_663_, v_x_664_);
lean_dec(v_x_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object* v_x1_667_, lean_object* v_x2_668_){
_start:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = l_Lean_IR_Decl_name(v_x2_668_);
v___x_670_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg(v_x1_667_, v___x_669_);
lean_dec(v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = 1;
return v___x_671_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = 0;
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object* v_x1_673_, lean_object* v_x2_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(v_x1_673_, v_x2_674_);
lean_dec_ref(v_x2_674_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_677_;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_, &l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__once, _init_l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_, &l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__once, _init_l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(v_x_682_);
lean_dec_ref(v_x_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_ks_688_; lean_object* v_vs_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_713_; 
v_ks_688_ = lean_ctor_get(v_x_684_, 0);
v_vs_689_ = lean_ctor_get(v_x_684_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_713_ == 0)
{
v___x_691_ = v_x_684_;
v_isShared_692_ = v_isSharedCheck_713_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_vs_689_);
lean_inc(v_ks_688_);
lean_dec(v_x_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_713_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_array_get_size(v_ks_688_);
v___x_694_ = lean_nat_dec_lt(v_x_685_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec(v_x_685_);
v___x_695_ = lean_array_push(v_ks_688_, v_x_686_);
v___x_696_ = lean_array_push(v_vs_689_, v_x_687_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_696_);
lean_ctor_set(v___x_691_, 0, v___x_695_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v_k_x27_700_; uint8_t v___x_701_; 
v_k_x27_700_ = lean_array_fget_borrowed(v_ks_688_, v_x_685_);
v___x_701_ = lean_name_eq(v_x_686_, v_k_x27_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_703_; 
if (v_isShared_692_ == 0)
{
v___x_703_ = v___x_691_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_ks_688_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_vs_689_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_x_685_, v___x_704_);
lean_dec(v_x_685_);
v_x_684_ = v___x_703_;
v_x_685_ = v___x_705_;
goto _start;
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_array_fset(v_ks_688_, v_x_685_, v_x_686_);
v___x_709_ = lean_array_fset(v_vs_689_, v_x_685_, v_x_687_);
lean_dec(v_x_685_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_709_);
lean_ctor_set(v___x_691_, 0, v___x_708_);
v___x_711_ = v___x_691_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_n_714_, lean_object* v_k_715_, lean_object* v_v_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(v_n_714_, v___x_717_, v_k_715_, v_v_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_x_720_, size_t v_x_721_, size_t v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v_es_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v_j_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_es_725_ = lean_ctor_get(v_x_720_, 0);
v___x_726_ = ((size_t)5ULL);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_729_ = lean_usize_land(v_x_721_, v___x_728_);
v_j_730_ = lean_usize_to_nat(v___x_729_);
v___x_731_ = lean_array_get_size(v_es_725_);
v___x_732_ = lean_nat_dec_lt(v_j_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_j_730_);
lean_dec(v_x_724_);
lean_dec(v_x_723_);
return v_x_720_;
}
else
{
lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_769_; 
lean_inc_ref(v_es_725_);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_x_720_, 0);
lean_dec(v_unused_770_);
v___x_734_ = v_x_720_;
v_isShared_735_ = v_isSharedCheck_769_;
goto v_resetjp_733_;
}
else
{
lean_dec(v_x_720_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_769_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_v_736_; lean_object* v___x_737_; lean_object* v_xs_x27_738_; lean_object* v___y_740_; 
v_v_736_ = lean_array_fget(v_es_725_, v_j_730_);
v___x_737_ = lean_box(0);
v_xs_x27_738_ = lean_array_fset(v_es_725_, v_j_730_, v___x_737_);
switch(lean_obj_tag(v_v_736_))
{
case 0:
{
lean_object* v_key_745_; lean_object* v_val_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_756_; 
v_key_745_ = lean_ctor_get(v_v_736_, 0);
v_val_746_ = lean_ctor_get(v_v_736_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_v_736_);
if (v_isSharedCheck_756_ == 0)
{
v___x_748_ = v_v_736_;
v_isShared_749_ = v_isSharedCheck_756_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_val_746_);
lean_inc(v_key_745_);
lean_dec(v_v_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_756_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v___x_750_; 
v___x_750_ = lean_name_eq(v_x_723_, v_key_745_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_del_object(v___x_748_);
v___x_751_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_745_, v_val_746_, v_x_723_, v_x_724_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
v___y_740_ = v___x_752_;
goto v___jp_739_;
}
else
{
lean_object* v___x_754_; 
lean_dec(v_val_746_);
lean_dec(v_key_745_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_x_724_);
lean_ctor_set(v___x_748_, 0, v_x_723_);
v___x_754_ = v___x_748_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_x_723_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_x_724_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
v___y_740_ = v___x_754_;
goto v___jp_739_;
}
}
}
}
case 1:
{
lean_object* v_node_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_767_; 
v_node_757_ = lean_ctor_get(v_v_736_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_v_736_);
if (v_isSharedCheck_767_ == 0)
{
v___x_759_ = v_v_736_;
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_node_757_);
lean_dec(v_v_736_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_761_ = lean_usize_shift_right(v_x_721_, v___x_726_);
v___x_762_ = lean_usize_add(v_x_722_, v___x_727_);
v___x_763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(v_node_757_, v___x_761_, v___x_762_, v_x_723_, v_x_724_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_763_);
v___x_765_ = v___x_759_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
v___y_740_ = v___x_765_;
goto v___jp_739_;
}
}
}
default: 
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_x_723_);
lean_ctor_set(v___x_768_, 1, v_x_724_);
v___y_740_ = v___x_768_;
goto v___jp_739_;
}
}
v___jp_739_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_array_fset(v_xs_x27_738_, v_j_730_, v___y_740_);
lean_dec(v_j_730_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_741_);
v___x_743_ = v___x_734_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_ks_771_; lean_object* v_vs_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_792_; 
v_ks_771_ = lean_ctor_get(v_x_720_, 0);
v_vs_772_ = lean_ctor_get(v_x_720_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_792_ == 0)
{
v___x_774_ = v_x_720_;
v_isShared_775_ = v_isSharedCheck_792_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_vs_772_);
lean_inc(v_ks_771_);
lean_dec(v_x_720_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_792_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_ks_771_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_vs_772_);
v___x_777_ = v_reuseFailAlloc_791_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v_newNode_778_; uint8_t v___y_780_; size_t v___x_786_; uint8_t v___x_787_; 
v_newNode_778_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_777_, v_x_723_, v_x_724_);
v___x_786_ = ((size_t)7ULL);
v___x_787_ = lean_usize_dec_le(v___x_786_, v_x_722_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_778_);
v___x_789_ = lean_unsigned_to_nat(4u);
v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
v___y_780_ = v___x_790_;
goto v___jp_779_;
}
else
{
v___y_780_ = v___x_787_;
goto v___jp_779_;
}
v___jp_779_:
{
if (v___y_780_ == 0)
{
lean_object* v_ks_781_; lean_object* v_vs_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_ks_781_ = lean_ctor_get(v_newNode_778_, 0);
lean_inc_ref(v_ks_781_);
v_vs_782_ = lean_ctor_get(v_newNode_778_, 1);
lean_inc_ref(v_vs_782_);
lean_dec_ref(v_newNode_778_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0);
v___x_785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_x_722_, v_ks_781_, v_vs_782_, v___x_783_, v___x_784_);
lean_dec_ref(v_vs_782_);
lean_dec_ref(v_ks_781_);
return v___x_785_;
}
else
{
return v_newNode_778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(size_t v_depth_793_, lean_object* v_keys_794_, lean_object* v_vals_795_, lean_object* v_i_796_, lean_object* v_entries_797_){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_array_get_size(v_keys_794_);
v___x_799_ = lean_nat_dec_lt(v_i_796_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec(v_i_796_);
return v_entries_797_;
}
else
{
lean_object* v_k_800_; lean_object* v_v_801_; uint64_t v___y_803_; 
v_k_800_ = lean_array_fget_borrowed(v_keys_794_, v_i_796_);
v_v_801_ = lean_array_fget_borrowed(v_vals_795_, v_i_796_);
if (lean_obj_tag(v_k_800_) == 0)
{
uint64_t v___x_814_; 
v___x_814_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_803_ = v___x_814_;
goto v___jp_802_;
}
else
{
uint64_t v_hash_815_; 
v_hash_815_ = lean_ctor_get_uint64(v_k_800_, sizeof(void*)*2);
v___y_803_ = v_hash_815_;
goto v___jp_802_;
}
v___jp_802_:
{
size_t v_h_804_; size_t v___x_805_; lean_object* v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v_h_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_h_804_ = lean_uint64_to_usize(v___y_803_);
v___x_805_ = ((size_t)5ULL);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_sub(v_depth_793_, v___x_807_);
v___x_809_ = lean_usize_mul(v___x_805_, v___x_808_);
v_h_810_ = lean_usize_shift_right(v_h_804_, v___x_809_);
v___x_811_ = lean_nat_add(v_i_796_, v___x_806_);
lean_dec(v_i_796_);
lean_inc(v_v_801_);
lean_inc(v_k_800_);
v___x_812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(v_entries_797_, v_h_810_, v_depth_793_, v_k_800_, v_v_801_);
v_i_796_ = v___x_811_;
v_entries_797_ = v___x_812_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_depth_816_, lean_object* v_keys_817_, lean_object* v_vals_818_, lean_object* v_i_819_, lean_object* v_entries_820_){
_start:
{
size_t v_depth_boxed_821_; lean_object* v_res_822_; 
v_depth_boxed_821_ = lean_unbox_usize(v_depth_816_);
lean_dec(v_depth_816_);
v_res_822_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_depth_boxed_821_, v_keys_817_, v_vals_818_, v_i_819_, v_entries_820_);
lean_dec_ref(v_vals_818_);
lean_dec_ref(v_keys_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
size_t v_x_2316__boxed_828_; size_t v_x_2317__boxed_829_; lean_object* v_res_830_; 
v_x_2316__boxed_828_ = lean_unbox_usize(v_x_824_);
lean_dec(v_x_824_);
v_x_2317__boxed_829_ = lean_unbox_usize(v_x_825_);
lean_dec(v_x_825_);
v_res_830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_823_, v_x_2316__boxed_828_, v_x_2317__boxed_829_, v_x_826_, v_x_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
uint64_t v___y_835_; 
if (lean_obj_tag(v_x_832_) == 0)
{
uint64_t v___x_839_; 
v___x_839_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_835_ = v___x_839_;
goto v___jp_834_;
}
else
{
uint64_t v_hash_840_; 
v_hash_840_ = lean_ctor_get_uint64(v_x_832_, sizeof(void*)*2);
v___y_835_ = v_hash_840_;
goto v___jp_834_;
}
v___jp_834_:
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_uint64_to_usize(v___y_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_831_, v___x_836_, v___x_837_, v_x_832_, v_x_833_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(lean_object* v_s_841_, lean_object* v_d_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = l_Lean_IR_Decl_name(v_d_842_);
v___x_844_ = l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4___redArg(v_s_841_, v___x_843_, v_d_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_));
v___x_873_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2____boxed(lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_();
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2(lean_object* v_n_876_, lean_object* v_as_877_, lean_object* v_lo_878_, lean_object* v_hi_879_, lean_object* v_w_880_, lean_object* v_hlo_881_, lean_object* v_hhi_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(v_as_877_, v_lo_878_, v_hi_879_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_884_, lean_object* v_as_885_, lean_object* v_lo_886_, lean_object* v_hi_887_, lean_object* v_w_888_, lean_object* v_hlo_889_, lean_object* v_hhi_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2(v_n_884_, v_as_885_, v_lo_886_, v_hi_887_, v_w_888_, v_hlo_889_, v_hhi_890_);
lean_dec(v_hi_887_);
lean_dec(v_n_884_);
return v_res_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg(v_x_893_, v_x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3(v_00_u03b2_896_, v_x_897_, v_x_898_);
lean_dec(v_x_898_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4___redArg(v_x_902_, v_x_903_, v_x_904_);
return v___x_905_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b2_906_, lean_object* v_x_907_, size_t v_x_908_, lean_object* v_x_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
size_t v_x_2603__boxed_915_; uint8_t v_res_916_; lean_object* v_r_917_; 
v_x_2603__boxed_915_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_res_916_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_911_, v_x_912_, v_x_2603__boxed_915_, v_x_914_);
lean_dec(v_x_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b2_918_, lean_object* v_x_919_, size_t v_x_920_, size_t v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_919_, v_x_920_, v_x_921_, v_x_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b2_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
size_t v_x_2614__boxed_931_; size_t v_x_2615__boxed_932_; lean_object* v_res_933_; 
v_x_2614__boxed_931_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_x_2615__boxed_932_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_res_933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b2_925_, v_x_926_, v_x_2614__boxed_931_, v_x_2615__boxed_932_, v_x_929_, v_x_930_);
return v_res_933_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b2_934_, lean_object* v_keys_935_, lean_object* v_vals_936_, lean_object* v_heq_937_, lean_object* v_i_938_, lean_object* v_k_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_keys_935_, v_i_938_, v_k_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_heq_944_, lean_object* v_i_945_, lean_object* v_k_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b2_941_, v_keys_942_, v_vals_943_, v_heq_944_, v_i_945_, v_k_946_);
lean_dec(v_k_946_);
lean_dec_ref(v_vals_943_);
lean_dec_ref(v_keys_942_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_949_, lean_object* v_n_950_, lean_object* v_k_951_, lean_object* v_v_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_n_950_, v_k_951_, v_v_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_00_u03b2_954_, size_t v_depth_955_, lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_heq_958_, lean_object* v_i_959_, lean_object* v_entries_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_depth_955_, v_keys_956_, v_vals_957_, v_i_959_, v_entries_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b2_962_, lean_object* v_depth_963_, lean_object* v_keys_964_, lean_object* v_vals_965_, lean_object* v_heq_966_, lean_object* v_i_967_, lean_object* v_entries_968_){
_start:
{
size_t v_depth_boxed_969_; lean_object* v_res_970_; 
v_depth_boxed_969_ = lean_unbox_usize(v_depth_963_);
lean_dec(v_depth_963_);
v_res_970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_00_u03b2_962_, v_depth_boxed_969_, v_keys_964_, v_vals_965_, v_heq_966_, v_i_967_, v_entries_968_);
lean_dec_ref(v_vals_965_);
lean_dec_ref(v_keys_964_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(v_x_972_, v_x_973_, v_x_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_977_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_array_get_size(v_irDecls_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_nat_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___y_984_; uint8_t v___x_988_; 
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_sub(v___x_978_, v___x_981_);
v___x_988_ = lean_nat_dec_le(v___x_979_, v___x_982_);
if (v___x_988_ == 0)
{
lean_inc(v___x_982_);
v___y_984_ = v___x_982_;
goto v___jp_983_;
}
else
{
v___y_984_ = v___x_979_;
goto v___jp_983_;
}
v___jp_983_:
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_le(v___y_984_, v___x_982_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v___x_982_);
lean_inc(v___y_984_);
v___x_986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(v_irDecls_977_, v___y_984_, v___y_984_);
lean_dec(v___y_984_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg(v_irDecls_977_, v___y_984_, v___x_982_);
lean_dec(v___x_982_);
return v___x_987_;
}
}
}
else
{
return v_irDecls_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_989_){
_start:
{
lean_inc_ref(v_initDecls_989_);
return v_initDecls_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_990_);
lean_dec_ref(v_initDecls_990_);
return v_res_991_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_995_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0));
v___x_996_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_995_, v___x_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v_toEnvExtension_1002_; lean_object* v_name_1003_; lean_object* v_asyncMode_1004_; lean_object* v___x_1005_; lean_object* v_ext_1006_; lean_object* v_toEnvExtension_1007_; lean_object* v_name_1008_; lean_object* v_exportEntriesFn_1009_; lean_object* v_asyncMode_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_irDecls_1015_; lean_object* v_irEntries_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v_initDecls_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1001_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc_ref(v_toEnvExtension_1002_);
v_name_1003_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_name_1003_);
v_asyncMode_1004_ = lean_ctor_get(v_toEnvExtension_1002_, 2);
lean_inc(v_asyncMode_1004_);
lean_dec_ref(v_toEnvExtension_1002_);
v___x_1005_ = l_Lean_regularInitAttr;
v_ext_1006_ = lean_ctor_get(v___x_1005_, 1);
lean_inc_ref(v_ext_1006_);
v_toEnvExtension_1007_ = lean_ctor_get(v_ext_1006_, 0);
v_name_1008_ = lean_ctor_get(v_ext_1006_, 1);
lean_inc(v_name_1008_);
v_exportEntriesFn_1009_ = lean_ctor_get(v_ext_1006_, 4);
lean_inc_ref(v_exportEntriesFn_1009_);
v_asyncMode_1010_ = lean_ctor_get(v_toEnvExtension_1007_, 2);
lean_inc(v_asyncMode_1010_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1012_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
v___x_1013_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1000_);
v___x_1014_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1011_, v___x_1001_, v_env_1000_, v_asyncMode_1004_);
lean_dec(v_asyncMode_1004_);
v_irDecls_1015_ = l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__1(v___x_1013_, v___x_1014_);
v_irEntries_1016_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(v_irDecls_1015_);
v___x_1017_ = lean_box(0);
lean_inc_ref(v_env_1000_);
v___x_1018_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1012_, v_ext_1006_, v_env_1000_, v_asyncMode_1010_, v___x_1017_);
lean_dec(v_asyncMode_1010_);
lean_dec_ref(v_ext_1006_);
v___x_1019_ = 2;
v___x_1020_ = lean_box(v___x_1019_);
v_initDecls_1021_ = lean_apply_3(v_exportEntriesFn_1009_, v_env_1000_, v___x_1018_, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_name_1003_);
lean_ctor_set(v___x_1022_, 1, v_irEntries_1016_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_name_1008_);
lean_ctor_set(v___x_1023_, 1, v_initDecls_1021_);
v___x_1024_ = lean_unsigned_to_nat(2u);
v___x_1025_ = lean_mk_empty_array_with_capacity(v___x_1024_);
v___x_1026_ = lean_array_push(v___x_1025_, v___x_1022_);
v___x_1027_ = lean_array_push(v___x_1026_, v___x_1023_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1028_, lean_object* v_k_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_m_1034_; lean_object* v_a_1035_; uint8_t v___x_1036_; 
v___x_1032_ = lean_nat_add(v_x_1030_, v_x_1031_);
v___x_1033_ = lean_unsigned_to_nat(1u);
v_m_1034_ = lean_nat_shiftr(v___x_1032_, v___x_1033_);
lean_dec(v___x_1032_);
v_a_1035_ = lean_array_fget_borrowed(v_as_1028_, v_m_1034_);
v___x_1036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1035_, v_k_1029_);
if (v___x_1036_ == 0)
{
uint8_t v___x_1037_; 
lean_dec(v_x_1031_);
v___x_1037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1029_, v_a_1035_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec(v_m_1034_);
lean_dec(v_x_1030_);
lean_inc(v_a_1035_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_a_1035_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_nat_dec_eq(v_m_1034_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_nat_sub(v_m_1034_, v___x_1033_);
lean_dec(v_m_1034_);
v___x_1042_ = lean_nat_dec_lt(v___x_1041_, v_x_1030_);
if (v___x_1042_ == 0)
{
v_x_1031_ = v___x_1041_;
goto _start;
}
else
{
lean_object* v___x_1044_; 
lean_dec(v___x_1041_);
lean_dec(v_x_1030_);
v___x_1044_ = lean_box(0);
return v___x_1044_;
}
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_m_1034_);
lean_dec(v_x_1030_);
v___x_1045_ = lean_box(0);
return v___x_1045_;
}
}
}
else
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
lean_dec(v_x_1030_);
v___x_1046_ = lean_nat_add(v_m_1034_, v___x_1033_);
lean_dec(v_m_1034_);
v___x_1047_ = lean_nat_dec_le(v___x_1046_, v_x_1031_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_dec(v___x_1046_);
lean_dec(v_x_1031_);
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
else
{
v_x_1030_ = v___x_1046_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1050_, lean_object* v_k_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1050_, v_k_1051_, v_x_1052_, v_x_1053_);
lean_dec_ref(v_k_1051_);
lean_dec_ref(v_as_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1055_, lean_object* v_vals_1056_, lean_object* v_i_1057_, lean_object* v_k_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_array_get_size(v_keys_1055_);
v___x_1060_ = lean_nat_dec_lt(v_i_1057_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v_i_1057_);
v___x_1061_ = lean_box(0);
return v___x_1061_;
}
else
{
lean_object* v_k_x27_1062_; uint8_t v___x_1063_; 
v_k_x27_1062_ = lean_array_fget_borrowed(v_keys_1055_, v_i_1057_);
v___x_1063_ = lean_name_eq(v_k_1058_, v_k_x27_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_i_1057_, v___x_1064_);
lean_dec(v_i_1057_);
v_i_1057_ = v___x_1065_;
goto _start;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_array_fget_borrowed(v_vals_1056_, v_i_1057_);
lean_dec(v_i_1057_);
lean_inc(v___x_1067_);
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_i_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1069_, v_vals_1070_, v_i_1071_, v_k_1072_);
lean_dec(v_k_1072_);
lean_dec_ref(v_vals_1070_);
lean_dec_ref(v_keys_1069_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1074_, size_t v_x_1075_, lean_object* v_x_1076_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v_es_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1098_; 
v_es_1077_ = lean_ctor_get(v_x_1074_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1079_ = v_x_1074_;
v_isShared_1080_ = v_isSharedCheck_1098_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_es_1077_);
lean_dec(v_x_1074_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1098_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v_j_1085_; lean_object* v___x_1086_; 
v___x_1081_ = lean_box(2);
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1084_ = lean_usize_land(v_x_1075_, v___x_1083_);
v_j_1085_ = lean_usize_to_nat(v___x_1084_);
v___x_1086_ = lean_array_get(v___x_1081_, v_es_1077_, v_j_1085_);
lean_dec(v_j_1085_);
lean_dec_ref(v_es_1077_);
switch(lean_obj_tag(v___x_1086_))
{
case 0:
{
lean_object* v_key_1087_; lean_object* v_val_1088_; uint8_t v___x_1089_; 
v_key_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_key_1087_);
v_val_1088_ = lean_ctor_get(v___x_1086_, 1);
lean_inc(v_val_1088_);
lean_dec_ref(v___x_1086_);
v___x_1089_ = lean_name_eq(v_x_1076_, v_key_1087_);
lean_dec(v_key_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v_val_1088_);
lean_del_object(v___x_1079_);
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
else
{
lean_object* v___x_1092_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 1);
lean_ctor_set(v___x_1079_, 0, v_val_1088_);
v___x_1092_ = v___x_1079_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_val_1088_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
case 1:
{
lean_object* v_node_1094_; size_t v___x_1095_; 
lean_del_object(v___x_1079_);
v_node_1094_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_node_1094_);
lean_dec_ref(v___x_1086_);
v___x_1095_ = lean_usize_shift_right(v_x_1075_, v___x_1082_);
v_x_1074_ = v_node_1094_;
v_x_1075_ = v___x_1095_;
goto _start;
}
default: 
{
lean_object* v___x_1097_; 
lean_del_object(v___x_1079_);
v___x_1097_ = lean_box(0);
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_ks_1099_; lean_object* v_vs_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_ks_1099_ = lean_ctor_get(v_x_1074_, 0);
lean_inc_ref(v_ks_1099_);
v_vs_1100_ = lean_ctor_get(v_x_1074_, 1);
lean_inc_ref(v_vs_1100_);
lean_dec_ref(v_x_1074_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1099_, v_vs_1100_, v___x_1101_, v_x_1076_);
lean_dec_ref(v_vs_1100_);
lean_dec_ref(v_ks_1099_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
size_t v_x_863__boxed_1106_; lean_object* v_res_1107_; 
v_x_863__boxed_1106_ = lean_unbox_usize(v_x_1104_);
lean_dec(v_x_1104_);
v_res_1107_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1103_, v_x_863__boxed_1106_, v_x_1105_);
lean_dec(v_x_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
uint64_t v___y_1111_; 
if (lean_obj_tag(v_x_1109_) == 0)
{
uint64_t v___x_1114_; 
v___x_1114_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_1111_ = v___x_1114_;
goto v___jp_1110_;
}
else
{
uint64_t v_hash_1115_; 
v_hash_1115_ = lean_ctor_get_uint64(v_x_1109_, sizeof(void*)*2);
v___y_1111_ = v_hash_1115_;
goto v___jp_1110_;
}
v___jp_1110_:
{
size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_uint64_to_usize(v___y_1111_);
v___x_1113_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1108_, v___x_1112_, v_x_1109_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1116_, v_x_1117_);
lean_dec(v_x_1117_);
return v_res_1118_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___x_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1122_, lean_object* v_declName_1123_, uint8_t v_includeServer_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1126_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1122_, v_declName_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; lean_object* v_toEnvExtension_1128_; lean_object* v_asyncMode_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1127_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_toEnvExtension_1128_);
v_asyncMode_1129_ = lean_ctor_get(v_toEnvExtension_1128_, 2);
lean_inc(v_asyncMode_1129_);
lean_dec_ref(v_toEnvExtension_1128_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1125_, v___x_1127_, v_env_1122_, v_asyncMode_1129_, v___x_1130_);
lean_dec(v_asyncMode_1129_);
v___x_1132_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1131_, v_declName_1123_);
lean_dec(v_declName_1123_);
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1134_; lean_object* v___y_1136_; 
v_val_1133_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1133_);
lean_dec_ref(v___x_1126_);
v___x_1134_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
if (v_includeServer_1124_ == 0)
{
lean_object* v___x_1169_; lean_object* v_modules_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1169_ = l_Lean_Environment_header(v_env_1122_);
v_modules_1170_ = lean_ctor_get(v___x_1169_, 3);
lean_inc_ref(v_modules_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = lean_array_get_size(v_modules_1170_);
v___x_1172_ = lean_nat_dec_lt(v_val_1133_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec_ref(v_modules_1170_);
goto v___jp_1167_;
}
else
{
lean_object* v___x_1173_; uint8_t v_irPhases_1174_; uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1173_ = lean_array_fget(v_modules_1170_, v_val_1133_);
lean_dec_ref(v_modules_1170_);
v_irPhases_1174_ = lean_ctor_get_uint8(v___x_1173_, sizeof(void*)*1);
lean_dec(v___x_1173_);
v___x_1175_ = 0;
v___x_1176_ = l_Lean_instBEqIRPhases_beq(v_irPhases_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
goto v___jp_1151_;
}
else
{
goto v___jp_1167_;
}
}
}
else
{
goto v___jp_1151_;
}
v___jp_1135_:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1137_ = l_Lean_IR_declMapExt;
v___x_1138_ = 0;
v___x_1139_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1134_, v___x_1137_, v_env_1122_, v_val_1133_, v___x_1138_);
lean_dec(v_val_1133_);
lean_dec_ref(v_env_1122_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_array_get_size(v___x_1139_);
v___x_1142_ = lean_nat_dec_lt(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec_ref(v___x_1139_);
lean_dec(v_declName_1123_);
return v___y_1136_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = lean_nat_sub(v___x_1141_, v___x_1143_);
v___x_1145_ = lean_nat_dec_le(v___x_1140_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec(v___x_1144_);
lean_dec_ref(v___x_1139_);
lean_dec(v_declName_1123_);
return v___y_1136_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_tmpDecl_1149_; lean_object* v___x_1150_; 
lean_dec(v___y_1136_);
v___x_1146_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_1149_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1149_, 0, v_declName_1123_);
lean_ctor_set(v_tmpDecl_1149_, 1, v___x_1146_);
lean_ctor_set(v_tmpDecl_1149_, 2, v___x_1147_);
lean_ctor_set(v_tmpDecl_1149_, 3, v___x_1148_);
v___x_1150_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1139_, v_tmpDecl_1149_, v___x_1140_, v___x_1144_);
lean_dec_ref(v_tmpDecl_1149_);
lean_dec_ref(v___x_1139_);
return v___x_1150_;
}
}
}
v___jp_1151_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1152_ = l_Lean_IR_declMapExt;
v___x_1153_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1134_, v___x_1152_, v_env_1122_, v_val_1133_);
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_array_get_size(v___x_1153_);
v___x_1156_ = lean_nat_dec_lt(v___x_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v___x_1153_);
v___x_1157_ = lean_box(0);
v___y_1136_ = v___x_1157_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_sub(v___x_1155_, v___x_1158_);
v___x_1160_ = lean_nat_dec_le(v___x_1154_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v___x_1159_);
lean_dec_ref(v___x_1153_);
v___x_1161_ = lean_box(0);
v___y_1136_ = v___x_1161_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_tmpDecl_1165_; lean_object* v___x_1166_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1123_);
v_tmpDecl_1165_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1165_, 0, v_declName_1123_);
lean_ctor_set(v_tmpDecl_1165_, 1, v___x_1162_);
lean_ctor_set(v_tmpDecl_1165_, 2, v___x_1163_);
lean_ctor_set(v_tmpDecl_1165_, 3, v___x_1164_);
v___x_1166_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1153_, v_tmpDecl_1165_, v___x_1154_, v___x_1159_);
lean_dec_ref(v_tmpDecl_1165_);
lean_dec_ref(v___x_1153_);
if (lean_obj_tag(v___x_1166_) == 0)
{
v___y_1136_ = v___x_1166_;
goto v___jp_1135_;
}
else
{
lean_dec(v_val_1133_);
lean_dec(v_declName_1123_);
lean_dec_ref(v_env_1122_);
return v___x_1166_;
}
}
}
}
v___jp_1167_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_box(0);
v___y_1136_ = v___x_1168_;
goto v___jp_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl___boxed(lean_object* v_env_1177_, lean_object* v_declName_1178_, lean_object* v_includeServer_1179_){
_start:
{
uint8_t v_includeServer_boxed_1180_; lean_object* v_res_1181_; 
v_includeServer_boxed_1180_ = lean_unbox(v_includeServer_1179_);
v_res_1181_ = l_Lean_IR_findEnvDecl(v_env_1177_, v_declName_1178_, v_includeServer_boxed_1180_);
return v_res_1181_;
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
size_t v_x_1073__boxed_1211_; lean_object* v_res_1212_; 
v_x_1073__boxed_1211_ = lean_unbox_usize(v_x_1209_);
lean_dec(v_x_1209_);
v_res_1212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1207_, v_x_1208_, v_x_1073__boxed_1211_, v_x_1210_);
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
uint8_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = 1;
v___x_1230_ = l_Lean_IR_findEnvDecl(v_env_1227_, v_declName_1228_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1231_, lean_object* v_declName_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v_boxed_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc(v_declName_1232_);
v_boxed_1234_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1232_);
v___x_1235_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1231_, v_declName_1232_);
lean_dec(v_declName_1232_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; lean_object* v_toEnvExtension_1237_; lean_object* v_asyncMode_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc_ref(v_toEnvExtension_1237_);
v_asyncMode_1238_ = lean_ctor_get(v_toEnvExtension_1237_, 2);
lean_inc(v_asyncMode_1238_);
lean_dec_ref(v_toEnvExtension_1237_);
v___x_1239_ = lean_box(0);
v___x_1240_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1233_, v___x_1236_, v_env_1231_, v_asyncMode_1238_, v___x_1239_);
lean_dec(v_asyncMode_1238_);
v___x_1241_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1240_, v_boxed_1234_);
lean_dec(v_boxed_1234_);
return v___x_1241_;
}
else
{
lean_object* v_val_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___y_1246_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_val_1242_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1242_);
lean_dec_ref(v___x_1235_);
v___x_1243_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1244_ = l_Lean_IR_declMapExt;
v___x_1260_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1243_, v___x_1244_, v_env_1231_, v_val_1242_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_array_get_size(v___x_1260_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1260_);
v___x_1264_ = lean_box(0);
v___y_1246_ = v___x_1264_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_sub(v___x_1262_, v___x_1265_);
v___x_1267_ = lean_nat_dec_le(v___x_1261_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v___x_1266_);
lean_dec_ref(v___x_1260_);
v___x_1268_ = lean_box(0);
v___y_1246_ = v___x_1268_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_tmpDecl_1272_; lean_object* v___x_1273_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1270_ = lean_box(0);
v___x_1271_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_boxed_1234_);
v_tmpDecl_1272_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1272_, 0, v_boxed_1234_);
lean_ctor_set(v_tmpDecl_1272_, 1, v___x_1269_);
lean_ctor_set(v_tmpDecl_1272_, 2, v___x_1270_);
lean_ctor_set(v_tmpDecl_1272_, 3, v___x_1271_);
v___x_1273_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1260_, v_tmpDecl_1272_, v___x_1261_, v___x_1266_);
lean_dec_ref(v_tmpDecl_1272_);
lean_dec_ref(v___x_1260_);
if (lean_obj_tag(v___x_1273_) == 0)
{
v___y_1246_ = v___x_1273_;
goto v___jp_1245_;
}
else
{
lean_dec(v_val_1242_);
lean_dec(v_boxed_1234_);
lean_dec_ref(v_env_1231_);
return v___x_1273_;
}
}
}
v___jp_1245_:
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1247_ = 0;
v___x_1248_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1243_, v___x_1244_, v_env_1231_, v_val_1242_, v___x_1247_);
lean_dec(v_val_1242_);
lean_dec_ref(v_env_1231_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_array_get_size(v___x_1248_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec_ref(v___x_1248_);
lean_dec(v_boxed_1234_);
return v___y_1246_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_sub(v___x_1250_, v___x_1252_);
v___x_1254_ = lean_nat_dec_le(v___x_1249_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec(v___x_1253_);
lean_dec_ref(v___x_1248_);
lean_dec(v_boxed_1234_);
return v___y_1246_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_tmpDecl_1258_; lean_object* v___x_1259_; 
lean_dec(v___y_1246_);
v___x_1255_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_1258_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1258_, 0, v_boxed_1234_);
lean_ctor_set(v_tmpDecl_1258_, 1, v___x_1255_);
lean_ctor_set(v_tmpDecl_1258_, 2, v___x_1256_);
lean_ctor_set(v_tmpDecl_1258_, 3, v___x_1257_);
v___x_1259_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1248_, v_tmpDecl_1258_, v___x_1249_, v___x_1253_);
lean_dec_ref(v_tmpDecl_1258_);
lean_dec_ref(v___x_1248_);
return v___x_1259_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1274_, lean_object* v_constName_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1274_, v_constName_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v_toEnvExtension_1278_; lean_object* v_asyncMode_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1277_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_toEnvExtension_1278_);
v_asyncMode_1279_ = lean_ctor_get(v_toEnvExtension_1278_, 2);
lean_inc(v_asyncMode_1279_);
lean_dec_ref(v_toEnvExtension_1278_);
v___x_1280_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1280_, v___x_1277_, v_env_1274_, v_asyncMode_1279_, v___x_1281_);
lean_dec(v_asyncMode_1279_);
v___x_1283_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2__spec__3___redArg(v___x_1282_, v_constName_1275_);
lean_dec(v_constName_1275_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = 1;
return v___x_1284_;
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = 0;
return v___x_1285_;
}
}
else
{
uint8_t v___x_1286_; 
lean_dec_ref(v___x_1276_);
lean_dec(v_constName_1275_);
lean_dec_ref(v_env_1274_);
v___x_1286_ = 0;
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1287_, lean_object* v_constName_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = lean_has_compile_error(v_env_1287_, v_constName_1288_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v_env_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1294_ = lean_st_ref_get(v_a_1292_);
v_env_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc_ref(v_env_1295_);
lean_dec(v___x_1294_);
v___x_1296_ = 0;
v___x_1297_ = l_Lean_IR_findEnvDecl(v_env_1295_, v_n_1291_, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_IR_findDecl___redArg(v_n_1299_, v_a_1300_);
lean_dec(v_a_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_IR_findDecl___redArg(v_n_1303_, v_a_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_IR_findDecl(v_n_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1331_; 
v___x_1316_ = l_Lean_IR_findDecl___redArg(v_n_1313_, v_a_1314_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1331_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1331_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
if (lean_obj_tag(v_a_1317_) == 0)
{
uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1321_ = 0;
v___x_1322_ = lean_box(v___x_1321_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1322_);
v___x_1324_ = v___x_1319_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
else
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec_ref(v_a_1317_);
v___x_1326_ = 1;
v___x_1327_ = lean_box(v___x_1326_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1327_);
v___x_1329_ = v___x_1319_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_IR_containsDecl___redArg(v_n_1332_, v_a_1333_);
lean_dec(v_a_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_IR_containsDecl___redArg(v_n_1336_, v_a_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_IR_containsDecl(v_n_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_ref_1350_; lean_object* v___x_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_ref_1350_ = lean_ctor_get(v___y_1347_, 5);
v___x_1351_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1346_, v___y_1347_, v___y_1348_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_inc(v_ref_1350_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_ref_1350_);
lean_ctor_set(v___x_1356_, 1, v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 1);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1390_; 
lean_inc(v_n_1368_);
v___x_1372_ = l_Lean_IR_findDecl___redArg(v_n_1368_, v_a_1370_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1390_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1390_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
if (lean_obj_tag(v_a_1373_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1379_; 
lean_dec(v_n_1368_);
v_val_1377_ = lean_ctor_get(v_a_1373_, 0);
lean_inc(v_val_1377_);
lean_dec_ref(v_a_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_val_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_val_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_del_object(v___x_1375_);
lean_dec(v_a_1373_);
v___x_1381_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1382_ = 1;
v___x_1383_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1368_, v___x_1382_);
v___x_1384_ = lean_string_append(v___x_1381_, v___x_1383_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
v___x_1389_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1388_, v_a_1369_, v_a_1370_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_IR_getDecl(v_n_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1396_, lean_object* v_msg_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1402_, v_msg_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_env_1412_; lean_object* v___x_1413_; lean_object* v_toEnvExtension_1414_; lean_object* v_asyncMode_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1411_ = lean_st_ref_get(v_a_1409_);
v_env_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc_ref(v_env_1412_);
lean_dec(v___x_1411_);
v___x_1413_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc_ref(v_toEnvExtension_1414_);
v_asyncMode_1415_ = lean_ctor_get(v_toEnvExtension_1414_, 2);
lean_inc(v_asyncMode_1415_);
lean_dec_ref(v_toEnvExtension_1414_);
v___x_1416_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1416_, v___x_1413_, v_env_1412_, v_asyncMode_1415_, v___x_1417_);
lean_dec(v_asyncMode_1415_);
v___x_1419_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1418_, v_n_1408_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_IR_findLocalDecl___redArg(v_n_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec(v_n_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_IR_findLocalDecl___redArg(v_n_1425_, v_a_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_IR_findLocalDecl(v_n_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_n_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v_toEnvExtension_1437_; lean_object* v_asyncMode_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_toEnvExtension_1437_);
v_asyncMode_1438_ = lean_ctor_get(v_toEnvExtension_1437_, 2);
lean_inc(v_asyncMode_1438_);
lean_dec_ref(v_toEnvExtension_1437_);
v___x_1439_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1440_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1439_, v___x_1436_, v_env_1435_, v_asyncMode_1438_);
lean_dec(v_asyncMode_1438_);
return v___x_1440_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_env_1450_; lean_object* v_nextMacroScope_1451_; lean_object* v_ngen_1452_; lean_object* v_auxDeclNGen_1453_; lean_object* v_traceState_1454_; lean_object* v_messages_1455_; lean_object* v_infoState_1456_; lean_object* v_snapshotTasks_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1473_; 
v___x_1449_ = lean_st_ref_take(v_a_1447_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
v_nextMacroScope_1451_ = lean_ctor_get(v___x_1449_, 1);
v_ngen_1452_ = lean_ctor_get(v___x_1449_, 2);
v_auxDeclNGen_1453_ = lean_ctor_get(v___x_1449_, 3);
v_traceState_1454_ = lean_ctor_get(v___x_1449_, 4);
v_messages_1455_ = lean_ctor_get(v___x_1449_, 6);
v_infoState_1456_ = lean_ctor_get(v___x_1449_, 7);
v_snapshotTasks_1457_ = lean_ctor_get(v___x_1449_, 8);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v___x_1449_, 5);
lean_dec(v_unused_1474_);
v___x_1459_ = v___x_1449_;
v_isShared_1460_ = v_isSharedCheck_1473_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snapshotTasks_1457_);
lean_inc(v_infoState_1456_);
lean_inc(v_messages_1455_);
lean_inc(v_traceState_1454_);
lean_inc(v_auxDeclNGen_1453_);
lean_inc(v_ngen_1452_);
lean_inc(v_nextMacroScope_1451_);
lean_inc(v_env_1450_);
lean_dec(v___x_1449_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1473_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v_toEnvExtension_1462_; lean_object* v_asyncMode_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1461_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_toEnvExtension_1462_);
v_asyncMode_1463_ = lean_ctor_get(v_toEnvExtension_1462_, 2);
lean_inc(v_asyncMode_1463_);
lean_dec_ref(v_toEnvExtension_1462_);
v___x_1464_ = lean_box(0);
v___x_1465_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1461_, v_env_1450_, v_decl_1446_, v_asyncMode_1463_, v___x_1464_);
lean_dec(v_asyncMode_1463_);
v___x_1466_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 5, v___x_1466_);
lean_ctor_set(v___x_1459_, 0, v___x_1465_);
v___x_1468_ = v___x_1459_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_nextMacroScope_1451_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_ngen_1452_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_auxDeclNGen_1453_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_traceState_1454_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_messages_1455_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_infoState_1456_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v_snapshotTasks_1457_);
v___x_1468_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_st_ref_set(v_a_1447_, v___x_1468_);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_IR_addDecl___redArg(v_decl_1475_, v_a_1476_);
lean_dec(v_a_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_IR_addDecl___redArg(v_decl_1479_, v_a_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_IR_addDecl(v_decl_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1489_, size_t v_i_1490_, size_t v_stop_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_usize_dec_eq(v_i_1490_, v_stop_1491_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_array_uget_borrowed(v_as_1489_, v_i_1490_);
lean_inc(v___x_1496_);
v___x_1497_ = l_Lean_IR_addDecl___redArg(v___x_1496_, v___y_1493_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; size_t v___x_1499_; size_t v___x_1500_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1490_, v___x_1499_);
v_i_1490_ = v___x_1500_;
v_b_1492_ = v_a_1498_;
goto _start;
}
else
{
return v___x_1497_;
}
}
else
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_b_1492_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1503_, lean_object* v_i_1504_, lean_object* v_stop_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
size_t v_i_boxed_1509_; size_t v_stop_boxed_1510_; lean_object* v_res_1511_; 
v_i_boxed_1509_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_stop_boxed_1510_ = lean_unbox_usize(v_stop_1505_);
lean_dec(v_stop_1505_);
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1503_, v_i_boxed_1509_, v_stop_boxed_1510_, v_b_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v_as_1503_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get_size(v_decls_1512_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_nat_dec_lt(v___x_1516_, v___x_1517_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
return v___x_1520_;
}
else
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_nat_dec_le(v___x_1517_, v___x_1517_);
if (v___x_1521_ == 0)
{
if (v___x_1519_ == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1518_);
return v___x_1522_;
}
else
{
size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = lean_usize_of_nat(v___x_1517_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1512_, v___x_1523_, v___x_1524_, v___x_1518_, v_a_1514_);
return v___x_1525_;
}
}
else
{
size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = ((size_t)0ULL);
v___x_1527_ = lean_usize_of_nat(v___x_1517_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1512_, v___x_1526_, v___x_1527_, v___x_1518_, v_a_1514_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_IR_addDecls(v_decls_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec_ref(v_decls_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1534_, size_t v_i_1535_, size_t v_stop_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1534_, v_i_1535_, v_stop_1536_, v_b_1537_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1542_, lean_object* v_i_1543_, lean_object* v_stop_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
size_t v_i_boxed_1549_; size_t v_stop_boxed_1550_; lean_object* v_res_1551_; 
v_i_boxed_1549_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_stop_boxed_1550_ = lean_unbox_usize(v_stop_1544_);
lean_dec(v_stop_1544_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1542_, v_i_boxed_1549_, v_stop_boxed_1550_, v_b_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_as_1542_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1555_, lean_object* v_as_1556_, size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_b_1559_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1560_ == 0)
{
return v_b_1559_;
}
else
{
lean_object* v___x_1561_; lean_object* v_a_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
lean_dec_ref(v_b_1559_);
v___x_1561_ = lean_box(0);
v_a_1562_ = lean_array_uget_borrowed(v_as_1556_, v_i_1558_);
v___x_1563_ = l_Lean_IR_Decl_name(v_a_1562_);
v___x_1564_ = lean_name_eq(v___x_1563_, v_n_1555_);
lean_dec(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; 
v___x_1565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1558_, v___x_1566_);
v_i_1558_ = v___x_1567_;
v_b_1559_ = v___x_1565_;
goto _start;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_inc(v_a_1562_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_a_1562_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1561_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1572_, lean_object* v_as_1573_, lean_object* v_sz_1574_, lean_object* v_i_1575_, lean_object* v_b_1576_){
_start:
{
size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; lean_object* v_res_1579_; 
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1574_);
lean_dec(v_sz_1574_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1575_);
lean_dec(v_i_1575_);
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1572_, v_as_1573_, v_sz_boxed_1577_, v_i_boxed_1578_, v_b_1576_);
lean_dec_ref(v_as_1573_);
lean_dec(v_n_1572_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1580_, lean_object* v_n_1581_, lean_object* v_decls_1582_){
_start:
{
lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; lean_object* v_fst_1590_; 
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1587_ = lean_array_size(v_decls_1582_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1581_, v_decls_1582_, v_sz_1587_, v___x_1588_, v___x_1586_);
v_fst_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_fst_1590_);
lean_dec_ref(v___x_1589_);
if (lean_obj_tag(v_fst_1590_) == 0)
{
goto v___jp_1583_;
}
else
{
lean_object* v_val_1591_; 
v_val_1591_ = lean_ctor_get(v_fst_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref(v_fst_1590_);
if (lean_obj_tag(v_val_1591_) == 0)
{
goto v___jp_1583_;
}
else
{
lean_dec(v_n_1581_);
lean_dec_ref(v_env_1580_);
return v_val_1591_;
}
}
v___jp_1583_:
{
uint8_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = 0;
v___x_1585_ = l_Lean_IR_findEnvDecl(v_env_1580_, v_n_1581_, v___x_1584_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1592_, lean_object* v_n_1593_, lean_object* v_decls_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_IR_findEnvDecl_x27(v_env_1592_, v_n_1593_, v_decls_1594_);
lean_dec_ref(v_decls_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1596_, lean_object* v_decls_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v_env_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1600_ = lean_st_ref_get(v_a_1598_);
v_env_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1601_);
lean_dec(v___x_1600_);
v___x_1602_ = l_Lean_IR_findEnvDecl_x27(v_env_1601_, v_n_1596_, v_decls_1597_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1604_, lean_object* v_decls_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_IR_findDecl_x27___redArg(v_n_1604_, v_decls_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_decls_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1609_, lean_object* v_decls_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_IR_findDecl_x27___redArg(v_n_1609_, v_decls_1610_, v_a_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1615_, lean_object* v_decls_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_IR_findDecl_x27(v_n_1615_, v_decls_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_decls_1616_);
return v_res_1620_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1621_, lean_object* v_as_1622_, size_t v_i_1623_, size_t v_stop_1624_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_usize_dec_eq(v_i_1623_, v_stop_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1626_ = lean_array_uget_borrowed(v_as_1622_, v_i_1623_);
v___x_1627_ = l_Lean_IR_Decl_name(v___x_1626_);
v___x_1628_ = lean_name_eq(v___x_1627_, v_n_1621_);
lean_dec(v___x_1627_);
if (v___x_1628_ == 0)
{
size_t v___x_1629_; size_t v___x_1630_; 
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_add(v_i_1623_, v___x_1629_);
v_i_1623_ = v___x_1630_;
goto _start;
}
else
{
return v___x_1628_;
}
}
else
{
uint8_t v___x_1632_; 
v___x_1632_ = 0;
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1633_, lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_stop_1636_){
_start:
{
size_t v_i_boxed_1637_; size_t v_stop_boxed_1638_; uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_i_boxed_1637_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_stop_boxed_1638_ = lean_unbox_usize(v_stop_1636_);
lean_dec(v_stop_1636_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1633_, v_as_1634_, v_i_boxed_1637_, v_stop_boxed_1638_);
lean_dec_ref(v_as_1634_);
lean_dec(v_n_1633_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1641_, lean_object* v_decls_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_array_get_size(v_decls_1642_);
v___x_1647_ = lean_nat_dec_lt(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_IR_containsDecl___redArg(v_n_1641_, v_a_1643_);
return v___x_1648_;
}
else
{
if (v___x_1647_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_IR_containsDecl___redArg(v_n_1641_, v_a_1643_);
return v___x_1649_;
}
else
{
size_t v___x_1650_; size_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = lean_usize_of_nat(v___x_1646_);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1641_, v_decls_1642_, v___x_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_IR_containsDecl___redArg(v_n_1641_, v_a_1643_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v_n_1641_);
v___x_1654_ = lean_box(v___x_1652_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1656_, lean_object* v_decls_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1656_, v_decls_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_decls_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1661_, lean_object* v_decls_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1661_, v_decls_1662_, v_a_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1667_, lean_object* v_decls_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_IR_containsDecl_x27(v_n_1667_, v_decls_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec_ref(v_decls_1668_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1673_, lean_object* v_decls_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1696_; 
lean_inc(v_n_1673_);
v___x_1678_ = l_Lean_IR_findDecl_x27___redArg(v_n_1673_, v_decls_1674_, v_a_1676_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1696_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1696_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
if (lean_obj_tag(v_a_1679_) == 1)
{
lean_object* v_val_1683_; lean_object* v___x_1685_; 
lean_dec(v_n_1673_);
v_val_1683_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_val_1683_);
lean_dec_ref(v_a_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_val_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_val_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
else
{
lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_del_object(v___x_1681_);
lean_dec(v_a_1679_);
v___x_1687_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1688_ = 1;
v___x_1689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1673_, v___x_1688_);
v___x_1690_ = lean_string_append(v___x_1687_, v___x_1689_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1692_ = lean_string_append(v___x_1690_, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
v___x_1694_ = l_Lean_MessageData_ofFormat(v___x_1693_);
v___x_1695_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1694_, v_a_1675_, v_a_1676_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1697_, lean_object* v_decls_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_IR_getDecl_x27(v_n_1697_, v_decls_1698_, v_a_1699_, v_a_1700_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v_decls_1698_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1703_, lean_object* v_declName_1704_){
_start:
{
uint8_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = 0;
v___x_1706_ = l_Lean_IR_findEnvDecl(v_env_1703_, v_declName_1704_, v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 1)
{
lean_object* v_val_1707_; 
v_val_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref(v___x_1706_);
if (lean_obj_tag(v_val_1707_) == 0)
{
lean_object* v_info_1708_; 
v_info_1708_ = lean_ctor_get(v_val_1707_, 4);
lean_inc(v_info_1708_);
lean_dec_ref(v_val_1707_);
return v_info_1708_;
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_val_1707_);
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
}
else
{
lean_object* v___x_1710_; 
lean_dec(v___x_1706_);
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1711_, uint8_t v_level_1712_, uint8_t v_includeDecls_1713_, lean_object* v_as_1714_, size_t v_i_1715_, size_t v_stop_1716_, lean_object* v_b_1717_){
_start:
{
lean_object* v___y_1719_; uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_eq(v_i_1715_, v_stop_1716_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; uint8_t v___y_1726_; 
v___x_1724_ = lean_array_uget_borrowed(v_as_1714_, v_i_1715_);
if (v_includeDecls_1713_ == 0)
{
uint8_t v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = 1;
lean_inc(v___x_1724_);
lean_inc_ref(v_env_1711_);
v___x_1735_ = l_Lean_Environment_contains(v_env_1711_, v___x_1724_, v___x_1734_);
if (v___x_1735_ == 0)
{
goto v___jp_1730_;
}
else
{
v___y_1719_ = v_b_1717_;
goto v___jp_1718_;
}
}
else
{
goto v___jp_1730_;
}
v___jp_1725_:
{
if (v___y_1726_ == 0)
{
uint8_t v___x_1727_; 
lean_inc_ref(v_env_1711_);
v___x_1727_ = l_Lean_isDeclMeta(v_env_1711_, v___x_1724_);
if (v___x_1727_ == 0)
{
v___y_1719_ = v_b_1717_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1728_; 
lean_inc(v___x_1724_);
v___x_1728_ = lean_array_push(v_b_1717_, v___x_1724_);
v___y_1719_ = v___x_1728_;
goto v___jp_1718_;
}
}
else
{
lean_object* v___x_1729_; 
lean_inc(v___x_1724_);
v___x_1729_ = lean_array_push(v_b_1717_, v___x_1724_);
v___y_1719_ = v___x_1729_;
goto v___jp_1718_;
}
}
v___jp_1730_:
{
uint8_t v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = 2;
v___x_1732_ = l_Lean_instDecidableEqOLeanLevel(v_level_1712_, v___x_1731_);
if (v___x_1732_ == 0)
{
uint8_t v___x_1733_; 
lean_inc_ref(v_env_1711_);
v___x_1733_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1711_, v___x_1724_);
v___y_1726_ = v___x_1733_;
goto v___jp_1725_;
}
else
{
v___y_1726_ = v___x_1732_;
goto v___jp_1725_;
}
}
}
else
{
lean_dec_ref(v_env_1711_);
return v_b_1717_;
}
v___jp_1718_:
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1715_, v___x_1720_);
v_i_1715_ = v___x_1721_;
v_b_1717_ = v___y_1719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1736_, lean_object* v_level_1737_, lean_object* v_includeDecls_1738_, lean_object* v_as_1739_, lean_object* v_i_1740_, lean_object* v_stop_1741_, lean_object* v_b_1742_){
_start:
{
uint8_t v_level_boxed_1743_; uint8_t v_includeDecls_boxed_1744_; size_t v_i_boxed_1745_; size_t v_stop_boxed_1746_; lean_object* v_res_1747_; 
v_level_boxed_1743_ = lean_unbox(v_level_1737_);
v_includeDecls_boxed_1744_ = lean_unbox(v_includeDecls_1738_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_stop_boxed_1746_ = lean_unbox_usize(v_stop_1741_);
lean_dec(v_stop_1741_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1736_, v_level_boxed_1743_, v_includeDecls_boxed_1744_, v_as_1739_, v_i_boxed_1745_, v_stop_boxed_1746_, v_b_1742_);
lean_dec_ref(v_as_1739_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_bs_1750_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1751_ == 0)
{
return v_bs_1750_;
}
else
{
lean_object* v_v_1752_; lean_object* v___x_1753_; lean_object* v_bs_x27_1754_; lean_object* v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_v_1752_ = lean_array_uget(v_bs_1750_, v_i_1749_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v_bs_x27_1754_ = lean_array_uset(v_bs_1750_, v_i_1749_, v___x_1753_);
v___x_1755_ = l_Lean_IR_Decl_name(v_v_1752_);
lean_dec(v_v_1752_);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1749_, v___x_1756_);
v___x_1758_ = lean_array_uset(v_bs_x27_1754_, v_i_1749_, v___x_1755_);
v_i_1749_ = v___x_1757_;
v_bs_1750_ = v___x_1758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1760_, lean_object* v_i_1761_, lean_object* v_bs_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1760_);
lean_dec(v_sz_1760_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1763_, v_i_boxed_1764_, v_bs_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1768_, uint8_t v_level_1769_, uint8_t v_includeDecls_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v_toEnvExtension_1772_; lean_object* v_asyncMode_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1771_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_ref(v_toEnvExtension_1772_);
v_asyncMode_1773_ = lean_ctor_get(v_toEnvExtension_1772_, 2);
lean_inc(v_asyncMode_1773_);
lean_dec_ref(v_toEnvExtension_1772_);
v___x_1774_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc_ref(v_env_1768_);
v___x_1775_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1774_, v___x_1771_, v_env_1768_, v_asyncMode_1773_);
lean_dec(v_asyncMode_1773_);
v___x_1776_ = lean_array_mk(v___x_1775_);
v_sz_1777_ = lean_array_size(v___x_1776_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1777_, v___x_1778_, v___x_1776_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_array_get_size(v___x_1779_);
v___x_1782_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1783_ = lean_nat_dec_lt(v___x_1780_, v___x_1781_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_env_1768_);
return v___x_1782_;
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_nat_dec_le(v___x_1781_, v___x_1781_);
if (v___x_1784_ == 0)
{
if (v___x_1783_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_env_1768_);
return v___x_1782_;
}
else
{
size_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_usize_of_nat(v___x_1781_);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1768_, v_level_1769_, v_includeDecls_1770_, v___x_1779_, v___x_1778_, v___x_1785_, v___x_1782_);
lean_dec_ref(v___x_1779_);
return v___x_1786_;
}
}
else
{
size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_usize_of_nat(v___x_1781_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1768_, v_level_1769_, v_includeDecls_1770_, v___x_1779_, v___x_1778_, v___x_1787_, v___x_1782_);
lean_dec_ref(v___x_1779_);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1789_, lean_object* v_level_1790_, lean_object* v_includeDecls_1791_){
_start:
{
uint8_t v_level_boxed_1792_; uint8_t v_includeDecls_boxed_1793_; lean_object* v_res_1794_; 
v_level_boxed_1792_ = lean_unbox(v_level_1790_);
v_includeDecls_boxed_1793_ = lean_unbox(v_includeDecls_1791_);
v_res_1794_ = lean_get_ir_extra_const_names(v_env_1789_, v_level_boxed_1792_, v_includeDecls_boxed_1793_);
return v_res_1794_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Types(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3276391492____hygCtx___hyg_2_();
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
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin);
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
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin);
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
