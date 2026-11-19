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
lean_object* v_cls_74_; lean_object* v_decls_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_101_; 
v_cls_74_ = lean_ctor_get(v_x_73_, 0);
v_decls_75_ = lean_ctor_get(v_x_73_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_101_ == 0)
{
v___x_77_ = v_x_73_;
v_isShared_78_ = v_isSharedCheck_101_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_decls_75_);
lean_inc(v_cls_74_);
lean_dec(v_x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_101_;
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
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_81_);
v___x_85_ = v_reuseFailAlloc_100_;
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
size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = ((size_t)0ULL);
v___x_97_ = lean_usize_of_nat(v___x_93_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_75_, v___x_96_, v___x_97_, v___x_91_);
lean_dec_ref(v_decls_75_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_90_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
return v___x_99_;
}
}
}
}
else
{
lean_object* v_msg_102_; 
v_msg_102_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_msg_102_);
lean_dec_ref_known(v_x_73_, 1);
return v_msg_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(lean_object* v_as_105_, size_t v_i_106_, size_t v_stop_107_, lean_object* v_b_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_usize_dec_eq(v_i_106_, v_stop_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; size_t v___x_115_; size_t v___x_116_; 
v___x_110_ = lean_array_uget_borrowed(v_as_105_, v_i_106_);
v___x_111_ = lean_box(1);
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v_b_108_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
lean_inc(v___x_110_);
v___x_113_ = l_Lean_IR_LogEntry_fmt(v___x_110_);
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_add(v_i_106_, v___x_115_);
v_i_106_ = v___x_116_;
v_b_108_ = v___x_114_;
goto _start;
}
else
{
return v_b_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(lean_object* v_as_118_, lean_object* v_i_119_, lean_object* v_stop_120_, lean_object* v_b_121_){
_start:
{
size_t v_i_boxed_122_; size_t v_stop_boxed_123_; lean_object* v_res_124_; 
v_i_boxed_122_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_stop_boxed_123_ = lean_unbox_usize(v_stop_120_);
lean_dec(v_stop_120_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_as_118_, v_i_boxed_122_, v_stop_boxed_123_, v_b_121_);
lean_dec_ref(v_as_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object* v_log_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_array_get_size(v_log_125_);
v___x_129_ = lean_nat_dec_lt(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
return v___x_126_;
}
else
{
size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((size_t)0ULL);
v___x_131_ = lean_usize_of_nat(v___x_128_);
v___x_132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_125_, v___x_130_, v___x_131_, v___x_126_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object* v_log_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_IR_Log_format(v_log_133_);
lean_dec_ref(v_log_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object* v_log_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_136_ = l_Lean_IR_Log_format(v_log_135_);
v___x_137_ = l_Std_Format_defWidth;
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = l_Std_Format_pretty(v___x_136_, v___x_137_, v___x_138_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object* v_log_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_IR_Log_toString(v_log_140_);
lean_dec_ref(v_log_140_);
return v_res_141_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
lean_ctor_set(v___x_147_, 3, v___x_146_);
lean_ctor_set(v___x_147_, 4, v___x_145_);
lean_ctor_set(v___x_147_, 5, v___x_145_);
lean_ctor_set(v___x_147_, 6, v___x_145_);
lean_ctor_set(v___x_147_, 7, v___x_145_);
lean_ctor_set(v___x_147_, 8, v___x_145_);
lean_ctor_set(v___x_147_, 9, v___x_145_);
lean_ctor_set(v___x_147_, 10, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(32u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_151_ = ((size_t)5ULL);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_unsigned_to_nat(32u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3);
v___x_156_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
lean_ctor_set(v___x_156_, 2, v___x_152_);
lean_ctor_set(v___x_156_, 3, v___x_152_);
lean_ctor_set_usize(v___x_156_, 4, v___x_151_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_box(1);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(lean_object* v_msgData_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v_toCold_166_; lean_object* v_env_167_; lean_object* v_options_168_; uint8_t v___x_169_; lean_object* v_env_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_165_ = lean_st_ref_get(v___y_163_);
v_toCold_166_ = lean_ctor_get(v___y_162_, 0);
v_env_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_165_);
v_options_168_ = lean_ctor_get(v_toCold_166_, 2);
v___x_169_ = 0;
v_env_170_ = l_Lean_Environment_setRecordingDeps(v_env_167_, v___x_169_);
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
v___x_172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_168_);
v___x_173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_173_, 0, v_env_170_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_172_);
lean_ctor_set(v___x_173_, 3, v_options_168_);
v___x_174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_msgData_161_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msgData_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0(void){
_start:
{
lean_object* v___x_181_; double v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_float_of_nat(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object* v_cls_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_238_; 
v_ref_191_ = lean_ctor_get(v___y_188_, 2);
v___x_192_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_187_, v___y_188_, v___y_189_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_238_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_238_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_238_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v_traceState_198_; lean_object* v_env_199_; lean_object* v_nextMacroScope_200_; lean_object* v_ngen_201_; lean_object* v_auxDeclNGen_202_; lean_object* v_cache_203_; lean_object* v_recordedDeps_204_; lean_object* v_messages_205_; lean_object* v_infoState_206_; lean_object* v_snapshotTasks_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_237_; 
v___x_197_ = lean_st_ref_take(v___y_189_);
v_traceState_198_ = lean_ctor_get(v___x_197_, 4);
v_env_199_ = lean_ctor_get(v___x_197_, 0);
v_nextMacroScope_200_ = lean_ctor_get(v___x_197_, 1);
v_ngen_201_ = lean_ctor_get(v___x_197_, 2);
v_auxDeclNGen_202_ = lean_ctor_get(v___x_197_, 3);
v_cache_203_ = lean_ctor_get(v___x_197_, 5);
v_recordedDeps_204_ = lean_ctor_get(v___x_197_, 6);
v_messages_205_ = lean_ctor_get(v___x_197_, 7);
v_infoState_206_ = lean_ctor_get(v___x_197_, 8);
v_snapshotTasks_207_ = lean_ctor_get(v___x_197_, 9);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_237_ == 0)
{
v___x_209_ = v___x_197_;
v_isShared_210_ = v_isSharedCheck_237_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snapshotTasks_207_);
lean_inc(v_infoState_206_);
lean_inc(v_messages_205_);
lean_inc(v_recordedDeps_204_);
lean_inc(v_cache_203_);
lean_inc(v_traceState_198_);
lean_inc(v_auxDeclNGen_202_);
lean_inc(v_ngen_201_);
lean_inc(v_nextMacroScope_200_);
lean_inc(v_env_199_);
lean_dec(v___x_197_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_237_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint64_t v_tid_211_; lean_object* v_traces_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_236_; 
v_tid_211_ = lean_ctor_get_uint64(v_traceState_198_, sizeof(void*)*1);
v_traces_212_ = lean_ctor_get(v_traceState_198_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_traceState_198_);
if (v_isSharedCheck_236_ == 0)
{
v___x_214_ = v_traceState_198_;
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_traces_212_);
lean_dec(v_traceState_198_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; double v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_box(0);
v___x_218_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_219_ = 0;
v___x_220_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_221_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_221_, 0, v_cls_186_);
lean_ctor_set(v___x_221_, 1, v___x_217_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set_float(v___x_221_, sizeof(void*)*3, v___x_218_);
lean_ctor_set_float(v___x_221_, sizeof(void*)*3 + 8, v___x_218_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*3 + 16, v___x_219_);
v___x_222_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_223_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v_a_193_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_inc(v_ref_191_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_191_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_PersistentArray_push___redArg(v_traces_212_, v___x_224_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_225_);
v___x_227_ = v___x_214_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_225_);
lean_ctor_set_uint64(v_reuseFailAlloc_235_, sizeof(void*)*1, v_tid_211_);
v___x_227_ = v_reuseFailAlloc_235_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 4, v___x_227_);
v___x_229_ = v___x_209_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_env_199_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_nextMacroScope_200_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_ngen_201_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_auxDeclNGen_202_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 5, v_cache_203_);
lean_ctor_set(v_reuseFailAlloc_234_, 6, v_recordedDeps_204_);
lean_ctor_set(v_reuseFailAlloc_234_, 7, v_messages_205_);
lean_ctor_set(v_reuseFailAlloc_234_, 8, v_infoState_206_);
lean_ctor_set(v_reuseFailAlloc_234_, 9, v_snapshotTasks_207_);
v___x_229_ = v_reuseFailAlloc_234_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_st_ref_put(v___y_189_, v___x_229_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_216_);
v___x_232_ = v___x_195_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_216_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_239_, lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_239_, v_msg_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_255_ = l_Lean_IR_LogEntry_fmt(v_entry_250_);
v___x_256_ = l_Lean_MessageData_ofFormat(v___x_255_);
v___x_257_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_254_, v___x_256_, v_a_251_, v_a_252_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_IR_log(v_entry_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_262_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_271_, lean_object* v_optName_272_){
_start:
{
lean_object* v_map_273_; lean_object* v___x_280_; 
v_map_273_ = lean_ctor_get(v_opts_271_, 0);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_273_, v_optName_272_);
if (lean_obj_tag(v___x_280_) == 1)
{
lean_object* v_val_281_; 
v_val_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v___x_280_, 1);
if (lean_obj_tag(v_val_281_) == 1)
{
uint8_t v_v_282_; 
v_v_282_ = lean_ctor_get_uint8(v_val_281_, 0);
lean_dec_ref_known(v_val_281_, 0);
return v_v_282_;
}
else
{
lean_dec(v_val_281_);
goto v___jp_274_;
}
}
else
{
lean_dec(v___x_280_);
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_276_ = 0;
v___x_277_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_273_, v___x_275_);
if (lean_obj_tag(v___x_277_) == 0)
{
return v___x_276_;
}
else
{
lean_object* v_val_278_; 
v_val_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_277_, 1);
if (lean_obj_tag(v_val_278_) == 1)
{
uint8_t v_v_279_; 
v_v_279_ = lean_ctor_get_uint8(v_val_278_, 0);
lean_dec_ref_known(v_val_278_, 0);
return v_v_279_;
}
else
{
lean_dec(v_val_278_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_283_, lean_object* v_optName_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_283_, v_optName_284_);
lean_dec(v_optName_284_);
lean_dec_ref(v_opts_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_287_, lean_object* v_cls_288_, lean_object* v_decls_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_290_);
v___x_294_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_293_, v_optName_287_);
lean_dec_ref(v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_decls_289_);
lean_dec(v_cls_288_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_cls_288_);
lean_ctor_set(v___x_297_, 1, v_decls_289_);
v___x_298_ = l_Lean_IR_log(v___x_297_, v_a_290_, v_a_291_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_299_, lean_object* v_cls_300_, lean_object* v_decls_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_299_, v_cls_300_, v_decls_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_optName_299_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_306_, lean_object* v_decl_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_306_);
v___x_312_ = l_Lean_Name_append(v___x_311_, v_cls_306_);
v___x_313_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_312_, v_cls_306_, v_decl_307_, v_a_308_, v_a_309_);
lean_dec(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_314_, lean_object* v_decl_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_IR_logDecls(v_cls_314_, v_decl_315_, v_a_316_, v_a_317_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_320_, lean_object* v_optName_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_323_);
v___x_327_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_326_, v_optName_321_);
lean_dec_ref(v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_a_322_);
lean_dec_ref(v_inst_320_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_apply_1(v_inst_320_, v_a_322_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___x_332_ = l_Lean_IR_log(v___x_331_, v_a_323_, v_a_324_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_333_, lean_object* v_optName_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_333_, v_optName_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_optName_334_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_optName_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_341_, v_optName_342_, v_a_343_, v_a_344_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_optName_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_348_, v_inst_349_, v_optName_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_optName_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_356_, lean_object* v_cls_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_363_ = l_Lean_Name_append(v___x_362_, v_cls_357_);
v___x_364_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_356_, v___x_363_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_365_, lean_object* v_cls_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_IR_logMessageIf___redArg(v_inst_365_, v_cls_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_372_, lean_object* v_inst_373_, lean_object* v_cls_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_380_ = l_Lean_Name_append(v___x_379_, v_cls_374_);
v___x_381_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_373_, v___x_380_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_cls_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_IR_logMessageIf(v_00_u03b1_382_, v_inst_383_, v_cls_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_396_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_390_, v___x_395_, v_a_391_, v_a_392_, v_a_393_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_IR_logMessage___redArg(v_inst_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_410_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_404_, v___x_409_, v_a_405_, v_a_406_, v_a_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_411_, lean_object* v_inst_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_IR_logMessage(v_00_u03b1_411_, v_inst_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_417_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = l_Lean_IR_Decl_name(v_a_418_);
v___x_421_ = l_Lean_IR_Decl_name(v_b_419_);
v___x_422_ = l_Lean_Name_quickLt(v___x_420_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v___x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_423_, lean_object* v_b_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_423_, v_b_424_);
lean_dec_ref(v_b_424_);
lean_dec_ref(v_a_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_array_get_size(v_decls_428_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_nat_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___y_436_; uint8_t v___x_440_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_sub(v___x_429_, v___x_433_);
v___x_440_ = lean_nat_dec_le(v___x_430_, v___x_434_);
if (v___x_440_ == 0)
{
lean_inc(v___x_434_);
v___y_436_ = v___x_434_;
goto v___jp_435_;
}
else
{
v___y_436_ = v___x_430_;
goto v___jp_435_;
}
v___jp_435_:
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_le(v___y_436_, v___x_434_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_dec(v___x_434_);
lean_inc(v___y_436_);
v___x_438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_432_, v___x_429_, v_decls_428_, v___y_436_, v___y_436_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_436_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_432_, v___x_429_, v_decls_428_, v___y_436_, v___x_434_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_434_);
return v___x_439_;
}
}
}
else
{
return v_decls_428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_444_, lean_object* v_declName_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_array_get_size(v_decls_444_);
v___x_448_ = lean_nat_dec_lt(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_declName_445_);
v___x_449_ = lean_box(0);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_sub(v___x_447_, v___x_450_);
v___x_452_ = lean_nat_dec_le(v___x_446_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v___x_451_);
lean_dec(v_declName_445_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_tmpDecl_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_455_ = lean_box(0);
v___x_456_ = lean_box(0);
v_tmpDecl_457_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_457_, 0, v_declName_445_);
lean_ctor_set(v_tmpDecl_457_, 1, v___x_454_);
lean_ctor_set(v_tmpDecl_457_, 2, v___x_455_);
lean_ctor_set(v_tmpDecl_457_, 3, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_459_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_460_ = l_Array_binSearchAux___redArg(v___x_458_, v___x_459_, v_decls_444_, v_tmpDecl_457_, v___x_446_, v___x_451_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_461_, lean_object* v_declName_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_461_, v_declName_462_);
lean_dec_ref(v_decls_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_464_, lean_object* v_pivot_465_, lean_object* v_as_466_, lean_object* v_i_467_, lean_object* v_k_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_nat_dec_lt(v_k_468_, v_hi_464_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_k_468_);
v___x_470_ = lean_array_fswap(v_as_466_, v_i_467_, v_hi_464_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_i_467_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_array_fget_borrowed(v_as_466_, v_k_468_);
v___x_473_ = l_Lean_IR_Decl_name(v___x_472_);
v___x_474_ = l_Lean_IR_Decl_name(v_pivot_465_);
v___x_475_ = l_Lean_Name_quickLt(v___x_473_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_473_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_k_468_, v___x_476_);
lean_dec(v_k_468_);
v_k_468_ = v___x_477_;
goto _start;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_array_fswap(v_as_466_, v_i_467_, v_k_468_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_i_467_, v___x_480_);
lean_dec(v_i_467_);
v___x_482_ = lean_nat_add(v_k_468_, v___x_480_);
lean_dec(v_k_468_);
v_as_466_ = v___x_479_;
v_i_467_ = v___x_481_;
v_k_468_ = v___x_482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_484_, lean_object* v_pivot_485_, lean_object* v_as_486_, lean_object* v_i_487_, lean_object* v_k_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_484_, v_pivot_485_, v_as_486_, v_i_487_, v_k_488_);
lean_dec_ref(v_pivot_485_);
lean_dec(v_hi_484_);
return v_res_489_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = l_Lean_IR_Decl_name(v___y_490_);
v___x_493_ = l_Lean_IR_Decl_name(v___y_491_);
v___x_494_ = l_Lean_Name_quickLt(v___x_492_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_495_, v___y_496_);
lean_dec_ref(v___y_496_);
lean_dec_ref(v___y_495_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_499_, lean_object* v_as_500_, lean_object* v_lo_501_, lean_object* v_hi_502_){
_start:
{
lean_object* v___y_504_; uint8_t v___x_514_; 
v___x_514_ = lean_nat_dec_lt(v_lo_501_, v_hi_502_);
if (v___x_514_ == 0)
{
lean_dec(v_lo_501_);
return v_as_500_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_mid_517_; lean_object* v___y_519_; lean_object* v___y_525_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_515_ = lean_nat_add(v_lo_501_, v_hi_502_);
v___x_516_ = lean_unsigned_to_nat(1u);
v_mid_517_ = lean_nat_shiftr(v___x_515_, v___x_516_);
lean_dec(v___x_515_);
v___x_530_ = lean_array_fget_borrowed(v_as_500_, v_mid_517_);
v___x_531_ = lean_array_fget_borrowed(v_as_500_, v_lo_501_);
v___x_532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
v___y_525_ = v_as_500_;
goto v___jp_524_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_array_fswap(v_as_500_, v_lo_501_, v_mid_517_);
v___y_525_ = v___x_533_;
goto v___jp_524_;
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_array_fget_borrowed(v___y_519_, v_mid_517_);
v___x_521_ = lean_array_fget_borrowed(v___y_519_, v_hi_502_);
v___x_522_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec(v_mid_517_);
v___y_504_ = v___y_519_;
goto v___jp_503_;
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_array_fswap(v___y_519_, v_mid_517_, v_hi_502_);
lean_dec(v_mid_517_);
v___y_504_ = v___x_523_;
goto v___jp_503_;
}
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_array_fget_borrowed(v___y_525_, v_hi_502_);
v___x_527_ = lean_array_fget_borrowed(v___y_525_, v_lo_501_);
v___x_528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
v___y_519_ = v___y_525_;
goto v___jp_518_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = lean_array_fswap(v___y_525_, v_lo_501_, v_hi_502_);
v___y_519_ = v___x_529_;
goto v___jp_518_;
}
}
}
v___jp_503_:
{
lean_object* v_pivot_505_; lean_object* v___x_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; uint8_t v___x_509_; 
v_pivot_505_ = lean_array_fget(v___y_504_, v_hi_502_);
lean_inc_n(v_lo_501_, 2);
v___x_506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_502_, v_pivot_505_, v___y_504_, v_lo_501_, v_lo_501_);
lean_dec(v_pivot_505_);
v_fst_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_fst_507_);
v_snd_508_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_snd_508_);
lean_dec_ref(v___x_506_);
v___x_509_ = lean_nat_dec_le(v_hi_502_, v_fst_507_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_499_, v_snd_508_, v_lo_501_, v_fst_507_);
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_add(v_fst_507_, v___x_511_);
lean_dec(v_fst_507_);
v_as_500_ = v___x_510_;
v_lo_501_ = v___x_512_;
goto _start;
}
else
{
lean_dec(v_fst_507_);
lean_dec(v_lo_501_);
return v_snd_508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_534_, lean_object* v_as_535_, lean_object* v_lo_536_, lean_object* v_hi_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_534_, v_as_535_, v_lo_536_, v_hi_537_);
lean_dec(v_hi_537_);
lean_dec(v_n_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_545_, lean_object* v_as_546_, size_t v_i_547_, size_t v_stop_548_, lean_object* v_b_549_){
_start:
{
lean_object* v___y_551_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___x_562_; 
v___x_562_ = lean_usize_dec_eq(v_i_547_, v_stop_548_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_563_ = lean_array_uget_borrowed(v_as_546_, v_i_547_);
v___x_578_ = l_Lean_IR_Decl_name(v___x_563_);
lean_inc_ref(v_env_545_);
v___x_579_ = l_Lean_isDeclMeta(v_env_545_, v___x_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; 
lean_inc_ref(v_env_545_);
v___x_580_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_545_, v___x_578_);
if (v___x_580_ == 0)
{
lean_dec(v___x_578_);
v___y_551_ = v_b_549_;
goto v___jp_550_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_578_);
if (v___x_581_ == 0)
{
lean_dec(v___x_578_);
goto v___jp_564_;
}
else
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = l_Lean_Name_getPrefix(v___x_578_);
lean_dec(v___x_578_);
lean_inc_ref(v_env_545_);
v___x_583_ = l_Lean_isExtern(v_env_545_, v___x_582_);
if (v___x_583_ == 0)
{
goto v___jp_564_;
}
else
{
lean_object* v___x_584_; 
lean_inc(v___x_563_);
v___x_584_ = lean_array_push(v_b_549_, v___x_563_);
v___y_551_ = v___x_584_;
goto v___jp_550_;
}
}
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v___x_578_);
lean_inc(v___x_563_);
v___x_585_ = lean_array_push(v_b_549_, v___x_563_);
v___y_551_ = v___x_585_;
goto v___jp_550_;
}
v___jp_564_:
{
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_f_565_; lean_object* v_xs_566_; lean_object* v_type_567_; lean_object* v___x_568_; 
v_f_565_ = lean_ctor_get(v___x_563_, 0);
v_xs_566_ = lean_ctor_get(v___x_563_, 1);
v_type_567_ = lean_ctor_get(v___x_563_, 2);
lean_inc(v_f_565_);
lean_inc_ref(v_env_545_);
v___x_568_ = lean_get_export_name_for(v_env_545_, v_f_565_);
if (lean_obj_tag(v___x_568_) == 1)
{
lean_object* v_val_569_; 
v_val_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_569_);
lean_dec_ref_known(v___x_568_, 1);
if (lean_obj_tag(v_val_569_) == 1)
{
lean_object* v_str_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_str_570_ = lean_ctor_get(v_val_569_, 1);
lean_inc_ref(v_str_570_);
lean_dec_ref_known(v_val_569_, 2);
v___x_571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_str_570_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_inc(v_type_567_);
lean_inc_ref(v_xs_566_);
lean_inc(v_f_565_);
v___x_575_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_575_, 0, v_f_565_);
lean_ctor_set(v___x_575_, 1, v_xs_566_);
lean_ctor_set(v___x_575_, 2, v_type_567_);
lean_ctor_set(v___x_575_, 3, v___x_574_);
v___x_576_ = lean_array_push(v_b_549_, v___x_575_);
v___y_551_ = v___x_576_;
goto v___jp_550_;
}
else
{
lean_dec(v_val_569_);
lean_inc(v_f_565_);
lean_inc(v_type_567_);
lean_inc_ref(v_xs_566_);
v___y_556_ = v_xs_566_;
v___y_557_ = v_type_567_;
v___y_558_ = v_f_565_;
goto v___jp_555_;
}
}
else
{
lean_dec(v___x_568_);
lean_inc(v_f_565_);
lean_inc(v_type_567_);
lean_inc_ref(v_xs_566_);
v___y_556_ = v_xs_566_;
v___y_557_ = v_type_567_;
v___y_558_ = v_f_565_;
goto v___jp_555_;
}
}
else
{
lean_object* v___x_577_; 
lean_inc(v___x_563_);
v___x_577_ = lean_array_push(v_b_549_, v___x_563_);
v___y_551_ = v___x_577_;
goto v___jp_550_;
}
}
}
else
{
lean_dec_ref(v_env_545_);
return v_b_549_;
}
v___jp_550_:
{
size_t v___x_552_; size_t v___x_553_; 
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_add(v_i_547_, v___x_552_);
v_i_547_ = v___x_553_;
v_b_549_ = v___y_551_;
goto _start;
}
v___jp_555_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_560_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_560_, 0, v___y_558_);
lean_ctor_set(v___x_560_, 1, v___y_556_);
lean_ctor_set(v___x_560_, 2, v___y_557_);
lean_ctor_set(v___x_560_, 3, v___x_559_);
v___x_561_ = lean_array_push(v_b_549_, v___x_560_);
v___y_551_ = v___x_561_;
goto v___jp_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_586_, lean_object* v_as_587_, lean_object* v_i_588_, lean_object* v_stop_589_, lean_object* v_b_590_){
_start:
{
size_t v_i_boxed_591_; size_t v_stop_boxed_592_; lean_object* v_res_593_; 
v_i_boxed_591_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_stop_boxed_592_ = lean_unbox_usize(v_stop_589_);
lean_dec(v_stop_589_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_586_, v_as_587_, v_i_boxed_591_, v_stop_boxed_592_, v_b_590_);
lean_dec_ref(v_as_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(lean_object* v_env_596_, lean_object* v_as_597_, lean_object* v_start_598_, lean_object* v_stop_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v___x_601_ = lean_nat_dec_lt(v_start_598_, v_stop_599_);
if (v___x_601_ == 0)
{
lean_dec_ref(v_env_596_);
return v___x_600_;
}
else
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_array_get_size(v_as_597_);
v___x_603_ = lean_nat_dec_le(v_stop_599_, v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_lt(v_start_598_, v___x_602_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_env_596_);
return v___x_600_;
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_usize_of_nat(v_start_598_);
v___x_606_ = lean_usize_of_nat(v___x_602_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_596_, v_as_597_, v___x_605_, v___x_606_, v___x_600_);
return v___x_607_;
}
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_usize_of_nat(v_start_598_);
v___x_609_ = lean_usize_of_nat(v_stop_599_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_596_, v_as_597_, v___x_608_, v___x_609_, v___x_600_);
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_611_, lean_object* v_as_612_, lean_object* v_start_613_, lean_object* v_stop_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_611_, v_as_612_, v_start_613_, v_stop_614_);
lean_dec(v_stop_614_);
lean_dec(v_start_613_);
lean_dec_ref(v_as_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
return v_x_616_;
}
else
{
lean_object* v_head_618_; lean_object* v_tail_619_; lean_object* v___x_620_; 
v_head_618_ = lean_ctor_get(v_x_617_, 0);
lean_inc(v_head_618_);
v_tail_619_ = lean_ctor_get(v_x_617_, 1);
lean_inc(v_tail_619_);
lean_dec_ref_known(v_x_617_, 2);
v___x_620_ = lean_array_push(v_x_616_, v_head_618_);
v_x_616_ = v___x_620_;
v_x_617_ = v_tail_619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_env_622_, lean_object* v_s_623_, lean_object* v_entries_624_){
_start:
{
lean_object* v___y_626_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_decls_636_; lean_object* v___x_637_; lean_object* v___y_639_; lean_object* v___y_640_; uint8_t v___x_642_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
v_decls_636_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_635_, v_entries_624_);
v___x_637_ = lean_array_get_size(v_decls_636_);
v___x_642_ = lean_nat_dec_eq(v___x_637_, v___x_634_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___y_646_; uint8_t v___x_648_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_sub(v___x_637_, v___x_643_);
v___x_648_ = lean_nat_dec_le(v___x_634_, v___x_644_);
if (v___x_648_ == 0)
{
lean_inc(v___x_644_);
v___y_646_ = v___x_644_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___x_634_;
goto v___jp_645_;
}
v___jp_645_:
{
uint8_t v___x_647_; 
v___x_647_ = lean_nat_dec_le(v___y_646_, v___x_644_);
if (v___x_647_ == 0)
{
lean_dec(v___x_644_);
lean_inc(v___y_646_);
v___y_639_ = v___y_646_;
v___y_640_ = v___y_646_;
goto v___jp_638_;
}
else
{
v___y_639_ = v___y_646_;
v___y_640_ = v___x_644_;
goto v___jp_638_;
}
}
}
else
{
v___y_626_ = v_decls_636_;
goto v___jp_625_;
}
v___jp_625_:
{
lean_object* v___x_627_; uint8_t v_isModule_628_; 
v___x_627_ = l_Lean_Environment_header(v_env_622_);
v_isModule_628_ = lean_ctor_get_uint8(v___x_627_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_627_);
if (v_isModule_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec_ref(v_env_622_);
lean_inc_ref_n(v___y_626_, 2);
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v___y_626_);
lean_ctor_set(v___x_629_, 1, v___y_626_);
lean_ctor_set(v___x_629_, 2, v___y_626_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_array_get_size(v___y_626_);
v___x_632_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_622_, v___y_626_, v___x_630_, v___x_631_);
lean_dec_ref(v___y_626_);
lean_inc_ref_n(v___x_632_, 2);
v___x_633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
return v___x_633_;
}
}
v___jp_638_:
{
lean_object* v___x_641_; 
v___x_641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_637_, v_decls_636_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
v___y_626_ = v___x_641_;
goto v___jp_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_env_649_, lean_object* v_s_650_, lean_object* v_entries_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_649_, v_s_650_, v_entries_651_);
lean_dec_ref(v_s_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_es_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_array_mk(v_es_653_);
return v___x_654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(lean_object* v_keys_655_, lean_object* v_i_656_, lean_object* v_k_657_){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_array_get_size(v_keys_655_);
v___x_659_ = lean_nat_dec_lt(v_i_656_, v___x_658_);
if (v___x_659_ == 0)
{
lean_dec(v_i_656_);
return v___x_659_;
}
else
{
lean_object* v_k_x27_660_; uint8_t v___x_661_; 
v_k_x27_660_ = lean_array_fget_borrowed(v_keys_655_, v_i_656_);
v___x_661_ = lean_name_eq(v_k_657_, v_k_x27_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = lean_nat_add(v_i_656_, v___x_662_);
lean_dec(v_i_656_);
v_i_656_ = v___x_663_;
goto _start;
}
else
{
lean_dec(v_i_656_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_665_, lean_object* v_i_666_, lean_object* v_k_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_665_, v_i_666_, v_k_667_);
lean_dec(v_k_667_);
lean_dec_ref(v_keys_665_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_670_, size_t v_x_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v_es_673_; lean_object* v___x_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v_j_677_; lean_object* v___x_678_; 
v_es_673_ = lean_ctor_get(v_x_670_, 0);
v___x_674_ = lean_box(2);
v___x_675_ = ((size_t)31ULL);
v___x_676_ = lean_usize_land(v_x_671_, v___x_675_);
v_j_677_ = lean_usize_to_nat(v___x_676_);
v___x_678_ = lean_array_get_borrowed(v___x_674_, v_es_673_, v_j_677_);
lean_dec(v_j_677_);
switch(lean_obj_tag(v___x_678_))
{
case 0:
{
lean_object* v_key_679_; uint8_t v___x_680_; 
v_key_679_ = lean_ctor_get(v___x_678_, 0);
v___x_680_ = lean_name_eq(v_x_672_, v_key_679_);
return v___x_680_;
}
case 1:
{
lean_object* v_node_681_; size_t v___x_682_; size_t v___x_683_; 
v_node_681_ = lean_ctor_get(v___x_678_, 0);
v___x_682_ = ((size_t)5ULL);
v___x_683_ = lean_usize_shift_right(v_x_671_, v___x_682_);
v_x_670_ = v_node_681_;
v_x_671_ = v___x_683_;
goto _start;
}
default: 
{
uint8_t v___x_685_; 
v___x_685_ = 0;
return v___x_685_;
}
}
}
else
{
lean_object* v_ks_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_ks_686_ = lean_ctor_get(v_x_670_, 0);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_686_, v___x_687_, v_x_672_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
size_t v_x_2190__boxed_692_; uint8_t v_res_693_; lean_object* v_r_694_; 
v_x_2190__boxed_692_ = lean_unbox_usize(v_x_690_);
lean_dec(v_x_690_);
v_res_693_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_689_, v_x_2190__boxed_692_, v_x_691_);
lean_dec(v_x_691_);
lean_dec_ref(v_x_689_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
uint64_t v___y_698_; 
if (lean_obj_tag(v_x_696_) == 0)
{
uint64_t v___x_701_; 
v___x_701_ = 1723ULL;
v___y_698_ = v___x_701_;
goto v___jp_697_;
}
else
{
uint64_t v_hash_702_; 
v_hash_702_ = lean_ctor_get_uint64(v_x_696_, sizeof(void*)*2);
v___y_698_ = v_hash_702_;
goto v___jp_697_;
}
v___jp_697_:
{
size_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_uint64_to_usize(v___y_698_);
v___x_700_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_695_, v___x_699_, v_x_696_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_703_, v_x_704_);
lean_dec(v_x_704_);
lean_dec_ref(v_x_703_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x1_707_, lean_object* v_x2_708_){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = l_Lean_IR_Decl_name(v_x2_708_);
v___x_710_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_707_, v___x_709_);
lean_dec(v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = 1;
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 0;
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x1_713_, lean_object* v_x2_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_713_, v_x2_714_);
lean_dec_ref(v_x2_714_);
lean_dec_ref(v_x1_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_x_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_721_);
lean_dec_ref(v_x_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_ks_727_; lean_object* v_vs_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_752_; 
v_ks_727_ = lean_ctor_get(v_x_723_, 0);
v_vs_728_ = lean_ctor_get(v_x_723_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_723_);
if (v_isSharedCheck_752_ == 0)
{
v___x_730_ = v_x_723_;
v_isShared_731_ = v_isSharedCheck_752_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_vs_728_);
lean_inc(v_ks_727_);
lean_dec(v_x_723_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_752_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_get_size(v_ks_727_);
v___x_733_ = lean_nat_dec_lt(v_x_724_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec(v_x_724_);
v___x_734_ = lean_array_push(v_ks_727_, v_x_725_);
v___x_735_ = lean_array_push(v_vs_728_, v_x_726_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_735_);
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v_k_x27_739_; uint8_t v___x_740_; 
v_k_x27_739_ = lean_array_fget_borrowed(v_ks_727_, v_x_724_);
v___x_740_ = lean_name_eq(v_x_725_, v_k_x27_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_742_; 
if (v_isShared_731_ == 0)
{
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_ks_727_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_vs_728_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_x_724_, v___x_743_);
lean_dec(v_x_724_);
v_x_723_ = v___x_742_;
v_x_724_ = v___x_744_;
goto _start;
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_array_fset(v_ks_727_, v_x_724_, v_x_725_);
v___x_748_ = lean_array_fset(v_vs_728_, v_x_724_, v_x_726_);
lean_dec(v_x_724_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_748_);
lean_ctor_set(v___x_730_, 0, v___x_747_);
v___x_750_ = v___x_730_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(lean_object* v_n_753_, lean_object* v_k_754_, lean_object* v_v_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_753_, v___x_756_, v_k_754_, v_v_755_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(lean_object* v_x_759_, size_t v_x_760_, size_t v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v_es_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v_j_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_es_764_ = lean_ctor_get(v_x_759_, 0);
v___x_765_ = ((size_t)31ULL);
v___x_766_ = lean_usize_land(v_x_760_, v___x_765_);
v_j_767_ = lean_usize_to_nat(v___x_766_);
v___x_768_ = lean_array_get_size(v_es_764_);
v___x_769_ = lean_nat_dec_lt(v_j_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec(v_j_767_);
lean_dec(v_x_763_);
lean_dec(v_x_762_);
return v_x_759_;
}
else
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_808_; 
lean_inc_ref(v_es_764_);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_x_759_, 0);
lean_dec(v_unused_809_);
v___x_771_ = v_x_759_;
v_isShared_772_ = v_isSharedCheck_808_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_x_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_808_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_v_773_; lean_object* v___x_774_; lean_object* v_xs_x27_775_; lean_object* v___y_777_; 
v_v_773_ = lean_array_fget(v_es_764_, v_j_767_);
v___x_774_ = lean_box(0);
v_xs_x27_775_ = lean_array_fset(v_es_764_, v_j_767_, v___x_774_);
switch(lean_obj_tag(v_v_773_))
{
case 0:
{
lean_object* v_key_782_; lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_793_; 
v_key_782_ = lean_ctor_get(v_v_773_, 0);
v_val_783_ = lean_ctor_get(v_v_773_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_v_773_);
if (v_isSharedCheck_793_ == 0)
{
v___x_785_ = v_v_773_;
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_inc(v_key_782_);
lean_dec(v_v_773_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
uint8_t v___x_787_; 
v___x_787_ = lean_name_eq(v_x_762_, v_key_782_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_785_);
v___x_788_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_782_, v_val_783_, v_x_762_, v_x_763_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___y_777_ = v___x_789_;
goto v___jp_776_;
}
else
{
lean_object* v___x_791_; 
lean_dec(v_val_783_);
lean_dec(v_key_782_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v_x_763_);
lean_ctor_set(v___x_785_, 0, v_x_762_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_x_762_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_x_763_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v___y_777_ = v___x_791_;
goto v___jp_776_;
}
}
}
}
case 1:
{
lean_object* v_node_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_806_; 
v_node_794_ = lean_ctor_get(v_v_773_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_v_773_);
if (v_isSharedCheck_806_ == 0)
{
v___x_796_ = v_v_773_;
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_node_794_);
lean_dec(v_v_773_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_shift_right(v_x_760_, v___x_798_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_x_761_, v___x_800_);
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_794_, v___x_799_, v___x_801_, v_x_762_, v_x_763_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_802_);
v___x_804_ = v___x_796_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_777_ = v___x_804_;
goto v___jp_776_;
}
}
}
default: 
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_x_762_);
lean_ctor_set(v___x_807_, 1, v_x_763_);
v___y_777_ = v___x_807_;
goto v___jp_776_;
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_array_fset(v_xs_x27_775_, v_j_767_, v___y_777_);
lean_dec(v_j_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_778_);
v___x_780_ = v___x_771_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
else
{
lean_object* v_ks_810_; lean_object* v_vs_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_829_; 
v_ks_810_ = lean_ctor_get(v_x_759_, 0);
v_vs_811_ = lean_ctor_get(v_x_759_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_829_ == 0)
{
v___x_813_ = v_x_759_;
v_isShared_814_ = v_isSharedCheck_829_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_vs_811_);
lean_inc(v_ks_810_);
lean_dec(v_x_759_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_829_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_ks_810_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_vs_811_);
v___x_816_ = v_reuseFailAlloc_828_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v_newNode_817_; size_t v___x_818_; uint8_t v___x_819_; 
v_newNode_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_816_, v_x_762_, v_x_763_);
v___x_818_ = ((size_t)7ULL);
v___x_819_ = lean_usize_dec_le(v___x_818_, v_x_761_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_817_);
v___x_821_ = lean_unsigned_to_nat(4u);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
lean_dec(v___x_820_);
if (v___x_822_ == 0)
{
lean_object* v_ks_823_; lean_object* v_vs_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_ks_823_ = lean_ctor_get(v_newNode_817_, 0);
lean_inc_ref(v_ks_823_);
v_vs_824_ = lean_ctor_get(v_newNode_817_, 1);
lean_inc_ref(v_vs_824_);
lean_dec_ref(v_newNode_817_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
v___x_827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_761_, v_ks_823_, v_vs_824_, v___x_825_, v___x_826_);
lean_dec_ref(v_vs_824_);
lean_dec_ref(v_ks_823_);
return v___x_827_;
}
else
{
return v_newNode_817_;
}
}
else
{
return v_newNode_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(size_t v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_i_833_, lean_object* v_entries_834_){
_start:
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_array_get_size(v_keys_831_);
v___x_836_ = lean_nat_dec_lt(v_i_833_, v___x_835_);
if (v___x_836_ == 0)
{
lean_dec(v_i_833_);
return v_entries_834_;
}
else
{
lean_object* v_k_837_; lean_object* v_v_838_; uint64_t v___y_840_; 
v_k_837_ = lean_array_fget_borrowed(v_keys_831_, v_i_833_);
v_v_838_ = lean_array_fget_borrowed(v_vals_832_, v_i_833_);
if (lean_obj_tag(v_k_837_) == 0)
{
uint64_t v___x_851_; 
v___x_851_ = 1723ULL;
v___y_840_ = v___x_851_;
goto v___jp_839_;
}
else
{
uint64_t v_hash_852_; 
v_hash_852_ = lean_ctor_get_uint64(v_k_837_, sizeof(void*)*2);
v___y_840_ = v_hash_852_;
goto v___jp_839_;
}
v___jp_839_:
{
size_t v_h_841_; size_t v___x_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v_h_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_h_841_ = lean_uint64_to_usize(v___y_840_);
v___x_842_ = ((size_t)5ULL);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_sub(v_depth_830_, v___x_844_);
v___x_846_ = lean_usize_mul(v___x_842_, v___x_845_);
v_h_847_ = lean_usize_shift_right(v_h_841_, v___x_846_);
v___x_848_ = lean_nat_add(v_i_833_, v___x_843_);
lean_dec(v_i_833_);
lean_inc(v_v_838_);
lean_inc(v_k_837_);
v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_834_, v_h_847_, v_depth_830_, v_k_837_, v_v_838_);
v_i_833_ = v___x_848_;
v_entries_834_ = v___x_849_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_853_, lean_object* v_keys_854_, lean_object* v_vals_855_, lean_object* v_i_856_, lean_object* v_entries_857_){
_start:
{
size_t v_depth_boxed_858_; lean_object* v_res_859_; 
v_depth_boxed_858_ = lean_unbox_usize(v_depth_853_);
lean_dec(v_depth_853_);
v_res_859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_858_, v_keys_854_, v_vals_855_, v_i_856_, v_entries_857_);
lean_dec_ref(v_vals_855_);
lean_dec_ref(v_keys_854_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
size_t v_x_2351__boxed_865_; size_t v_x_2352__boxed_866_; lean_object* v_res_867_; 
v_x_2351__boxed_865_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_x_2352__boxed_866_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_860_, v_x_2351__boxed_865_, v_x_2352__boxed_866_, v_x_863_, v_x_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
uint64_t v___y_872_; 
if (lean_obj_tag(v_x_869_) == 0)
{
uint64_t v___x_876_; 
v___x_876_ = 1723ULL;
v___y_872_ = v___x_876_;
goto v___jp_871_;
}
else
{
uint64_t v_hash_877_; 
v_hash_877_ = lean_ctor_get_uint64(v_x_869_, sizeof(void*)*2);
v___y_872_ = v_hash_877_;
goto v___jp_871_;
}
v___jp_871_:
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_uint64_to_usize(v___y_872_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_868_, v___x_873_, v___x_874_, v_x_869_, v_x_870_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(lean_object* v_s_878_, lean_object* v_d_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = l_Lean_IR_Decl_name(v_d_879_);
v___x_881_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_878_, v___x_880_, v_d_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_));
v___x_911_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(lean_object* v_n_914_, lean_object* v_as_915_, lean_object* v_lo_916_, lean_object* v_hi_917_, lean_object* v_w_918_, lean_object* v_hlo_919_, lean_object* v_hhi_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_914_, v_as_915_, v_lo_916_, v_hi_917_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_922_, lean_object* v_as_923_, lean_object* v_lo_924_, lean_object* v_hi_925_, lean_object* v_w_926_, lean_object* v_hlo_927_, lean_object* v_hhi_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_922_, v_as_923_, v_lo_924_, v_hi_925_, v_w_926_, v_hlo_927_, v_hhi_928_);
lean_dec(v_hi_925_);
lean_dec(v_n_922_);
return v_res_929_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_934_, v_x_935_, v_x_936_);
lean_dec(v_x_936_);
lean_dec_ref(v_x_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_940_, v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_944_, lean_object* v_lo_945_, lean_object* v_hi_946_, lean_object* v_hhi_947_, lean_object* v_pivot_948_, lean_object* v_as_949_, lean_object* v_i_950_, lean_object* v_k_951_, lean_object* v_ilo_952_, lean_object* v_ik_953_, lean_object* v_w_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_946_, v_pivot_948_, v_as_949_, v_i_950_, v_k_951_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_956_, lean_object* v_lo_957_, lean_object* v_hi_958_, lean_object* v_hhi_959_, lean_object* v_pivot_960_, lean_object* v_as_961_, lean_object* v_i_962_, lean_object* v_k_963_, lean_object* v_ilo_964_, lean_object* v_ik_965_, lean_object* v_w_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_956_, v_lo_957_, v_hi_958_, v_hhi_959_, v_pivot_960_, v_as_961_, v_i_962_, v_k_963_, v_ilo_964_, v_ik_965_, v_w_966_);
lean_dec_ref(v_pivot_960_);
lean_dec(v_hi_958_);
lean_dec(v_lo_957_);
lean_dec(v_n_956_);
return v_res_967_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_968_, lean_object* v_x_969_, size_t v_x_970_, lean_object* v_x_971_){
_start:
{
uint8_t v___x_972_; 
v___x_972_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_969_, v_x_970_, v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
size_t v_x_2636__boxed_977_; uint8_t v_res_978_; lean_object* v_r_979_; 
v_x_2636__boxed_977_ = lean_unbox_usize(v_x_975_);
lean_dec(v_x_975_);
v_res_978_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_973_, v_x_974_, v_x_2636__boxed_977_, v_x_976_);
lean_dec(v_x_976_);
lean_dec_ref(v_x_974_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, size_t v_x_982_, size_t v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_981_, v_x_982_, v_x_983_, v_x_984_, v_x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
size_t v_x_2647__boxed_993_; size_t v_x_2648__boxed_994_; lean_object* v_res_995_; 
v_x_2647__boxed_993_ = lean_unbox_usize(v_x_989_);
lean_dec(v_x_989_);
v_x_2648__boxed_994_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_res_995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_987_, v_x_988_, v_x_2647__boxed_993_, v_x_2648__boxed_994_, v_x_991_, v_x_992_);
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(lean_object* v_00_u03b2_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_heq_999_, lean_object* v_i_1000_, lean_object* v_k_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_997_, v_i_1000_, v_k_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_keys_1004_, lean_object* v_vals_1005_, lean_object* v_heq_1006_, lean_object* v_i_1007_, lean_object* v_k_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_1003_, v_keys_1004_, v_vals_1005_, v_heq_1006_, v_i_1007_, v_k_1008_);
lean_dec(v_k_1008_);
lean_dec_ref(v_vals_1005_);
lean_dec_ref(v_keys_1004_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1011_, lean_object* v_n_1012_, lean_object* v_k_1013_, lean_object* v_v_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_1012_, v_k_1013_, v_v_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1016_, size_t v_depth_1017_, lean_object* v_keys_1018_, lean_object* v_vals_1019_, lean_object* v_heq_1020_, lean_object* v_i_1021_, lean_object* v_entries_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_1017_, v_keys_1018_, v_vals_1019_, v_i_1021_, v_entries_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1024_, lean_object* v_depth_1025_, lean_object* v_keys_1026_, lean_object* v_vals_1027_, lean_object* v_heq_1028_, lean_object* v_i_1029_, lean_object* v_entries_1030_){
_start:
{
size_t v_depth_boxed_1031_; lean_object* v_res_1032_; 
v_depth_boxed_1031_ = lean_unbox_usize(v_depth_1025_);
lean_dec(v_depth_1025_);
v_res_1032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_1024_, v_depth_boxed_1031_, v_keys_1026_, v_vals_1027_, v_heq_1028_, v_i_1029_, v_entries_1030_);
lean_dec_ref(v_vals_1027_);
lean_dec_ref(v_keys_1026_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_1034_, v_x_1035_, v_x_1036_, v_x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = lean_array_get_size(v_irDecls_1039_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_nat_dec_eq(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___y_1047_; uint8_t v___x_1051_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_sub(v___x_1040_, v___x_1044_);
v___x_1051_ = lean_nat_dec_le(v___x_1041_, v___x_1045_);
if (v___x_1051_ == 0)
{
lean_inc(v___x_1045_);
v___y_1047_ = v___x_1045_;
goto v___jp_1046_;
}
else
{
v___y_1047_ = v___x_1041_;
goto v___jp_1046_;
}
v___jp_1046_:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_nat_dec_le(v___y_1047_, v___x_1045_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v___x_1045_);
lean_inc(v___y_1047_);
v___x_1049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1043_, v___x_1040_, v_irDecls_1039_, v___y_1047_, v___y_1047_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1047_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1043_, v___x_1040_, v_irDecls_1039_, v___y_1047_, v___x_1045_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_1045_);
return v___x_1050_;
}
}
}
else
{
return v_irDecls_1039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1052_){
_start:
{
lean_inc_ref(v_initDecls_1052_);
return v_initDecls_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1053_);
lean_dec_ref(v_initDecls_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1055_){
_start:
{
lean_inc_ref(v_modPkg_1055_);
return v_modPkg_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1056_);
lean_dec_ref(v_modPkg_1056_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0(void){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v_toEnvExtension_1064_; lean_object* v_name_1065_; lean_object* v_asyncMode_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___y_1071_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_irDecls_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___x_1108_; 
v___x_1063_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1064_ = lean_ctor_get(v___x_1063_, 0);
v_name_1065_ = lean_ctor_get(v___x_1063_, 1);
v_asyncMode_1066_ = lean_ctor_get(v_toEnvExtension_1064_, 2);
v___x_1067_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1068_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1069_ = lean_box(0);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1062_);
v___x_1101_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1067_, v___x_1063_, v_env_1062_, v_asyncMode_1066_);
v_irDecls_1102_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1100_, v___x_1101_);
v___x_1103_ = lean_array_get_size(v_irDecls_1102_);
v___x_1108_ = lean_nat_dec_eq(v___x_1103_, v___x_1099_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___y_1112_; uint8_t v___x_1114_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_sub(v___x_1103_, v___x_1109_);
v___x_1114_ = lean_nat_dec_le(v___x_1099_, v___x_1110_);
if (v___x_1114_ == 0)
{
lean_inc(v___x_1110_);
v___y_1112_ = v___x_1110_;
goto v___jp_1111_;
}
else
{
v___y_1112_ = v___x_1099_;
goto v___jp_1111_;
}
v___jp_1111_:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_nat_dec_le(v___y_1112_, v___x_1110_);
if (v___x_1113_ == 0)
{
lean_dec(v___x_1110_);
lean_inc(v___y_1112_);
v___y_1105_ = v___y_1112_;
v___y_1106_ = v___y_1112_;
goto v___jp_1104_;
}
else
{
v___y_1105_ = v___y_1112_;
v___y_1106_ = v___x_1110_;
goto v___jp_1104_;
}
}
}
else
{
v___y_1071_ = v_irDecls_1102_;
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v_ext_1073_; lean_object* v_toEnvExtension_1074_; lean_object* v_name_1075_; lean_object* v_exportEntriesFn_1076_; lean_object* v_asyncMode_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_private_1082_; lean_object* v___x_1083_; lean_object* v_toEnvExtension_1084_; lean_object* v_name_1085_; lean_object* v_exportEntriesFn_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_private_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1072_ = l_Lean_regularInitAttr;
v_ext_1073_ = lean_ctor_get(v___x_1072_, 1);
v_toEnvExtension_1074_ = lean_ctor_get(v_ext_1073_, 0);
v_name_1075_ = lean_ctor_get(v_ext_1073_, 1);
v_exportEntriesFn_1076_ = lean_ctor_get(v_ext_1073_, 4);
v_asyncMode_1077_ = lean_ctor_get(v_toEnvExtension_1074_, 2);
v___x_1078_ = lean_box(0);
v___x_1079_ = 0;
lean_inc_ref_n(v_env_1062_, 3);
v___x_1080_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1068_, v_ext_1073_, v_env_1062_, v_asyncMode_1077_, v___x_1078_, v___x_1079_);
lean_inc_ref(v_exportEntriesFn_1076_);
v___x_1081_ = lean_apply_2(v_exportEntriesFn_1076_, v_env_1062_, v___x_1080_);
v_private_1082_ = lean_ctor_get(v___x_1081_, 2);
lean_inc(v_private_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1084_ = lean_ctor_get(v___x_1083_, 0);
v_name_1085_ = lean_ctor_get(v___x_1083_, 1);
v_exportEntriesFn_1086_ = lean_ctor_get(v___x_1083_, 4);
v_asyncMode_1087_ = lean_ctor_get(v_toEnvExtension_1084_, 2);
v___x_1088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1069_, v___x_1083_, v_env_1062_, v_asyncMode_1087_, v___x_1078_, v___x_1079_);
lean_inc_ref(v_exportEntriesFn_1086_);
v___x_1089_ = lean_apply_2(v_exportEntriesFn_1086_, v_env_1062_, v___x_1088_);
v_private_1090_ = lean_ctor_get(v___x_1089_, 2);
lean_inc(v_private_1090_);
lean_dec_ref(v___x_1089_);
lean_inc(v_name_1065_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_name_1065_);
lean_ctor_set(v___x_1091_, 1, v___y_1071_);
lean_inc(v_name_1075_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_name_1075_);
lean_ctor_set(v___x_1092_, 1, v_private_1082_);
lean_inc(v_name_1085_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_name_1085_);
lean_ctor_set(v___x_1093_, 1, v_private_1090_);
v___x_1094_ = lean_unsigned_to_nat(3u);
v___x_1095_ = lean_mk_empty_array_with_capacity(v___x_1094_);
v___x_1096_ = lean_array_push(v___x_1095_, v___x_1091_);
v___x_1097_ = lean_array_push(v___x_1096_, v___x_1092_);
v___x_1098_ = lean_array_push(v___x_1097_, v___x_1093_);
return v___x_1098_;
}
v___jp_1104_:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1103_, v_irDecls_1102_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
v___y_1071_ = v___x_1107_;
goto v___jp_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1115_, lean_object* v_k_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_m_1121_; lean_object* v_a_1122_; uint8_t v___x_1123_; 
v___x_1119_ = lean_nat_add(v_x_1117_, v_x_1118_);
v___x_1120_ = lean_unsigned_to_nat(1u);
v_m_1121_ = lean_nat_shiftr(v___x_1119_, v___x_1120_);
lean_dec(v___x_1119_);
v_a_1122_ = lean_array_fget_borrowed(v_as_1115_, v_m_1121_);
v___x_1123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1122_, v_k_1116_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
lean_dec(v_x_1118_);
v___x_1124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1116_, v_a_1122_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v_m_1121_);
lean_dec(v_x_1117_);
lean_inc(v_a_1122_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1122_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_nat_dec_eq(v_m_1121_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_nat_sub(v_m_1121_, v___x_1120_);
lean_dec(v_m_1121_);
v___x_1129_ = lean_nat_dec_lt(v___x_1128_, v_x_1117_);
if (v___x_1129_ == 0)
{
v_x_1118_ = v___x_1128_;
goto _start;
}
else
{
lean_object* v___x_1131_; 
lean_dec(v___x_1128_);
lean_dec(v_x_1117_);
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
}
else
{
lean_object* v___x_1132_; 
lean_dec(v_m_1121_);
lean_dec(v_x_1117_);
v___x_1132_ = lean_box(0);
return v___x_1132_;
}
}
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
lean_dec(v_x_1117_);
v___x_1133_ = lean_nat_add(v_m_1121_, v___x_1120_);
lean_dec(v_m_1121_);
v___x_1134_ = lean_nat_dec_le(v___x_1133_, v_x_1118_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v___x_1133_);
lean_dec(v_x_1118_);
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
v_x_1117_ = v___x_1133_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1137_, lean_object* v_k_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1137_, v_k_1138_, v_x_1139_, v_x_1140_);
lean_dec_ref(v_k_1138_);
lean_dec_ref(v_as_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1142_, lean_object* v_vals_1143_, lean_object* v_i_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = lean_array_get_size(v_keys_1142_);
v___x_1147_ = lean_nat_dec_lt(v_i_1144_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec(v_i_1144_);
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
else
{
lean_object* v_k_x27_1149_; uint8_t v___x_1150_; 
v_k_x27_1149_ = lean_array_fget_borrowed(v_keys_1142_, v_i_1144_);
v___x_1150_ = lean_name_eq(v_k_1145_, v_k_x27_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_i_1144_, v___x_1151_);
lean_dec(v_i_1144_);
v_i_1144_ = v___x_1152_;
goto _start;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_array_fget_borrowed(v_vals_1143_, v_i_1144_);
lean_dec(v_i_1144_);
lean_inc(v___x_1154_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1156_, lean_object* v_vals_1157_, lean_object* v_i_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1156_, v_vals_1157_, v_i_1158_, v_k_1159_);
lean_dec(v_k_1159_);
lean_dec_ref(v_vals_1157_);
lean_dec_ref(v_keys_1156_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1161_, size_t v_x_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1161_) == 0)
{
lean_object* v_es_1164_; lean_object* v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; lean_object* v_j_1168_; lean_object* v___x_1169_; 
v_es_1164_ = lean_ctor_get(v_x_1161_, 0);
v___x_1165_ = lean_box(2);
v___x_1166_ = ((size_t)31ULL);
v___x_1167_ = lean_usize_land(v_x_1162_, v___x_1166_);
v_j_1168_ = lean_usize_to_nat(v___x_1167_);
v___x_1169_ = lean_array_get_borrowed(v___x_1165_, v_es_1164_, v_j_1168_);
lean_dec(v_j_1168_);
switch(lean_obj_tag(v___x_1169_))
{
case 0:
{
lean_object* v_key_1170_; lean_object* v_val_1171_; uint8_t v___x_1172_; 
v_key_1170_ = lean_ctor_get(v___x_1169_, 0);
v_val_1171_ = lean_ctor_get(v___x_1169_, 1);
v___x_1172_ = lean_name_eq(v_x_1163_, v_key_1170_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_inc(v_val_1171_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_val_1171_);
return v___x_1174_;
}
}
case 1:
{
lean_object* v_node_1175_; size_t v___x_1176_; size_t v___x_1177_; 
v_node_1175_ = lean_ctor_get(v___x_1169_, 0);
v___x_1176_ = ((size_t)5ULL);
v___x_1177_ = lean_usize_shift_right(v_x_1162_, v___x_1176_);
v_x_1161_ = v_node_1175_;
v_x_1162_ = v___x_1177_;
goto _start;
}
default: 
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
}
}
else
{
lean_object* v_ks_1180_; lean_object* v_vs_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_ks_1180_ = lean_ctor_get(v_x_1161_, 0);
v_vs_1181_ = lean_ctor_get(v_x_1161_, 1);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1180_, v_vs_1181_, v___x_1182_, v_x_1163_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
size_t v_x_422__boxed_1187_; lean_object* v_res_1188_; 
v_x_422__boxed_1187_ = lean_unbox_usize(v_x_1185_);
lean_dec(v_x_1185_);
v_res_1188_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1184_, v_x_422__boxed_1187_, v_x_1186_);
lean_dec(v_x_1186_);
lean_dec_ref(v_x_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
uint64_t v___y_1192_; 
if (lean_obj_tag(v_x_1190_) == 0)
{
uint64_t v___x_1195_; 
v___x_1195_ = 1723ULL;
v___y_1192_ = v___x_1195_;
goto v___jp_1191_;
}
else
{
uint64_t v_hash_1196_; 
v_hash_1196_ = lean_ctor_get_uint64(v_x_1190_, sizeof(void*)*2);
v___y_1192_ = v_hash_1196_;
goto v___jp_1191_;
}
v___jp_1191_:
{
size_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_uint64_to_usize(v___y_1192_);
v___x_1194_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1189_, v___x_1193_, v_x_1190_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_x_1197_);
return v_res_1199_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1203_, lean_object* v_declName_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1216_; 
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1207_ = l_Lean_IR_declMapExt;
v___x_1216_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1203_, v_declName_1204_);
if (lean_obj_tag(v___x_1216_) == 0)
{
goto v___jp_1208_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_val_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1231_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1206_, v___x_1207_, v_env_1203_, v_val_1217_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_array_get_size(v___x_1231_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v___x_1231_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_sub(v___x_1233_, v___x_1235_);
v___x_1237_ = lean_nat_dec_le(v___x_1232_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1231_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_tmpDecl_1240_; lean_object* v___x_1241_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1239_ = lean_box(0);
lean_inc(v_declName_1204_);
v_tmpDecl_1240_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1240_, 0, v_declName_1204_);
lean_ctor_set(v_tmpDecl_1240_, 1, v___x_1238_);
lean_ctor_set(v_tmpDecl_1240_, 2, v___x_1239_);
lean_ctor_set(v_tmpDecl_1240_, 3, v___x_1205_);
v___x_1241_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1231_, v_tmpDecl_1240_, v___x_1232_, v___x_1236_);
lean_dec_ref_known(v_tmpDecl_1240_, 4);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v___x_1241_) == 0)
{
goto v___jp_1218_;
}
else
{
lean_dec(v_val_1217_);
lean_dec(v_declName_1204_);
lean_dec_ref(v_env_1203_);
return v___x_1241_;
}
}
}
v___jp_1218_:
{
uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1219_ = 0;
v___x_1220_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1206_, v___x_1207_, v_env_1203_, v_val_1217_, v___x_1219_);
lean_dec(v_val_1217_);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_array_get_size(v___x_1220_);
v___x_1223_ = lean_nat_dec_lt(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec_ref(v___x_1220_);
goto v___jp_1208_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_sub(v___x_1222_, v___x_1224_);
v___x_1226_ = lean_nat_dec_le(v___x_1221_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_dec(v___x_1225_);
lean_dec_ref(v___x_1220_);
goto v___jp_1208_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_tmpDecl_1229_; lean_object* v___x_1230_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1228_ = lean_box(0);
lean_inc(v_declName_1204_);
v_tmpDecl_1229_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1229_, 0, v_declName_1204_);
lean_ctor_set(v_tmpDecl_1229_, 1, v___x_1227_);
lean_ctor_set(v_tmpDecl_1229_, 2, v___x_1228_);
lean_ctor_set(v_tmpDecl_1229_, 3, v___x_1205_);
v___x_1230_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1220_, v_tmpDecl_1229_, v___x_1221_, v___x_1225_);
lean_dec_ref_known(v_tmpDecl_1229_, 4);
lean_dec_ref(v___x_1220_);
if (lean_obj_tag(v___x_1230_) == 0)
{
goto v___jp_1208_;
}
else
{
lean_dec(v_declName_1204_);
lean_dec_ref(v_env_1203_);
return v___x_1230_;
}
}
}
}
}
v___jp_1208_:
{
lean_object* v_toEnvExtension_1209_; lean_object* v_asyncMode_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v_snd_1214_; lean_object* v___x_1215_; 
v_toEnvExtension_1209_ = lean_ctor_get(v___x_1207_, 0);
v_asyncMode_1210_ = lean_ctor_get(v_toEnvExtension_1209_, 2);
v___x_1211_ = lean_box(0);
v___x_1212_ = 0;
v___x_1213_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1206_, v___x_1207_, v_env_1203_, v_asyncMode_1210_, v___x_1211_, v___x_1212_);
v_snd_1214_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_snd_1214_);
lean_dec(v___x_1213_);
v___x_1215_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1214_, v_declName_1204_);
lean_dec(v_declName_1204_);
lean_dec(v_snd_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1243_, v_x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1246_, v_x_1247_, v_x_1248_);
lean_dec(v_x_1248_);
lean_dec_ref(v_x_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1250_, lean_object* v_k_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1250_, v_k_1251_, v_x_1252_, v_x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1256_, lean_object* v_k_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1256_, v_k_1257_, v_x_1258_, v_x_1259_, v_x_1260_);
lean_dec_ref(v_k_1257_);
lean_dec_ref(v_as_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1262_, lean_object* v_x_1263_, size_t v_x_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1263_, v_x_1264_, v_x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
size_t v_x_584__boxed_1271_; lean_object* v_res_1272_; 
v_x_584__boxed_1271_ = lean_unbox_usize(v_x_1269_);
lean_dec(v_x_1269_);
v_res_1272_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1267_, v_x_1268_, v_x_584__boxed_1271_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec_ref(v_x_1268_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1273_, lean_object* v_keys_1274_, lean_object* v_vals_1275_, lean_object* v_heq_1276_, lean_object* v_i_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1274_, v_vals_1275_, v_i_1277_, v_k_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_keys_1281_, lean_object* v_vals_1282_, lean_object* v_heq_1283_, lean_object* v_i_1284_, lean_object* v_k_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1280_, v_keys_1281_, v_vals_1282_, v_heq_1283_, v_i_1284_, v_k_1285_);
lean_dec(v_k_1285_);
lean_dec_ref(v_vals_1282_);
lean_dec_ref(v_keys_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1287_, lean_object* v_declName_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1290_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1287_, v_declName_1288_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v___x_1291_; lean_object* v_toEnvExtension_1292_; lean_object* v_asyncMode_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1291_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1292_ = lean_ctor_get(v___x_1291_, 0);
v_asyncMode_1293_ = lean_ctor_get(v_toEnvExtension_1292_, 2);
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1289_, v___x_1291_, v_env_1287_, v_asyncMode_1293_, v___x_1294_);
v___x_1296_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1295_, v_declName_1288_);
lean_dec(v_declName_1288_);
lean_dec(v___x_1295_);
return v___x_1296_;
}
else
{
lean_object* v_val_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___y_1302_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_val_1297_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1300_ = l_Lean_IR_declMapExt;
v___x_1315_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1299_, v___x_1300_, v_env_1287_, v_val_1297_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_array_get_size(v___x_1315_);
v___x_1318_ = lean_nat_dec_lt(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref(v___x_1315_);
v___x_1319_ = lean_box(0);
v___y_1302_ = v___x_1319_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_sub(v___x_1317_, v___x_1320_);
v___x_1322_ = lean_nat_dec_le(v___x_1316_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
lean_dec(v___x_1321_);
lean_dec_ref(v___x_1315_);
v___x_1323_ = lean_box(0);
v___y_1302_ = v___x_1323_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_tmpDecl_1326_; lean_object* v___x_1327_; 
v___x_1324_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1325_ = lean_box(0);
lean_inc(v_declName_1288_);
v_tmpDecl_1326_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1326_, 0, v_declName_1288_);
lean_ctor_set(v_tmpDecl_1326_, 1, v___x_1324_);
lean_ctor_set(v_tmpDecl_1326_, 2, v___x_1325_);
lean_ctor_set(v_tmpDecl_1326_, 3, v___x_1298_);
v___x_1327_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1315_, v_tmpDecl_1326_, v___x_1316_, v___x_1321_);
lean_dec_ref_known(v_tmpDecl_1326_, 4);
lean_dec_ref(v___x_1315_);
if (lean_obj_tag(v___x_1327_) == 0)
{
v___y_1302_ = v___x_1327_;
goto v___jp_1301_;
}
else
{
lean_dec(v_val_1297_);
lean_dec(v_declName_1288_);
lean_dec_ref(v_env_1287_);
return v___x_1327_;
}
}
}
v___jp_1301_:
{
uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1303_ = 0;
v___x_1304_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1299_, v___x_1300_, v_env_1287_, v_val_1297_, v___x_1303_);
lean_dec(v_val_1297_);
lean_dec_ref(v_env_1287_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_size(v___x_1304_);
v___x_1307_ = lean_nat_dec_lt(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v___x_1304_);
lean_dec(v_declName_1288_);
return v___y_1302_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1309_ = lean_nat_sub(v___x_1306_, v___x_1308_);
v___x_1310_ = lean_nat_dec_le(v___x_1305_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1304_);
lean_dec(v_declName_1288_);
return v___y_1302_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_tmpDecl_1313_; lean_object* v___x_1314_; 
lean_dec(v___y_1302_);
v___x_1311_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1312_ = lean_box(0);
v_tmpDecl_1313_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1313_, 0, v_declName_1288_);
lean_ctor_set(v_tmpDecl_1313_, 1, v___x_1311_);
lean_ctor_set(v_tmpDecl_1313_, 2, v___x_1312_);
lean_ctor_set(v_tmpDecl_1313_, 3, v___x_1298_);
v___x_1314_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1304_, v_tmpDecl_1313_, v___x_1305_, v___x_1309_);
lean_dec_ref_known(v_tmpDecl_1313_, 4);
lean_dec_ref(v___x_1304_);
return v___x_1314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1328_, lean_object* v_declName_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v_boxed_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
lean_inc(v_declName_1329_);
v_boxed_1331_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1329_);
v___x_1332_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1328_, v_declName_1329_);
lean_dec(v_declName_1329_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; lean_object* v_toEnvExtension_1334_; lean_object* v_asyncMode_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1333_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1334_ = lean_ctor_get(v___x_1333_, 0);
v_asyncMode_1335_ = lean_ctor_get(v_toEnvExtension_1334_, 2);
v___x_1336_ = lean_box(0);
v___x_1337_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1330_, v___x_1333_, v_env_1328_, v_asyncMode_1335_, v___x_1336_);
v___x_1338_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1337_, v_boxed_1331_);
lean_dec(v_boxed_1331_);
lean_dec(v___x_1337_);
return v___x_1338_;
}
else
{
lean_object* v_val_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___y_1344_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_val_1339_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1342_ = l_Lean_IR_declMapExt;
v___x_1357_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1341_, v___x_1342_, v_env_1328_, v_val_1339_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_array_get_size(v___x_1357_);
v___x_1360_ = lean_nat_dec_lt(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_dec_ref(v___x_1357_);
v___x_1361_ = lean_box(0);
v___y_1344_ = v___x_1361_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_sub(v___x_1359_, v___x_1362_);
v___x_1364_ = lean_nat_dec_le(v___x_1358_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec(v___x_1363_);
lean_dec_ref(v___x_1357_);
v___x_1365_ = lean_box(0);
v___y_1344_ = v___x_1365_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_tmpDecl_1368_; lean_object* v___x_1369_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1367_ = lean_box(0);
lean_inc(v_boxed_1331_);
v_tmpDecl_1368_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1368_, 0, v_boxed_1331_);
lean_ctor_set(v_tmpDecl_1368_, 1, v___x_1366_);
lean_ctor_set(v_tmpDecl_1368_, 2, v___x_1367_);
lean_ctor_set(v_tmpDecl_1368_, 3, v___x_1340_);
v___x_1369_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1357_, v_tmpDecl_1368_, v___x_1358_, v___x_1363_);
lean_dec_ref_known(v_tmpDecl_1368_, 4);
lean_dec_ref(v___x_1357_);
if (lean_obj_tag(v___x_1369_) == 0)
{
v___y_1344_ = v___x_1369_;
goto v___jp_1343_;
}
else
{
lean_dec(v_val_1339_);
lean_dec(v_boxed_1331_);
lean_dec_ref(v_env_1328_);
return v___x_1369_;
}
}
}
v___jp_1343_:
{
uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1345_ = 0;
v___x_1346_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1341_, v___x_1342_, v_env_1328_, v_val_1339_, v___x_1345_);
lean_dec(v_val_1339_);
lean_dec_ref(v_env_1328_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_get_size(v___x_1346_);
v___x_1349_ = lean_nat_dec_lt(v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v___x_1346_);
lean_dec(v_boxed_1331_);
return v___y_1344_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_sub(v___x_1348_, v___x_1350_);
v___x_1352_ = lean_nat_dec_le(v___x_1347_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec(v___x_1351_);
lean_dec_ref(v___x_1346_);
lean_dec(v_boxed_1331_);
return v___y_1344_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_tmpDecl_1355_; lean_object* v___x_1356_; 
lean_dec(v___y_1344_);
v___x_1353_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1354_ = lean_box(0);
v_tmpDecl_1355_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1355_, 0, v_boxed_1331_);
lean_ctor_set(v_tmpDecl_1355_, 1, v___x_1353_);
lean_ctor_set(v_tmpDecl_1355_, 2, v___x_1354_);
lean_ctor_set(v_tmpDecl_1355_, 3, v___x_1340_);
v___x_1356_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1346_, v_tmpDecl_1355_, v___x_1347_, v___x_1351_);
lean_dec_ref_known(v_tmpDecl_1355_, 4);
lean_dec_ref(v___x_1346_);
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1370_, lean_object* v_constName_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1370_, v_constName_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; lean_object* v_toEnvExtension_1374_; lean_object* v_asyncMode_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1373_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1374_ = lean_ctor_get(v___x_1373_, 0);
v_asyncMode_1375_ = lean_ctor_get(v_toEnvExtension_1374_, 2);
v___x_1376_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1377_ = lean_box(0);
v___x_1378_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1376_, v___x_1373_, v_env_1370_, v_asyncMode_1375_, v___x_1377_);
v___x_1379_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1378_, v_constName_1371_);
lean_dec(v_constName_1371_);
lean_dec(v___x_1378_);
if (v___x_1379_ == 0)
{
uint8_t v___x_1380_; 
v___x_1380_ = 1;
return v___x_1380_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
}
else
{
uint8_t v___x_1382_; 
lean_dec_ref_known(v___x_1372_, 1);
lean_dec(v_constName_1371_);
lean_dec_ref(v_env_1370_);
v___x_1382_ = 0;
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1383_, lean_object* v_constName_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = lean_has_compile_error(v_env_1383_, v_constName_1384_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v_env_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1390_ = lean_st_ref_get(v_a_1388_);
v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc_ref(v_env_1391_);
lean_dec(v___x_1390_);
v___x_1392_ = l_Lean_IR_findEnvDecl(v_env_1391_, v_n_1387_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_IR_findDecl___redArg(v_n_1394_, v_a_1395_);
lean_dec(v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_IR_findDecl___redArg(v_n_1398_, v_a_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_IR_findDecl(v_n_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1426_; 
v___x_1411_ = l_Lean_IR_findDecl___redArg(v_n_1408_, v_a_1409_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1426_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1426_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
if (lean_obj_tag(v_a_1412_) == 0)
{
uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1416_ = 0;
v___x_1417_ = lean_box(v___x_1416_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1417_);
v___x_1419_ = v___x_1414_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec_ref_known(v_a_1412_, 1);
v___x_1421_ = 1;
v___x_1422_ = lean_box(v___x_1421_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1422_);
v___x_1424_ = v___x_1414_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_IR_containsDecl___redArg(v_n_1427_, v_a_1428_);
lean_dec(v_a_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_IR_containsDecl___redArg(v_n_1431_, v_a_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_IR_containsDecl(v_n_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_ref_1445_; lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_ref_1445_ = lean_ctor_get(v___y_1442_, 2);
v___x_1446_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1441_, v___y_1442_, v___y_1443_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_inc(v_ref_1445_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_ref_1445_);
lean_ctor_set(v___x_1451_, 1, v_a_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 1);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1485_; 
lean_inc(v_n_1463_);
v___x_1467_ = l_Lean_IR_findDecl___redArg(v_n_1463_, v_a_1465_);
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1485_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1485_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
if (lean_obj_tag(v_a_1468_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1474_; 
lean_dec(v_n_1463_);
v_val_1472_ = lean_ctor_get(v_a_1468_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v_a_1468_, 1);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_val_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_val_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
else
{
lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
v___x_1476_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1477_ = 1;
v___x_1478_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1463_, v___x_1477_);
v___x_1479_ = lean_string_append(v___x_1476_, v___x_1478_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1481_ = lean_string_append(v___x_1479_, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
v___x_1483_ = l_Lean_MessageData_ofFormat(v___x_1482_);
v___x_1484_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1483_, v_a_1464_, v_a_1465_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_IR_getDecl(v_n_1486_, v_a_1487_, v_a_1488_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1492_, v___y_1493_, v___y_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1497_, lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1497_, v_msg_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_env_1508_; lean_object* v___x_1509_; lean_object* v_toEnvExtension_1510_; lean_object* v_asyncMode_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1507_ = lean_st_ref_get(v_a_1504_);
v_env_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc_ref(v_env_1508_);
lean_dec(v___x_1507_);
v___x_1509_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1510_ = lean_ctor_get(v___x_1509_, 0);
v_asyncMode_1511_ = lean_ctor_get(v_toEnvExtension_1510_, 2);
v___x_1512_ = lean_box(0);
v___x_1513_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1506_, v___x_1509_, v_env_1508_, v_asyncMode_1511_, v___x_1512_);
v___x_1514_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1513_, v_n_1503_);
lean_dec(v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_IR_findLocalDecl___redArg(v_n_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec(v_n_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_IR_findLocalDecl___redArg(v_n_1520_, v_a_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_IR_findLocalDecl(v_n_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_n_1525_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v_toEnvExtension_1532_; lean_object* v_asyncMode_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1531_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1532_ = lean_ctor_get(v___x_1531_, 0);
v_asyncMode_1533_ = lean_ctor_get(v_toEnvExtension_1532_, 2);
v___x_1534_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1535_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1534_, v___x_1531_, v_env_1530_, v_asyncMode_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___lam__0(lean_object* v_addEntryFn_1536_, lean_object* v_decl_1537_, lean_object* v_s_1538_){
_start:
{
lean_object* v_importedEntries_1539_; lean_object* v_state_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1548_; 
v_importedEntries_1539_ = lean_ctor_get(v_s_1538_, 0);
v_state_1540_ = lean_ctor_get(v_s_1538_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_s_1538_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1542_ = v_s_1538_;
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_state_1540_);
lean_inc(v_importedEntries_1539_);
lean_dec(v_s_1538_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_state_1544_; lean_object* v___x_1546_; 
v_state_1544_ = lean_apply_2(v_addEntryFn_1536_, v_state_1540_, v_decl_1537_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v_state_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_importedEntries_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_state_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v_env_1557_; lean_object* v_nextMacroScope_1558_; lean_object* v_ngen_1559_; lean_object* v_auxDeclNGen_1560_; lean_object* v_traceState_1561_; lean_object* v_recordedDeps_1562_; lean_object* v_messages_1563_; lean_object* v_infoState_1564_; lean_object* v_snapshotTasks_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1589_; 
v___x_1556_ = lean_st_ref_take(v_a_1554_);
v_env_1557_ = lean_ctor_get(v___x_1556_, 0);
v_nextMacroScope_1558_ = lean_ctor_get(v___x_1556_, 1);
v_ngen_1559_ = lean_ctor_get(v___x_1556_, 2);
v_auxDeclNGen_1560_ = lean_ctor_get(v___x_1556_, 3);
v_traceState_1561_ = lean_ctor_get(v___x_1556_, 4);
v_recordedDeps_1562_ = lean_ctor_get(v___x_1556_, 6);
v_messages_1563_ = lean_ctor_get(v___x_1556_, 7);
v_infoState_1564_ = lean_ctor_get(v___x_1556_, 8);
v_snapshotTasks_1565_ = lean_ctor_get(v___x_1556_, 9);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v___x_1556_, 5);
lean_dec(v_unused_1590_);
v___x_1567_ = v___x_1556_;
v_isShared_1568_ = v_isSharedCheck_1589_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_snapshotTasks_1565_);
lean_inc(v_infoState_1564_);
lean_inc(v_messages_1563_);
lean_inc(v_recordedDeps_1562_);
lean_inc(v_traceState_1561_);
lean_inc(v_auxDeclNGen_1560_);
lean_inc(v_ngen_1559_);
lean_inc(v_nextMacroScope_1558_);
lean_inc(v_env_1557_);
lean_dec(v___x_1556_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1589_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v_toEnvExtension_1570_; lean_object* v_addEntryFn_1571_; lean_object* v_asyncMode_1572_; uint8_t v_logWrites_1573_; lean_object* v___x_1574_; lean_object* v___y_1576_; lean_object* v___f_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1569_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1570_ = lean_ctor_get(v___x_1569_, 0);
v_addEntryFn_1571_ = lean_ctor_get(v___x_1569_, 3);
v_asyncMode_1572_ = lean_ctor_get(v_toEnvExtension_1570_, 2);
v_logWrites_1573_ = lean_ctor_get_uint8(v_toEnvExtension_1570_, sizeof(void*)*6);
v___x_1574_ = lean_box(0);
lean_inc(v_addEntryFn_1571_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_IR_addDecl___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1583_, 0, v_addEntryFn_1571_);
lean_closure_set(v___f_1583_, 1, v_decl_1553_);
v___x_1584_ = lean_box(0);
v___x_1585_ = 1;
if (v_logWrites_1573_ == 0)
{
lean_object* v___x_1586_; 
lean_inc_ref(v_toEnvExtension_1570_);
v___x_1586_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1570_, v_env_1557_, v___f_1583_, v_asyncMode_1572_, v___x_1584_, v___x_1585_);
v___y_1576_ = v___x_1586_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_inc_ref_n(v_toEnvExtension_1570_, 2);
v___x_1587_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1570_, v_env_1557_);
lean_dec_ref(v_env_1557_);
v___x_1588_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1570_, v___x_1587_, v___f_1583_, v_asyncMode_1572_, v___x_1584_, v___x_1585_);
v___y_1576_ = v___x_1588_;
goto v___jp_1575_;
}
v___jp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 5, v___x_1577_);
lean_ctor_set(v___x_1567_, 0, v___y_1576_);
v___x_1579_ = v___x_1567_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___y_1576_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_nextMacroScope_1558_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_ngen_1559_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_auxDeclNGen_1560_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v_traceState_1561_);
lean_ctor_set(v_reuseFailAlloc_1582_, 5, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1582_, 6, v_recordedDeps_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 7, v_messages_1563_);
lean_ctor_set(v_reuseFailAlloc_1582_, 8, v_infoState_1564_);
lean_ctor_set(v_reuseFailAlloc_1582_, 9, v_snapshotTasks_1565_);
v___x_1579_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_st_ref_put(v_a_1554_, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1574_);
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_IR_addDecl___redArg(v_decl_1591_, v_a_1592_);
lean_dec(v_a_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_IR_addDecl___redArg(v_decl_1595_, v_a_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_IR_addDecl(v_decl_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1605_, size_t v_i_1606_, size_t v_stop_1607_, lean_object* v_b_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_usize_dec_eq(v_i_1606_, v_stop_1607_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_array_uget_borrowed(v_as_1605_, v_i_1606_);
lean_inc(v___x_1612_);
v___x_1613_ = l_Lean_IR_addDecl___redArg(v___x_1612_, v___y_1609_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; size_t v___x_1615_; size_t v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1606_, v___x_1615_);
v_i_1606_ = v___x_1616_;
v_b_1608_ = v_a_1614_;
goto _start;
}
else
{
return v___x_1613_;
}
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_b_1608_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1619_, lean_object* v_i_1620_, lean_object* v_stop_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
size_t v_i_boxed_1625_; size_t v_stop_boxed_1626_; lean_object* v_res_1627_; 
v_i_boxed_1625_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_stop_boxed_1626_ = lean_unbox_usize(v_stop_1621_);
lean_dec(v_stop_1621_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1619_, v_i_boxed_1625_, v_stop_boxed_1626_, v_b_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v_as_1619_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_array_get_size(v_decls_1628_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_nat_dec_lt(v___x_1632_, v___x_1633_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
return v___x_1636_;
}
else
{
size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = lean_usize_of_nat(v___x_1633_);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1628_, v___x_1637_, v___x_1638_, v___x_1634_, v_a_1630_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_IR_addDecls(v_decls_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec_ref(v_decls_1640_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1645_, size_t v_i_1646_, size_t v_stop_1647_, lean_object* v_b_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1645_, v_i_1646_, v_stop_1647_, v_b_1648_, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1653_, lean_object* v_i_1654_, lean_object* v_stop_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
size_t v_i_boxed_1660_; size_t v_stop_boxed_1661_; lean_object* v_res_1662_; 
v_i_boxed_1660_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_stop_boxed_1661_ = lean_unbox_usize(v_stop_1655_);
lean_dec(v_stop_1655_);
v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1653_, v_i_boxed_1660_, v_stop_boxed_1661_, v_b_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_as_1653_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1666_, lean_object* v_as_1667_, size_t v_sz_1668_, size_t v_i_1669_, lean_object* v_b_1670_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_usize_dec_lt(v_i_1669_, v_sz_1668_);
if (v___x_1671_ == 0)
{
lean_inc_ref(v_b_1670_);
return v_b_1670_;
}
else
{
lean_object* v___x_1672_; lean_object* v_a_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1672_ = lean_box(0);
v_a_1673_ = lean_array_uget_borrowed(v_as_1667_, v_i_1669_);
v___x_1674_ = l_Lean_IR_Decl_name(v_a_1673_);
v___x_1675_ = lean_name_eq(v___x_1674_, v_n_1666_);
lean_dec(v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; 
v___x_1676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1669_, v___x_1677_);
v_i_1669_ = v___x_1678_;
v_b_1670_ = v___x_1676_;
goto _start;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_inc(v_a_1673_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1673_);
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
lean_ctor_set(v___x_1682_, 1, v___x_1672_);
return v___x_1682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1683_, lean_object* v_as_1684_, lean_object* v_sz_1685_, lean_object* v_i_1686_, lean_object* v_b_1687_){
_start:
{
size_t v_sz_boxed_1688_; size_t v_i_boxed_1689_; lean_object* v_res_1690_; 
v_sz_boxed_1688_ = lean_unbox_usize(v_sz_1685_);
lean_dec(v_sz_1685_);
v_i_boxed_1689_ = lean_unbox_usize(v_i_1686_);
lean_dec(v_i_1686_);
v_res_1690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1683_, v_as_1684_, v_sz_boxed_1688_, v_i_boxed_1689_, v_b_1687_);
lean_dec_ref(v_b_1687_);
lean_dec_ref(v_as_1684_);
lean_dec(v_n_1683_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1691_, lean_object* v_n_1692_, lean_object* v_decls_1693_){
_start:
{
lean_object* v___x_1694_; size_t v_sz_1695_; size_t v___x_1696_; lean_object* v___x_1697_; lean_object* v_fst_1698_; 
v___x_1694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1695_ = lean_array_size(v_decls_1693_);
v___x_1696_ = ((size_t)0ULL);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1692_, v_decls_1693_, v_sz_1695_, v___x_1696_, v___x_1694_);
v_fst_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_fst_1698_);
lean_dec_ref(v___x_1697_);
if (lean_obj_tag(v_fst_1698_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_IR_findEnvDecl(v_env_1691_, v_n_1692_);
return v___x_1699_;
}
else
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v_fst_1698_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v_fst_1698_, 1);
if (lean_obj_tag(v_val_1700_) == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_IR_findEnvDecl(v_env_1691_, v_n_1692_);
return v___x_1701_;
}
else
{
lean_dec(v_n_1692_);
lean_dec_ref(v_env_1691_);
return v_val_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1702_, lean_object* v_n_1703_, lean_object* v_decls_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_IR_findEnvDecl_x27(v_env_1702_, v_n_1703_, v_decls_1704_);
lean_dec_ref(v_decls_1704_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1706_, lean_object* v_decls_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; lean_object* v_env_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = lean_st_ref_get(v_a_1708_);
v_env_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref(v_env_1711_);
lean_dec(v___x_1710_);
v___x_1712_ = l_Lean_IR_findEnvDecl_x27(v_env_1711_, v_n_1706_, v_decls_1707_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1714_, lean_object* v_decls_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_IR_findDecl_x27___redArg(v_n_1714_, v_decls_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_decls_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1719_, lean_object* v_decls_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_IR_findDecl_x27___redArg(v_n_1719_, v_decls_1720_, v_a_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1725_, lean_object* v_decls_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_IR_findDecl_x27(v_n_1725_, v_decls_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec_ref(v_decls_1726_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1731_, lean_object* v_as_1732_, size_t v_i_1733_, size_t v_stop_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_eq(v_i_1733_, v_stop_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_array_uget_borrowed(v_as_1732_, v_i_1733_);
v___x_1737_ = l_Lean_IR_Decl_name(v___x_1736_);
v___x_1738_ = lean_name_eq(v___x_1737_, v_n_1731_);
lean_dec(v___x_1737_);
if (v___x_1738_ == 0)
{
size_t v___x_1739_; size_t v___x_1740_; 
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1733_, v___x_1739_);
v_i_1733_ = v___x_1740_;
goto _start;
}
else
{
return v___x_1738_;
}
}
else
{
uint8_t v___x_1742_; 
v___x_1742_ = 0;
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1743_, lean_object* v_as_1744_, lean_object* v_i_1745_, lean_object* v_stop_1746_){
_start:
{
size_t v_i_boxed_1747_; size_t v_stop_boxed_1748_; uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_i_boxed_1747_ = lean_unbox_usize(v_i_1745_);
lean_dec(v_i_1745_);
v_stop_boxed_1748_ = lean_unbox_usize(v_stop_1746_);
lean_dec(v_stop_1746_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1743_, v_as_1744_, v_i_boxed_1747_, v_stop_boxed_1748_);
lean_dec_ref(v_as_1744_);
lean_dec(v_n_1743_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1751_, lean_object* v_decls_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = lean_array_get_size(v_decls_1752_);
v___x_1757_ = lean_nat_dec_lt(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_IR_containsDecl___redArg(v_n_1751_, v_a_1753_);
return v___x_1758_;
}
else
{
if (v___x_1757_ == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_IR_containsDecl___redArg(v_n_1751_, v_a_1753_);
return v___x_1759_;
}
else
{
size_t v___x_1760_; size_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = lean_usize_of_nat(v___x_1756_);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1751_, v_decls_1752_, v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_IR_containsDecl___redArg(v_n_1751_, v_a_1753_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v_n_1751_);
v___x_1764_ = lean_box(v___x_1757_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1766_, lean_object* v_decls_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1766_, v_decls_1767_, v_a_1768_);
lean_dec(v_a_1768_);
lean_dec_ref(v_decls_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1771_, lean_object* v_decls_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1771_, v_decls_1772_, v_a_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1777_, lean_object* v_decls_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_IR_containsDecl_x27(v_n_1777_, v_decls_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec_ref(v_decls_1778_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1783_, lean_object* v_decls_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1806_; 
lean_inc(v_n_1783_);
v___x_1788_ = l_Lean_IR_findDecl_x27___redArg(v_n_1783_, v_decls_1784_, v_a_1786_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1806_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1806_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
if (lean_obj_tag(v_a_1789_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1795_; 
lean_dec(v_n_1783_);
v_val_1793_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v_a_1789_, 1);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_val_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_val_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_del_object(v___x_1791_);
lean_dec(v_a_1789_);
v___x_1797_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1798_ = 1;
v___x_1799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1783_, v___x_1798_);
v___x_1800_ = lean_string_append(v___x_1797_, v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
v___x_1804_ = l_Lean_MessageData_ofFormat(v___x_1803_);
v___x_1805_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1804_, v_a_1785_, v_a_1786_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1807_, lean_object* v_decls_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_IR_getDecl_x27(v_n_1807_, v_decls_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec_ref(v_decls_1808_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1813_, lean_object* v_declName_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_IR_findEnvDecl(v_env_1813_, v_declName_1814_);
if (lean_obj_tag(v___x_1815_) == 1)
{
lean_object* v_val_1816_; 
v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref_known(v___x_1815_, 1);
if (lean_obj_tag(v_val_1816_) == 0)
{
lean_object* v_info_1817_; lean_object* v_sorryDep_x3f_1818_; 
v_info_1817_ = lean_ctor_get(v_val_1816_, 4);
lean_inc_ref(v_info_1817_);
lean_dec_ref_known(v_val_1816_, 5);
v_sorryDep_x3f_1818_ = lean_ctor_get(v_info_1817_, 0);
lean_inc(v_sorryDep_x3f_1818_);
lean_dec_ref(v_info_1817_);
return v_sorryDep_x3f_1818_;
}
else
{
lean_object* v___x_1819_; 
lean_dec(v_val_1816_);
v___x_1819_ = lean_box(0);
return v___x_1819_;
}
}
else
{
lean_object* v___x_1820_; 
lean_dec(v___x_1815_);
v___x_1820_ = lean_box(0);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(uint8_t v_level_1821_, lean_object* v_env_1822_, uint8_t v_includeDecls_1823_, lean_object* v_as_1824_, size_t v_i_1825_, size_t v_stop_1826_, lean_object* v_b_1827_){
_start:
{
lean_object* v___y_1829_; uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_eq(v_i_1825_, v_stop_1826_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_array_uget_borrowed(v_as_1824_, v_i_1825_);
if (v_includeDecls_1823_ == 0)
{
uint8_t v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = 1;
lean_inc(v___x_1834_);
lean_inc_ref(v_env_1822_);
v___x_1846_ = l_Lean_Environment_contains(v_env_1822_, v___x_1834_, v___x_1845_);
if (v___x_1846_ == 0)
{
goto v___jp_1835_;
}
else
{
v___y_1829_ = v_b_1827_;
goto v___jp_1828_;
}
}
else
{
goto v___jp_1835_;
}
v___jp_1835_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1836_ = lean_box(v_level_1821_);
v___x_1837_ = lean_obj_tag_nat(v___x_1836_);
lean_dec(v___x_1836_);
v___x_1838_ = lean_unsigned_to_nat(2u);
v___x_1839_ = lean_nat_dec_eq(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
uint8_t v___x_1840_; 
lean_inc_ref(v_env_1822_);
v___x_1840_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1822_, v___x_1834_);
if (v___x_1840_ == 0)
{
uint8_t v___x_1841_; 
lean_inc_ref(v_env_1822_);
v___x_1841_ = l_Lean_isDeclMeta(v_env_1822_, v___x_1834_);
if (v___x_1841_ == 0)
{
v___y_1829_ = v_b_1827_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1842_; 
lean_inc(v___x_1834_);
v___x_1842_ = lean_array_push(v_b_1827_, v___x_1834_);
v___y_1829_ = v___x_1842_;
goto v___jp_1828_;
}
}
else
{
lean_object* v___x_1843_; 
lean_inc(v___x_1834_);
v___x_1843_ = lean_array_push(v_b_1827_, v___x_1834_);
v___y_1829_ = v___x_1843_;
goto v___jp_1828_;
}
}
else
{
lean_object* v___x_1844_; 
lean_inc(v___x_1834_);
v___x_1844_ = lean_array_push(v_b_1827_, v___x_1834_);
v___y_1829_ = v___x_1844_;
goto v___jp_1828_;
}
}
}
else
{
lean_dec_ref(v_env_1822_);
return v_b_1827_;
}
v___jp_1828_:
{
size_t v___x_1830_; size_t v___x_1831_; 
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_i_1825_, v___x_1830_);
v_i_1825_ = v___x_1831_;
v_b_1827_ = v___y_1829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_level_1847_, lean_object* v_env_1848_, lean_object* v_includeDecls_1849_, lean_object* v_as_1850_, lean_object* v_i_1851_, lean_object* v_stop_1852_, lean_object* v_b_1853_){
_start:
{
uint8_t v_level_boxed_1854_; uint8_t v_includeDecls_boxed_1855_; size_t v_i_boxed_1856_; size_t v_stop_boxed_1857_; lean_object* v_res_1858_; 
v_level_boxed_1854_ = lean_unbox(v_level_1847_);
v_includeDecls_boxed_1855_ = lean_unbox(v_includeDecls_1849_);
v_i_boxed_1856_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_stop_boxed_1857_ = lean_unbox_usize(v_stop_1852_);
lean_dec(v_stop_1852_);
v_res_1858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_boxed_1854_, v_env_1848_, v_includeDecls_boxed_1855_, v_as_1850_, v_i_boxed_1856_, v_stop_boxed_1857_, v_b_1853_);
lean_dec_ref(v_as_1850_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1859_, size_t v_i_1860_, lean_object* v_bs_1861_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_usize_dec_lt(v_i_1860_, v_sz_1859_);
if (v___x_1862_ == 0)
{
return v_bs_1861_;
}
else
{
lean_object* v_v_1863_; lean_object* v___x_1864_; lean_object* v_bs_x27_1865_; lean_object* v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v_v_1863_ = lean_array_uget(v_bs_1861_, v_i_1860_);
v___x_1864_ = lean_unsigned_to_nat(0u);
v_bs_x27_1865_ = lean_array_uset(v_bs_1861_, v_i_1860_, v___x_1864_);
v___x_1866_ = l_Lean_IR_Decl_name(v_v_1863_);
lean_dec(v_v_1863_);
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_add(v_i_1860_, v___x_1867_);
v___x_1869_ = lean_array_uset(v_bs_x27_1865_, v_i_1860_, v___x_1866_);
v_i_1860_ = v___x_1868_;
v_bs_1861_ = v___x_1869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1871_, lean_object* v_i_1872_, lean_object* v_bs_1873_){
_start:
{
size_t v_sz_boxed_1874_; size_t v_i_boxed_1875_; lean_object* v_res_1876_; 
v_sz_boxed_1874_ = lean_unbox_usize(v_sz_1871_);
lean_dec(v_sz_1871_);
v_i_boxed_1875_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1874_, v_i_boxed_1875_, v_bs_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1879_, uint8_t v_level_1880_, uint8_t v_includeDecls_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v_toEnvExtension_1883_; lean_object* v_asyncMode_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v_env_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; size_t v_sz_1893_; size_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1882_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1883_ = lean_ctor_get(v___x_1882_, 0);
v_asyncMode_1884_ = lean_ctor_get(v_toEnvExtension_1883_, 2);
v___x_1885_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1886_ = lean_box(v_level_1880_);
v___x_1887_ = lean_obj_tag_nat(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_nat_dec_eq(v___x_1887_, v___x_1888_);
v_env_1890_ = l_Lean_Environment_setExporting(v_env_1879_, v___x_1889_);
lean_inc_ref(v_env_1890_);
v___x_1891_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1885_, v___x_1882_, v_env_1890_, v_asyncMode_1884_);
v___x_1892_ = lean_array_mk(v___x_1891_);
v_sz_1893_ = lean_array_size(v___x_1892_);
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1893_, v___x_1894_, v___x_1892_);
v___x_1896_ = lean_array_get_size(v___x_1895_);
v___x_1897_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1898_ = lean_nat_dec_lt(v___x_1888_, v___x_1896_);
if (v___x_1898_ == 0)
{
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_env_1890_);
return v___x_1897_;
}
else
{
size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_usize_of_nat(v___x_1896_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1880_, v_env_1890_, v_includeDecls_1881_, v___x_1895_, v___x_1894_, v___x_1899_, v___x_1897_);
lean_dec_ref(v___x_1895_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1901_, lean_object* v_level_1902_, lean_object* v_includeDecls_1903_){
_start:
{
uint8_t v_level_boxed_1904_; uint8_t v_includeDecls_boxed_1905_; lean_object* v_res_1906_; 
v_level_boxed_1904_ = lean_unbox(v_level_1902_);
v_includeDecls_boxed_1905_ = lean_unbox(v_includeDecls_1903_);
v_res_1906_ = lean_get_ir_extra_const_names(v_env_1901_, v_level_boxed_1904_, v_includeDecls_boxed_1905_);
return v_res_1906_;
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
