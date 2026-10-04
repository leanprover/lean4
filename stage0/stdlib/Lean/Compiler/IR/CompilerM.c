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
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_155_);
lean_ctor_set(v___x_157_, 5, v___x_155_);
lean_ctor_set(v___x_157_, 6, v___x_155_);
lean_ctor_set(v___x_157_, 7, v___x_155_);
lean_ctor_set(v___x_157_, 8, v___x_155_);
lean_ctor_set(v___x_157_, 9, v___x_155_);
lean_ctor_set(v___x_157_, 10, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v_toCold_176_; lean_object* v_env_177_; lean_object* v_options_178_; uint8_t v___x_179_; lean_object* v_env_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_toCold_176_ = lean_ctor_get(v___y_172_, 0);
v_env_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_175_);
v_options_178_ = lean_ctor_get(v_toCold_176_, 2);
v___x_179_ = 0;
v_env_180_ = l_Lean_Environment_setRecordingDeps(v_env_177_, v___x_179_);
v___x_181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
v___x_182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_178_);
v___x_183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_183_, 0, v_env_180_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_182_);
lean_ctor_set(v___x_183_, 3, v_options_178_);
v___x_184_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_msgData_171_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msgData_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_190_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0(void){
_start:
{
lean_object* v___x_191_; double v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_float_of_nat(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object* v_cls_196_, lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_ref_201_; lean_object* v___x_202_; lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_248_; 
v_ref_201_ = lean_ctor_get(v___y_198_, 2);
v___x_202_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_197_, v___y_198_, v___y_199_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_248_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_248_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_248_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v_traceState_208_; lean_object* v_env_209_; lean_object* v_nextMacroScope_210_; lean_object* v_ngen_211_; lean_object* v_auxDeclNGen_212_; lean_object* v_cache_213_; lean_object* v_recordedDeps_214_; lean_object* v_messages_215_; lean_object* v_infoState_216_; lean_object* v_snapshotTasks_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_247_; 
v___x_207_ = lean_st_ref_take(v___y_199_);
v_traceState_208_ = lean_ctor_get(v___x_207_, 4);
v_env_209_ = lean_ctor_get(v___x_207_, 0);
v_nextMacroScope_210_ = lean_ctor_get(v___x_207_, 1);
v_ngen_211_ = lean_ctor_get(v___x_207_, 2);
v_auxDeclNGen_212_ = lean_ctor_get(v___x_207_, 3);
v_cache_213_ = lean_ctor_get(v___x_207_, 5);
v_recordedDeps_214_ = lean_ctor_get(v___x_207_, 6);
v_messages_215_ = lean_ctor_get(v___x_207_, 7);
v_infoState_216_ = lean_ctor_get(v___x_207_, 8);
v_snapshotTasks_217_ = lean_ctor_get(v___x_207_, 9);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_247_ == 0)
{
v___x_219_ = v___x_207_;
v_isShared_220_ = v_isSharedCheck_247_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_snapshotTasks_217_);
lean_inc(v_infoState_216_);
lean_inc(v_messages_215_);
lean_inc(v_recordedDeps_214_);
lean_inc(v_cache_213_);
lean_inc(v_traceState_208_);
lean_inc(v_auxDeclNGen_212_);
lean_inc(v_ngen_211_);
lean_inc(v_nextMacroScope_210_);
lean_inc(v_env_209_);
lean_dec(v___x_207_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_247_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint64_t v_tid_221_; lean_object* v_traces_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_246_; 
v_tid_221_ = lean_ctor_get_uint64(v_traceState_208_, sizeof(void*)*1);
v_traces_222_ = lean_ctor_get(v_traceState_208_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_traceState_208_);
if (v_isSharedCheck_246_ == 0)
{
v___x_224_ = v_traceState_208_;
v_isShared_225_ = v_isSharedCheck_246_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_traces_222_);
lean_dec(v_traceState_208_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_246_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; double v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_226_ = lean_box(0);
v___x_227_ = lean_box(0);
v___x_228_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_229_ = 0;
v___x_230_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_231_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_231_, 0, v_cls_196_);
lean_ctor_set(v___x_231_, 1, v___x_227_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_ctor_set_float(v___x_231_, sizeof(void*)*3, v___x_228_);
lean_ctor_set_float(v___x_231_, sizeof(void*)*3 + 8, v___x_228_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*3 + 16, v___x_229_);
v___x_232_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_233_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v_a_203_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
lean_inc(v_ref_201_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_ref_201_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = l_Lean_PersistentArray_push___redArg(v_traces_222_, v___x_234_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_235_);
v___x_237_ = v___x_224_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_235_);
lean_ctor_set_uint64(v_reuseFailAlloc_245_, sizeof(void*)*1, v_tid_221_);
v___x_237_ = v_reuseFailAlloc_245_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 4, v___x_237_);
v___x_239_ = v___x_219_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_env_209_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_nextMacroScope_210_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_ngen_211_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_auxDeclNGen_212_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_244_, 5, v_cache_213_);
lean_ctor_set(v_reuseFailAlloc_244_, 6, v_recordedDeps_214_);
lean_ctor_set(v_reuseFailAlloc_244_, 7, v_messages_215_);
lean_ctor_set(v_reuseFailAlloc_244_, 8, v_infoState_216_);
lean_ctor_set(v_reuseFailAlloc_244_, 9, v_snapshotTasks_217_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_st_ref_put(v___y_199_, v___x_239_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_226_);
v___x_242_ = v___x_205_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_226_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_249_, v_msg_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_265_ = l_Lean_IR_LogEntry_fmt(v_entry_260_);
v___x_266_ = l_Lean_MessageData_ofFormat(v___x_265_);
v___x_267_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_264_, v___x_266_, v_a_261_, v_a_262_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_IR_log(v_entry_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_281_, lean_object* v_optName_282_){
_start:
{
lean_object* v_map_283_; lean_object* v___x_290_; 
v_map_283_ = lean_ctor_get(v_opts_281_, 0);
v___x_290_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_283_, v_optName_282_);
if (lean_obj_tag(v___x_290_) == 1)
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_290_, 1);
if (lean_obj_tag(v_val_291_) == 1)
{
uint8_t v_v_292_; 
v_v_292_ = lean_ctor_get_uint8(v_val_291_, 0);
lean_dec_ref_known(v_val_291_, 0);
return v_v_292_;
}
else
{
lean_dec(v_val_291_);
goto v___jp_284_;
}
}
else
{
lean_dec(v___x_290_);
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_286_ = 0;
v___x_287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_283_, v___x_285_);
if (lean_obj_tag(v___x_287_) == 0)
{
return v___x_286_;
}
else
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
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_293_, lean_object* v_optName_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_293_, v_optName_294_);
lean_dec(v_optName_294_);
lean_dec_ref(v_opts_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_297_, lean_object* v_cls_298_, lean_object* v_decls_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_300_);
v___x_304_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_303_, v_optName_297_);
lean_dec_ref(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref(v_decls_299_);
lean_dec(v_cls_298_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_cls_298_);
lean_ctor_set(v___x_307_, 1, v_decls_299_);
v___x_308_ = l_Lean_IR_log(v___x_307_, v_a_300_, v_a_301_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_309_, lean_object* v_cls_310_, lean_object* v_decls_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_309_, v_cls_310_, v_decls_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_optName_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_316_, lean_object* v_decl_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_316_);
v___x_322_ = l_Lean_Name_append(v___x_321_, v_cls_316_);
v___x_323_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_322_, v_cls_316_, v_decl_317_, v_a_318_, v_a_319_);
lean_dec(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_324_, lean_object* v_decl_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_IR_logDecls(v_cls_324_, v_decl_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_330_, lean_object* v_optName_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_333_);
v___x_337_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v___x_336_, v_optName_331_);
lean_dec_ref(v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_a_332_);
lean_dec_ref(v_inst_330_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_apply_1(v_inst_330_, v_a_332_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = l_Lean_IR_log(v___x_341_, v_a_333_, v_a_334_);
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
lean_inc(v_type_578_);
lean_inc(v_f_576_);
v___y_566_ = v_f_576_;
v___y_567_ = v_type_578_;
v___y_568_ = v_xs_577_;
goto v___jp_565_;
}
}
else
{
lean_dec(v___x_579_);
lean_inc_ref(v_xs_577_);
lean_inc(v_type_578_);
lean_inc(v_f_576_);
v___y_566_ = v_f_576_;
v___y_567_ = v_type_578_;
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
lean_ctor_set(v___x_570_, 0, v___y_566_);
lean_ctor_set(v___x_570_, 1, v___y_568_);
lean_ctor_set(v___x_570_, 2, v___y_567_);
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
size_t v_x_2165__boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_x_2165__boxed_703_ = lean_unbox_usize(v_x_701_);
lean_dec(v_x_701_);
v_res_704_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_700_, v_x_2165__boxed_703_, v_x_702_);
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
size_t v_x_2326__boxed_876_; size_t v_x_2327__boxed_877_; lean_object* v_res_878_; 
v_x_2326__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_2327__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_871_, v_x_2326__boxed_876_, v_x_2327__boxed_877_, v_x_874_, v_x_875_);
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
size_t v_x_2611__boxed_988_; uint8_t v_res_989_; lean_object* v_r_990_; 
v_x_2611__boxed_988_ = lean_unbox_usize(v_x_986_);
lean_dec(v_x_986_);
v_res_989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_984_, v_x_985_, v_x_2611__boxed_988_, v_x_987_);
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
size_t v_x_2622__boxed_1004_; size_t v_x_2623__boxed_1005_; lean_object* v_res_1006_; 
v_x_2622__boxed_1004_ = lean_unbox_usize(v_x_1000_);
lean_dec(v_x_1000_);
v_x_2623__boxed_1005_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_res_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_998_, v_x_999_, v_x_2622__boxed_1004_, v_x_2623__boxed_1005_, v_x_1002_, v_x_1003_);
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
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___y_1058_; uint8_t v___x_1062_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_sub(v___x_1051_, v___x_1055_);
v___x_1062_ = lean_nat_dec_le(v___x_1052_, v___x_1056_);
if (v___x_1062_ == 0)
{
lean_inc(v___x_1056_);
v___y_1058_ = v___x_1056_;
goto v___jp_1057_;
}
else
{
v___y_1058_ = v___x_1052_;
goto v___jp_1057_;
}
v___jp_1057_:
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_le(v___y_1058_, v___x_1056_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v___x_1056_);
lean_inc(v___y_1058_);
v___x_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1054_, v___x_1051_, v_irDecls_1050_, v___y_1058_, v___y_1058_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1058_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_1054_, v___x_1051_, v_irDecls_1050_, v___y_1058_, v___x_1056_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_1056_);
return v___x_1061_;
}
}
}
else
{
return v_irDecls_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_1063_){
_start:
{
lean_inc_ref(v_initDecls_1063_);
return v_initDecls_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_1064_);
lean_dec_ref(v_initDecls_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1066_){
_start:
{
lean_inc_ref(v_modPkg_1066_);
return v_modPkg_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1067_);
lean_dec_ref(v_modPkg_1067_);
return v_res_1068_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0(void){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v_toEnvExtension_1075_; lean_object* v_name_1076_; lean_object* v_asyncMode_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___y_1082_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_irDecls_1113_; lean_object* v___x_1114_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v___x_1119_; 
v___x_1074_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1075_ = lean_ctor_get(v___x_1074_, 0);
v_name_1076_ = lean_ctor_get(v___x_1074_, 1);
v_asyncMode_1077_ = lean_ctor_get(v_toEnvExtension_1075_, 2);
v___x_1078_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1079_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1080_ = lean_box(0);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0));
lean_inc_ref(v_env_1073_);
v___x_1112_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1078_, v___x_1074_, v_env_1073_, v_asyncMode_1077_);
v_irDecls_1113_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_array_get_size(v_irDecls_1113_);
v___x_1119_ = lean_nat_dec_eq(v___x_1114_, v___x_1110_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; uint8_t v___x_1125_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_sub(v___x_1114_, v___x_1120_);
v___x_1125_ = lean_nat_dec_le(v___x_1110_, v___x_1121_);
if (v___x_1125_ == 0)
{
lean_inc(v___x_1121_);
v___y_1123_ = v___x_1121_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___x_1110_;
goto v___jp_1122_;
}
v___jp_1122_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_nat_dec_le(v___y_1123_, v___x_1121_);
if (v___x_1124_ == 0)
{
lean_dec(v___x_1121_);
lean_inc(v___y_1123_);
v___y_1116_ = v___y_1123_;
v___y_1117_ = v___y_1123_;
goto v___jp_1115_;
}
else
{
v___y_1116_ = v___y_1123_;
v___y_1117_ = v___x_1121_;
goto v___jp_1115_;
}
}
}
else
{
v___y_1082_ = v_irDecls_1113_;
goto v___jp_1081_;
}
v___jp_1081_:
{
lean_object* v___x_1083_; lean_object* v_ext_1084_; lean_object* v_toEnvExtension_1085_; lean_object* v_name_1086_; lean_object* v_exportEntriesFn_1087_; lean_object* v_asyncMode_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_private_1093_; lean_object* v___x_1094_; lean_object* v_toEnvExtension_1095_; lean_object* v_name_1096_; lean_object* v_exportEntriesFn_1097_; lean_object* v_asyncMode_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_private_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1083_ = l_Lean_regularInitAttr;
v_ext_1084_ = lean_ctor_get(v___x_1083_, 1);
v_toEnvExtension_1085_ = lean_ctor_get(v_ext_1084_, 0);
v_name_1086_ = lean_ctor_get(v_ext_1084_, 1);
v_exportEntriesFn_1087_ = lean_ctor_get(v_ext_1084_, 4);
v_asyncMode_1088_ = lean_ctor_get(v_toEnvExtension_1085_, 2);
v___x_1089_ = lean_box(0);
v___x_1090_ = 0;
lean_inc_ref_n(v_env_1073_, 3);
v___x_1091_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1079_, v_ext_1084_, v_env_1073_, v_asyncMode_1088_, v___x_1089_, v___x_1090_);
lean_inc_ref(v_exportEntriesFn_1087_);
v___x_1092_ = lean_apply_2(v_exportEntriesFn_1087_, v_env_1073_, v___x_1091_);
v_private_1093_ = lean_ctor_get(v___x_1092_, 2);
lean_inc(v_private_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1095_ = lean_ctor_get(v___x_1094_, 0);
v_name_1096_ = lean_ctor_get(v___x_1094_, 1);
v_exportEntriesFn_1097_ = lean_ctor_get(v___x_1094_, 4);
v_asyncMode_1098_ = lean_ctor_get(v_toEnvExtension_1095_, 2);
v___x_1099_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1080_, v___x_1094_, v_env_1073_, v_asyncMode_1098_, v___x_1089_, v___x_1090_);
lean_inc_ref(v_exportEntriesFn_1097_);
v___x_1100_ = lean_apply_2(v_exportEntriesFn_1097_, v_env_1073_, v___x_1099_);
v_private_1101_ = lean_ctor_get(v___x_1100_, 2);
lean_inc(v_private_1101_);
lean_dec_ref(v___x_1100_);
lean_inc(v_name_1076_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_name_1076_);
lean_ctor_set(v___x_1102_, 1, v___y_1082_);
lean_inc(v_name_1086_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_name_1086_);
lean_ctor_set(v___x_1103_, 1, v_private_1093_);
lean_inc(v_name_1096_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_name_1096_);
lean_ctor_set(v___x_1104_, 1, v_private_1101_);
v___x_1105_ = lean_unsigned_to_nat(3u);
v___x_1106_ = lean_mk_empty_array_with_capacity(v___x_1105_);
v___x_1107_ = lean_array_push(v___x_1106_, v___x_1102_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1103_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1104_);
return v___x_1109_;
}
v___jp_1115_:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_1114_, v_irDecls_1113_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
v___y_1082_ = v___x_1118_;
goto v___jp_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1126_, lean_object* v_k_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_m_1132_; lean_object* v_a_1133_; uint8_t v___x_1134_; 
v___x_1130_ = lean_nat_add(v_x_1128_, v_x_1129_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v_m_1132_ = lean_nat_shiftr(v___x_1130_, v___x_1131_);
lean_dec(v___x_1130_);
v_a_1133_ = lean_array_fget_borrowed(v_as_1126_, v_m_1132_);
v___x_1134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1133_, v_k_1127_);
if (v___x_1134_ == 0)
{
uint8_t v___x_1135_; 
lean_dec(v_x_1129_);
v___x_1135_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1127_, v_a_1133_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec(v_m_1132_);
lean_dec(v_x_1128_);
lean_inc(v_a_1133_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_a_1133_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_nat_dec_eq(v_m_1132_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_nat_sub(v_m_1132_, v___x_1131_);
lean_dec(v_m_1132_);
v___x_1140_ = lean_nat_dec_lt(v___x_1139_, v_x_1128_);
if (v___x_1140_ == 0)
{
v_x_1129_ = v___x_1139_;
goto _start;
}
else
{
lean_object* v___x_1142_; 
lean_dec(v___x_1139_);
lean_dec(v_x_1128_);
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_m_1132_);
lean_dec(v_x_1128_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
}
}
else
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
lean_dec(v_x_1128_);
v___x_1144_ = lean_nat_add(v_m_1132_, v___x_1131_);
lean_dec(v_m_1132_);
v___x_1145_ = lean_nat_dec_le(v___x_1144_, v_x_1129_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec(v___x_1144_);
lean_dec(v_x_1129_);
v___x_1146_ = lean_box(0);
return v___x_1146_;
}
else
{
v_x_1128_ = v___x_1144_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1148_, lean_object* v_k_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1148_, v_k_1149_, v_x_1150_, v_x_1151_);
lean_dec_ref(v_k_1149_);
lean_dec_ref(v_as_1148_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1153_, lean_object* v_vals_1154_, lean_object* v_i_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_array_get_size(v_keys_1153_);
v___x_1158_ = lean_nat_dec_lt(v_i_1155_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_i_1155_);
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
else
{
lean_object* v_k_x27_1160_; uint8_t v___x_1161_; 
v_k_x27_1160_ = lean_array_fget_borrowed(v_keys_1153_, v_i_1155_);
v___x_1161_ = lean_name_eq(v_k_1156_, v_k_x27_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_i_1155_, v___x_1162_);
lean_dec(v_i_1155_);
v_i_1155_ = v___x_1163_;
goto _start;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_array_fget_borrowed(v_vals_1154_, v_i_1155_);
lean_dec(v_i_1155_);
lean_inc(v___x_1165_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1167_, lean_object* v_vals_1168_, lean_object* v_i_1169_, lean_object* v_k_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1167_, v_vals_1168_, v_i_1169_, v_k_1170_);
lean_dec(v_k_1170_);
lean_dec_ref(v_vals_1168_);
lean_dec_ref(v_keys_1167_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1172_, size_t v_x_1173_, lean_object* v_x_1174_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v_es_1175_; lean_object* v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v_j_1179_; lean_object* v___x_1180_; 
v_es_1175_ = lean_ctor_get(v_x_1172_, 0);
v___x_1176_ = lean_box(2);
v___x_1177_ = ((size_t)31ULL);
v___x_1178_ = lean_usize_land(v_x_1173_, v___x_1177_);
v_j_1179_ = lean_usize_to_nat(v___x_1178_);
v___x_1180_ = lean_array_get_borrowed(v___x_1176_, v_es_1175_, v_j_1179_);
lean_dec(v_j_1179_);
switch(lean_obj_tag(v___x_1180_))
{
case 0:
{
lean_object* v_key_1181_; lean_object* v_val_1182_; uint8_t v___x_1183_; 
v_key_1181_ = lean_ctor_get(v___x_1180_, 0);
v_val_1182_ = lean_ctor_get(v___x_1180_, 1);
v___x_1183_ = lean_name_eq(v_x_1174_, v_key_1181_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_box(0);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
lean_inc(v_val_1182_);
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_val_1182_);
return v___x_1185_;
}
}
case 1:
{
lean_object* v_node_1186_; size_t v___x_1187_; size_t v___x_1188_; 
v_node_1186_ = lean_ctor_get(v___x_1180_, 0);
v___x_1187_ = ((size_t)5ULL);
v___x_1188_ = lean_usize_shift_right(v_x_1173_, v___x_1187_);
v_x_1172_ = v_node_1186_;
v_x_1173_ = v___x_1188_;
goto _start;
}
default: 
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_box(0);
return v___x_1190_;
}
}
}
else
{
lean_object* v_ks_1191_; lean_object* v_vs_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_ks_1191_ = lean_ctor_get(v_x_1172_, 0);
v_vs_1192_ = lean_ctor_get(v_x_1172_, 1);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1191_, v_vs_1192_, v___x_1193_, v_x_1174_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
size_t v_x_422__boxed_1198_; lean_object* v_res_1199_; 
v_x_422__boxed_1198_ = lean_unbox_usize(v_x_1196_);
lean_dec(v_x_1196_);
v_res_1199_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1195_, v_x_422__boxed_1198_, v_x_1197_);
lean_dec(v_x_1197_);
lean_dec_ref(v_x_1195_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
uint64_t v___y_1203_; 
if (lean_obj_tag(v_x_1201_) == 0)
{
uint64_t v___x_1206_; 
v___x_1206_ = 1723ULL;
v___y_1203_ = v___x_1206_;
goto v___jp_1202_;
}
else
{
uint64_t v_hash_1207_; 
v_hash_1207_ = lean_ctor_get_uint64(v_x_1201_, sizeof(void*)*2);
v___y_1203_ = v_hash_1207_;
goto v___jp_1202_;
}
v___jp_1202_:
{
size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_uint64_to_usize(v___y_1203_);
v___x_1205_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1200_, v___x_1204_, v_x_1201_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1208_, v_x_1209_);
lean_dec(v_x_1209_);
lean_dec_ref(v_x_1208_);
return v_res_1210_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1214_, lean_object* v_declName_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1227_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1218_ = l_Lean_IR_declMapExt;
v___x_1227_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1214_, v_declName_1215_);
if (lean_obj_tag(v___x_1227_) == 0)
{
goto v___jp_1219_;
}
else
{
lean_object* v_val_1228_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1242_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1217_, v___x_1218_, v_env_1214_, v_val_1228_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_array_get_size(v___x_1242_);
v___x_1245_ = lean_nat_dec_lt(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec_ref(v___x_1242_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_sub(v___x_1244_, v___x_1246_);
v___x_1248_ = lean_nat_dec_le(v___x_1243_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec(v___x_1247_);
lean_dec_ref(v___x_1242_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_tmpDecl_1251_; lean_object* v___x_1252_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1250_ = lean_box(0);
lean_inc(v_declName_1215_);
v_tmpDecl_1251_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1251_, 0, v_declName_1215_);
lean_ctor_set(v_tmpDecl_1251_, 1, v___x_1249_);
lean_ctor_set(v_tmpDecl_1251_, 2, v___x_1250_);
lean_ctor_set(v_tmpDecl_1251_, 3, v___x_1216_);
v___x_1252_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1242_, v_tmpDecl_1251_, v___x_1243_, v___x_1247_);
lean_dec_ref_known(v_tmpDecl_1251_, 4);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v___x_1252_) == 0)
{
goto v___jp_1229_;
}
else
{
lean_dec(v_val_1228_);
lean_dec(v_declName_1215_);
lean_dec_ref(v_env_1214_);
return v___x_1252_;
}
}
}
v___jp_1229_:
{
uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1230_ = 0;
v___x_1231_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1217_, v___x_1218_, v_env_1214_, v_val_1228_, v___x_1230_);
lean_dec(v_val_1228_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_array_get_size(v___x_1231_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v___x_1231_);
goto v___jp_1219_;
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
goto v___jp_1219_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_tmpDecl_1240_; lean_object* v___x_1241_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1239_ = lean_box(0);
lean_inc(v_declName_1215_);
v_tmpDecl_1240_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1240_, 0, v_declName_1215_);
lean_ctor_set(v_tmpDecl_1240_, 1, v___x_1238_);
lean_ctor_set(v_tmpDecl_1240_, 2, v___x_1239_);
lean_ctor_set(v_tmpDecl_1240_, 3, v___x_1216_);
v___x_1241_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1231_, v_tmpDecl_1240_, v___x_1232_, v___x_1236_);
lean_dec_ref_known(v_tmpDecl_1240_, 4);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v___x_1241_) == 0)
{
goto v___jp_1219_;
}
else
{
lean_dec(v_declName_1215_);
lean_dec_ref(v_env_1214_);
return v___x_1241_;
}
}
}
}
}
v___jp_1219_:
{
lean_object* v_toEnvExtension_1220_; lean_object* v_asyncMode_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; 
v_toEnvExtension_1220_ = lean_ctor_get(v___x_1218_, 0);
v_asyncMode_1221_ = lean_ctor_get(v_toEnvExtension_1220_, 2);
v___x_1222_ = lean_box(0);
v___x_1223_ = 0;
v___x_1224_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1217_, v___x_1218_, v_env_1214_, v_asyncMode_1221_, v___x_1222_, v___x_1223_);
v_snd_1225_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_snd_1225_);
lean_dec(v___x_1224_);
v___x_1226_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1225_, v_declName_1215_);
lean_dec(v_declName_1215_);
lean_dec(v_snd_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1254_, v_x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1257_, v_x_1258_, v_x_1259_);
lean_dec(v_x_1259_);
lean_dec_ref(v_x_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1261_, lean_object* v_k_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1261_, v_k_1262_, v_x_1263_, v_x_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1267_, lean_object* v_k_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1267_, v_k_1268_, v_x_1269_, v_x_1270_, v_x_1271_);
lean_dec_ref(v_k_1268_);
lean_dec_ref(v_as_1267_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, size_t v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1274_, v_x_1275_, v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
size_t v_x_584__boxed_1282_; lean_object* v_res_1283_; 
v_x_584__boxed_1282_ = lean_unbox_usize(v_x_1280_);
lean_dec(v_x_1280_);
v_res_1283_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1278_, v_x_1279_, v_x_584__boxed_1282_, v_x_1281_);
lean_dec(v_x_1281_);
lean_dec_ref(v_x_1279_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1284_, lean_object* v_keys_1285_, lean_object* v_vals_1286_, lean_object* v_heq_1287_, lean_object* v_i_1288_, lean_object* v_k_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1285_, v_vals_1286_, v_i_1288_, v_k_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1291_, lean_object* v_keys_1292_, lean_object* v_vals_1293_, lean_object* v_heq_1294_, lean_object* v_i_1295_, lean_object* v_k_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1291_, v_keys_1292_, v_vals_1293_, v_heq_1294_, v_i_1295_, v_k_1296_);
lean_dec(v_k_1296_);
lean_dec_ref(v_vals_1293_);
lean_dec_ref(v_keys_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1298_, lean_object* v_declName_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1301_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1298_, v_declName_1299_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1302_; lean_object* v_toEnvExtension_1303_; lean_object* v_asyncMode_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1303_ = lean_ctor_get(v___x_1302_, 0);
v_asyncMode_1304_ = lean_ctor_get(v_toEnvExtension_1303_, 2);
v___x_1305_ = lean_box(0);
v___x_1306_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1300_, v___x_1302_, v_env_1298_, v_asyncMode_1304_, v___x_1305_);
v___x_1307_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1306_, v_declName_1299_);
lean_dec(v_declName_1299_);
lean_dec(v___x_1306_);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___y_1313_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_val_1308_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1311_ = l_Lean_IR_declMapExt;
v___x_1326_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1310_, v___x_1311_, v_env_1298_, v_val_1308_);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_array_get_size(v___x_1326_);
v___x_1329_ = lean_nat_dec_lt(v___x_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec_ref(v___x_1326_);
v___x_1330_ = lean_box(0);
v___y_1313_ = v___x_1330_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_sub(v___x_1328_, v___x_1331_);
v___x_1333_ = lean_nat_dec_le(v___x_1327_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1326_);
v___x_1334_ = lean_box(0);
v___y_1313_ = v___x_1334_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_tmpDecl_1337_; lean_object* v___x_1338_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1336_ = lean_box(0);
lean_inc(v_declName_1299_);
v_tmpDecl_1337_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1337_, 0, v_declName_1299_);
lean_ctor_set(v_tmpDecl_1337_, 1, v___x_1335_);
lean_ctor_set(v_tmpDecl_1337_, 2, v___x_1336_);
lean_ctor_set(v_tmpDecl_1337_, 3, v___x_1309_);
v___x_1338_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1326_, v_tmpDecl_1337_, v___x_1327_, v___x_1332_);
lean_dec_ref_known(v_tmpDecl_1337_, 4);
lean_dec_ref(v___x_1326_);
if (lean_obj_tag(v___x_1338_) == 0)
{
v___y_1313_ = v___x_1338_;
goto v___jp_1312_;
}
else
{
lean_dec(v_val_1308_);
lean_dec(v_declName_1299_);
lean_dec_ref(v_env_1298_);
return v___x_1338_;
}
}
}
v___jp_1312_:
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1314_ = 0;
v___x_1315_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1310_, v___x_1311_, v_env_1298_, v_val_1308_, v___x_1314_);
lean_dec(v_val_1308_);
lean_dec_ref(v_env_1298_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_array_get_size(v___x_1315_);
v___x_1318_ = lean_nat_dec_lt(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v___x_1315_);
lean_dec(v_declName_1299_);
return v___y_1313_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_nat_sub(v___x_1317_, v___x_1319_);
v___x_1321_ = lean_nat_dec_le(v___x_1316_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec(v___x_1320_);
lean_dec_ref(v___x_1315_);
lean_dec(v_declName_1299_);
return v___y_1313_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_tmpDecl_1324_; lean_object* v___x_1325_; 
lean_dec(v___y_1313_);
v___x_1322_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1323_ = lean_box(0);
v_tmpDecl_1324_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1324_, 0, v_declName_1299_);
lean_ctor_set(v_tmpDecl_1324_, 1, v___x_1322_);
lean_ctor_set(v_tmpDecl_1324_, 2, v___x_1323_);
lean_ctor_set(v_tmpDecl_1324_, 3, v___x_1309_);
v___x_1325_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1315_, v_tmpDecl_1324_, v___x_1316_, v___x_1320_);
lean_dec_ref_known(v_tmpDecl_1324_, 4);
lean_dec_ref(v___x_1315_);
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1339_, lean_object* v_declName_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v_boxed_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
lean_inc(v_declName_1340_);
v_boxed_1342_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1340_);
v___x_1343_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1339_, v_declName_1340_);
lean_dec(v_declName_1340_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; lean_object* v_toEnvExtension_1345_; lean_object* v_asyncMode_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1344_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1345_ = lean_ctor_get(v___x_1344_, 0);
v_asyncMode_1346_ = lean_ctor_get(v_toEnvExtension_1345_, 2);
v___x_1347_ = lean_box(0);
v___x_1348_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1341_, v___x_1344_, v_env_1339_, v_asyncMode_1346_, v___x_1347_);
v___x_1349_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1348_, v_boxed_1342_);
lean_dec(v_boxed_1342_);
lean_dec(v___x_1348_);
return v___x_1349_;
}
else
{
lean_object* v_val_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___y_1355_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_val_1350_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1353_ = l_Lean_IR_declMapExt;
v___x_1368_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1352_, v___x_1353_, v_env_1339_, v_val_1350_);
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v___x_1368_);
v___x_1371_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v___x_1368_);
v___x_1372_ = lean_box(0);
v___y_1355_ = v___x_1372_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_sub(v___x_1370_, v___x_1373_);
v___x_1375_ = lean_nat_dec_le(v___x_1369_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec(v___x_1374_);
lean_dec_ref(v___x_1368_);
v___x_1376_ = lean_box(0);
v___y_1355_ = v___x_1376_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_tmpDecl_1379_; lean_object* v___x_1380_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1378_ = lean_box(0);
lean_inc(v_boxed_1342_);
v_tmpDecl_1379_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1379_, 0, v_boxed_1342_);
lean_ctor_set(v_tmpDecl_1379_, 1, v___x_1377_);
lean_ctor_set(v_tmpDecl_1379_, 2, v___x_1378_);
lean_ctor_set(v_tmpDecl_1379_, 3, v___x_1351_);
v___x_1380_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1368_, v_tmpDecl_1379_, v___x_1369_, v___x_1374_);
lean_dec_ref_known(v_tmpDecl_1379_, 4);
lean_dec_ref(v___x_1368_);
if (lean_obj_tag(v___x_1380_) == 0)
{
v___y_1355_ = v___x_1380_;
goto v___jp_1354_;
}
else
{
lean_dec(v_val_1350_);
lean_dec(v_boxed_1342_);
lean_dec_ref(v_env_1339_);
return v___x_1380_;
}
}
}
v___jp_1354_:
{
uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1356_ = 0;
v___x_1357_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1352_, v___x_1353_, v_env_1339_, v_val_1350_, v___x_1356_);
lean_dec(v_val_1350_);
lean_dec_ref(v_env_1339_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_array_get_size(v___x_1357_);
v___x_1360_ = lean_nat_dec_lt(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_dec_ref(v___x_1357_);
lean_dec(v_boxed_1342_);
return v___y_1355_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_nat_sub(v___x_1359_, v___x_1361_);
v___x_1363_ = lean_nat_dec_le(v___x_1358_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec(v___x_1362_);
lean_dec_ref(v___x_1357_);
lean_dec(v_boxed_1342_);
return v___y_1355_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_tmpDecl_1366_; lean_object* v___x_1367_; 
lean_dec(v___y_1355_);
v___x_1364_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1365_ = lean_box(0);
v_tmpDecl_1366_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1366_, 0, v_boxed_1342_);
lean_ctor_set(v_tmpDecl_1366_, 1, v___x_1364_);
lean_ctor_set(v_tmpDecl_1366_, 2, v___x_1365_);
lean_ctor_set(v_tmpDecl_1366_, 3, v___x_1351_);
v___x_1367_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1357_, v_tmpDecl_1366_, v___x_1358_, v___x_1362_);
lean_dec_ref_known(v_tmpDecl_1366_, 4);
lean_dec_ref(v___x_1357_);
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1381_, lean_object* v_constName_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1381_, v_constName_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; lean_object* v_toEnvExtension_1385_; lean_object* v_asyncMode_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1384_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1385_ = lean_ctor_get(v___x_1384_, 0);
v_asyncMode_1386_ = lean_ctor_get(v_toEnvExtension_1385_, 2);
v___x_1387_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1387_, v___x_1384_, v_env_1381_, v_asyncMode_1386_, v___x_1388_);
v___x_1390_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_1389_, v_constName_1382_);
lean_dec(v_constName_1382_);
lean_dec(v___x_1389_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; 
v___x_1391_ = 1;
return v___x_1391_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = 0;
return v___x_1392_;
}
}
else
{
uint8_t v___x_1393_; 
lean_dec_ref_known(v___x_1383_, 1);
lean_dec(v_constName_1382_);
lean_dec_ref(v_env_1381_);
v___x_1393_ = 0;
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1394_, lean_object* v_constName_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = lean_has_compile_error(v_env_1394_, v_constName_1395_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v_env_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = lean_st_ref_get(v_a_1399_);
v_env_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc_ref(v_env_1402_);
lean_dec(v___x_1401_);
v___x_1403_ = l_Lean_IR_findEnvDecl(v_env_1402_, v_n_1398_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_IR_findDecl___redArg(v_n_1405_, v_a_1406_);
lean_dec(v_a_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_IR_findDecl___redArg(v_n_1409_, v_a_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_IR_findDecl(v_n_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1437_; 
v___x_1422_ = l_Lean_IR_findDecl___redArg(v_n_1419_, v_a_1420_);
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1437_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1437_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
if (lean_obj_tag(v_a_1423_) == 0)
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = 0;
v___x_1428_ = lean_box(v___x_1427_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1428_);
v___x_1430_ = v___x_1425_;
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
else
{
uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_dec_ref_known(v_a_1423_, 1);
v___x_1432_ = 1;
v___x_1433_ = lean_box(v___x_1432_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1433_);
v___x_1435_ = v___x_1425_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_IR_containsDecl___redArg(v_n_1438_, v_a_1439_);
lean_dec(v_a_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_IR_containsDecl___redArg(v_n_1442_, v_a_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_IR_containsDecl(v_n_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_ref_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_ref_1456_ = lean_ctor_get(v___y_1453_, 2);
v___x_1457_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1452_, v___y_1453_, v___y_1454_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_inc(v_ref_1456_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_ref_1456_);
lean_ctor_set(v___x_1462_, 1, v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 1);
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1496_; 
lean_inc(v_n_1474_);
v___x_1478_ = l_Lean_IR_findDecl___redArg(v_n_1474_, v_a_1476_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1496_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1496_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
if (lean_obj_tag(v_a_1479_) == 1)
{
lean_object* v_val_1483_; lean_object* v___x_1485_; 
lean_dec(v_n_1474_);
v_val_1483_ = lean_ctor_get(v_a_1479_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v_a_1479_, 1);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v_val_1483_);
v___x_1485_ = v___x_1481_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_val_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_del_object(v___x_1481_);
lean_dec(v_a_1479_);
v___x_1487_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1488_ = 1;
v___x_1489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1474_, v___x_1488_);
v___x_1490_ = lean_string_append(v___x_1487_, v___x_1489_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
v___x_1493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
v___x_1494_ = l_Lean_MessageData_ofFormat(v___x_1493_);
v___x_1495_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1494_, v_a_1475_, v_a_1476_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_IR_getDecl(v_n_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1503_, v___y_1504_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_msg_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1508_, v_msg_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_env_1519_; lean_object* v___x_1520_; lean_object* v_toEnvExtension_1521_; lean_object* v_asyncMode_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1517_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1518_ = lean_st_ref_get(v_a_1515_);
v_env_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_ref(v_env_1519_);
lean_dec(v___x_1518_);
v___x_1520_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1521_ = lean_ctor_get(v___x_1520_, 0);
v_asyncMode_1522_ = lean_ctor_get(v_toEnvExtension_1521_, 2);
v___x_1523_ = lean_box(0);
v___x_1524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1517_, v___x_1520_, v_env_1519_, v_asyncMode_1522_, v___x_1523_);
v___x_1525_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1524_, v_n_1514_);
lean_dec(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_IR_findLocalDecl___redArg(v_n_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec(v_n_1527_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_IR_findLocalDecl___redArg(v_n_1531_, v_a_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_IR_findLocalDecl(v_n_1536_, v_a_1537_, v_a_1538_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_n_1536_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v_toEnvExtension_1543_; lean_object* v_asyncMode_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1542_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1543_ = lean_ctor_get(v___x_1542_, 0);
v_asyncMode_1544_ = lean_ctor_get(v_toEnvExtension_1543_, 2);
v___x_1545_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1546_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1545_, v___x_1542_, v_env_1541_, v_asyncMode_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___lam__0(lean_object* v___x_1547_, lean_object* v_decl_1548_, lean_object* v_s_1549_){
_start:
{
lean_object* v_addEntryFn_1550_; lean_object* v_importedEntries_1551_; lean_object* v_state_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_addEntryFn_1550_ = lean_ctor_get(v___x_1547_, 3);
lean_inc(v_addEntryFn_1550_);
lean_dec_ref(v___x_1547_);
v_importedEntries_1551_ = lean_ctor_get(v_s_1549_, 0);
v_state_1552_ = lean_ctor_get(v_s_1549_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_s_1549_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1554_ = v_s_1549_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_state_1552_);
lean_inc(v_importedEntries_1551_);
lean_dec(v_s_1549_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_state_1556_; lean_object* v___x_1558_; 
v_state_1556_ = lean_apply_2(v_addEntryFn_1550_, v_state_1552_, v_decl_1548_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 1, v_state_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_importedEntries_1551_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_state_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v_env_1569_; lean_object* v_nextMacroScope_1570_; lean_object* v_ngen_1571_; lean_object* v_auxDeclNGen_1572_; lean_object* v_traceState_1573_; lean_object* v_recordedDeps_1574_; lean_object* v_messages_1575_; lean_object* v_infoState_1576_; lean_object* v_snapshotTasks_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1600_; 
v___x_1568_ = lean_st_ref_take(v_a_1566_);
v_env_1569_ = lean_ctor_get(v___x_1568_, 0);
v_nextMacroScope_1570_ = lean_ctor_get(v___x_1568_, 1);
v_ngen_1571_ = lean_ctor_get(v___x_1568_, 2);
v_auxDeclNGen_1572_ = lean_ctor_get(v___x_1568_, 3);
v_traceState_1573_ = lean_ctor_get(v___x_1568_, 4);
v_recordedDeps_1574_ = lean_ctor_get(v___x_1568_, 6);
v_messages_1575_ = lean_ctor_get(v___x_1568_, 7);
v_infoState_1576_ = lean_ctor_get(v___x_1568_, 8);
v_snapshotTasks_1577_ = lean_ctor_get(v___x_1568_, 9);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v___x_1568_, 5);
lean_dec(v_unused_1601_);
v___x_1579_ = v___x_1568_;
v_isShared_1580_ = v_isSharedCheck_1600_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snapshotTasks_1577_);
lean_inc(v_infoState_1576_);
lean_inc(v_messages_1575_);
lean_inc(v_recordedDeps_1574_);
lean_inc(v_traceState_1573_);
lean_inc(v_auxDeclNGen_1572_);
lean_inc(v_ngen_1571_);
lean_inc(v_nextMacroScope_1570_);
lean_inc(v_env_1569_);
lean_dec(v___x_1568_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1600_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v_toEnvExtension_1582_; lean_object* v_asyncMode_1583_; uint8_t v_logWrites_1584_; lean_object* v___x_1585_; lean_object* v___y_1587_; lean_object* v___f_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1581_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1582_ = lean_ctor_get(v___x_1581_, 0);
v_asyncMode_1583_ = lean_ctor_get(v_toEnvExtension_1582_, 2);
v_logWrites_1584_ = lean_ctor_get_uint8(v_toEnvExtension_1582_, sizeof(void*)*6);
v___x_1585_ = lean_box(0);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_IR_addDecl___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1594_, 0, v___x_1581_);
lean_closure_set(v___f_1594_, 1, v_decl_1565_);
v___x_1595_ = lean_box(0);
v___x_1596_ = 1;
if (v_logWrites_1584_ == 0)
{
lean_object* v___x_1597_; 
lean_inc_ref(v_toEnvExtension_1582_);
v___x_1597_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1582_, v_env_1569_, v___f_1594_, v_asyncMode_1583_, v___x_1595_, v___x_1596_);
v___y_1587_ = v___x_1597_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_inc_ref_n(v_toEnvExtension_1582_, 2);
v___x_1598_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1582_, v_env_1569_);
lean_dec_ref(v_env_1569_);
v___x_1599_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1582_, v___x_1598_, v___f_1594_, v_asyncMode_1583_, v___x_1595_, v___x_1596_);
v___y_1587_ = v___x_1599_;
goto v___jp_1586_;
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 5, v___x_1588_);
lean_ctor_set(v___x_1579_, 0, v___y_1587_);
v___x_1590_ = v___x_1579_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___y_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_nextMacroScope_1570_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_ngen_1571_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_auxDeclNGen_1572_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_traceState_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_recordedDeps_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_messages_1575_);
lean_ctor_set(v_reuseFailAlloc_1593_, 8, v_infoState_1576_);
lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_snapshotTasks_1577_);
v___x_1590_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_st_ref_put(v_a_1566_, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1585_);
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_IR_addDecl___redArg(v_decl_1602_, v_a_1603_);
lean_dec(v_a_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_IR_addDecl___redArg(v_decl_1606_, v_a_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_IR_addDecl(v_decl_1611_, v_a_1612_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1616_, size_t v_i_1617_, size_t v_stop_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_usize_dec_eq(v_i_1617_, v_stop_1618_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_array_uget_borrowed(v_as_1616_, v_i_1617_);
lean_inc(v___x_1623_);
v___x_1624_ = l_Lean_IR_addDecl___redArg(v___x_1623_, v___y_1620_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; size_t v___x_1626_; size_t v___x_1627_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_add(v_i_1617_, v___x_1626_);
v_i_1617_ = v___x_1627_;
v_b_1619_ = v_a_1625_;
goto _start;
}
else
{
return v___x_1624_;
}
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_b_1619_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1630_, lean_object* v_i_1631_, lean_object* v_stop_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
size_t v_i_boxed_1636_; size_t v_stop_boxed_1637_; lean_object* v_res_1638_; 
v_i_boxed_1636_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_stop_boxed_1637_ = lean_unbox_usize(v_stop_1632_);
lean_dec(v_stop_1632_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1630_, v_i_boxed_1636_, v_stop_boxed_1637_, v_b_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v_as_1630_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_array_get_size(v_decls_1639_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_nat_dec_lt(v___x_1643_, v___x_1644_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
return v___x_1647_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_le(v___x_1644_, v___x_1644_);
if (v___x_1648_ == 0)
{
if (v___x_1646_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1645_);
return v___x_1649_;
}
else
{
size_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = lean_usize_of_nat(v___x_1644_);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1639_, v___x_1650_, v___x_1651_, v___x_1645_, v_a_1641_);
return v___x_1652_;
}
}
else
{
size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((size_t)0ULL);
v___x_1654_ = lean_usize_of_nat(v___x_1644_);
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1639_, v___x_1653_, v___x_1654_, v___x_1645_, v_a_1641_);
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_IR_addDecls(v_decls_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec_ref(v_decls_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1661_, size_t v_i_1662_, size_t v_stop_1663_, lean_object* v_b_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1661_, v_i_1662_, v_stop_1663_, v_b_1664_, v___y_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1669_, lean_object* v_i_1670_, lean_object* v_stop_1671_, lean_object* v_b_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
size_t v_i_boxed_1676_; size_t v_stop_boxed_1677_; lean_object* v_res_1678_; 
v_i_boxed_1676_ = lean_unbox_usize(v_i_1670_);
lean_dec(v_i_1670_);
v_stop_boxed_1677_ = lean_unbox_usize(v_stop_1671_);
lean_dec(v_stop_1671_);
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1669_, v_i_boxed_1676_, v_stop_boxed_1677_, v_b_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec_ref(v_as_1669_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1682_, lean_object* v_as_1683_, size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_b_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1687_ == 0)
{
lean_inc_ref(v_b_1686_);
return v_b_1686_;
}
else
{
lean_object* v___x_1688_; lean_object* v_a_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1688_ = lean_box(0);
v_a_1689_ = lean_array_uget_borrowed(v_as_1683_, v_i_1685_);
v___x_1690_ = l_Lean_IR_Decl_name(v_a_1689_);
v___x_1691_ = lean_name_eq(v___x_1690_, v_n_1682_);
lean_dec(v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; 
v___x_1692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_add(v_i_1685_, v___x_1693_);
v_i_1685_ = v___x_1694_;
v_b_1686_ = v___x_1692_;
goto _start;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_inc(v_a_1689_);
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1689_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___x_1688_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1699_, lean_object* v_as_1700_, lean_object* v_sz_1701_, lean_object* v_i_1702_, lean_object* v_b_1703_){
_start:
{
size_t v_sz_boxed_1704_; size_t v_i_boxed_1705_; lean_object* v_res_1706_; 
v_sz_boxed_1704_ = lean_unbox_usize(v_sz_1701_);
lean_dec(v_sz_1701_);
v_i_boxed_1705_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_res_1706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1699_, v_as_1700_, v_sz_boxed_1704_, v_i_boxed_1705_, v_b_1703_);
lean_dec_ref(v_b_1703_);
lean_dec_ref(v_as_1700_);
lean_dec(v_n_1699_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1707_, lean_object* v_n_1708_, lean_object* v_decls_1709_){
_start:
{
lean_object* v___x_1710_; size_t v_sz_1711_; size_t v___x_1712_; lean_object* v___x_1713_; lean_object* v_fst_1714_; 
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1711_ = lean_array_size(v_decls_1709_);
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1708_, v_decls_1709_, v_sz_1711_, v___x_1712_, v___x_1710_);
v_fst_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_fst_1714_);
lean_dec_ref(v___x_1713_);
if (lean_obj_tag(v_fst_1714_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_IR_findEnvDecl(v_env_1707_, v_n_1708_);
return v___x_1715_;
}
else
{
lean_object* v_val_1716_; 
v_val_1716_ = lean_ctor_get(v_fst_1714_, 0);
lean_inc(v_val_1716_);
lean_dec_ref_known(v_fst_1714_, 1);
if (lean_obj_tag(v_val_1716_) == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_IR_findEnvDecl(v_env_1707_, v_n_1708_);
return v___x_1717_;
}
else
{
lean_dec(v_n_1708_);
lean_dec_ref(v_env_1707_);
return v_val_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1718_, lean_object* v_n_1719_, lean_object* v_decls_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_IR_findEnvDecl_x27(v_env_1718_, v_n_1719_, v_decls_1720_);
lean_dec_ref(v_decls_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1722_, lean_object* v_decls_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v_env_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1726_ = lean_st_ref_get(v_a_1724_);
v_env_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_ref(v_env_1727_);
lean_dec(v___x_1726_);
v___x_1728_ = l_Lean_IR_findEnvDecl_x27(v_env_1727_, v_n_1722_, v_decls_1723_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1730_, lean_object* v_decls_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_IR_findDecl_x27___redArg(v_n_1730_, v_decls_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_decls_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1735_, lean_object* v_decls_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_IR_findDecl_x27___redArg(v_n_1735_, v_decls_1736_, v_a_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1741_, lean_object* v_decls_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_IR_findDecl_x27(v_n_1741_, v_decls_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec_ref(v_decls_1742_);
return v_res_1746_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1747_, lean_object* v_as_1748_, size_t v_i_1749_, size_t v_stop_1750_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_eq(v_i_1749_, v_stop_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = lean_array_uget_borrowed(v_as_1748_, v_i_1749_);
v___x_1753_ = l_Lean_IR_Decl_name(v___x_1752_);
v___x_1754_ = lean_name_eq(v___x_1753_, v_n_1747_);
lean_dec(v___x_1753_);
if (v___x_1754_ == 0)
{
size_t v___x_1755_; size_t v___x_1756_; 
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1749_, v___x_1755_);
v_i_1749_ = v___x_1756_;
goto _start;
}
else
{
return v___x_1754_;
}
}
else
{
uint8_t v___x_1758_; 
v___x_1758_ = 0;
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1759_, lean_object* v_as_1760_, lean_object* v_i_1761_, lean_object* v_stop_1762_){
_start:
{
size_t v_i_boxed_1763_; size_t v_stop_boxed_1764_; uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_i_boxed_1763_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_stop_boxed_1764_ = lean_unbox_usize(v_stop_1762_);
lean_dec(v_stop_1762_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1759_, v_as_1760_, v_i_boxed_1763_, v_stop_boxed_1764_);
lean_dec_ref(v_as_1760_);
lean_dec(v_n_1759_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1767_, lean_object* v_decls_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_array_get_size(v_decls_1768_);
v___x_1773_ = lean_nat_dec_lt(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_IR_containsDecl___redArg(v_n_1767_, v_a_1769_);
return v___x_1774_;
}
else
{
if (v___x_1773_ == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_IR_containsDecl___redArg(v_n_1767_, v_a_1769_);
return v___x_1775_;
}
else
{
size_t v___x_1776_; size_t v___x_1777_; uint8_t v___x_1778_; 
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1772_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1767_, v_decls_1768_, v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_IR_containsDecl___redArg(v_n_1767_, v_a_1769_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v_n_1767_);
v___x_1780_ = lean_box(v___x_1773_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1782_, lean_object* v_decls_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1782_, v_decls_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_decls_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1787_, lean_object* v_decls_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1787_, v_decls_1788_, v_a_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1793_, lean_object* v_decls_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_IR_containsDecl_x27(v_n_1793_, v_decls_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec_ref(v_decls_1794_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1799_, lean_object* v_decls_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1822_; 
lean_inc(v_n_1799_);
v___x_1804_ = l_Lean_IR_findDecl_x27___redArg(v_n_1799_, v_decls_1800_, v_a_1802_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1822_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1822_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
if (lean_obj_tag(v_a_1805_) == 1)
{
lean_object* v_val_1809_; lean_object* v___x_1811_; 
lean_dec(v_n_1799_);
v_val_1809_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_val_1809_);
lean_dec_ref_known(v_a_1805_, 1);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_val_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_val_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_del_object(v___x_1807_);
lean_dec(v_a_1805_);
v___x_1813_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1814_ = 1;
v___x_1815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1799_, v___x_1814_);
v___x_1816_ = lean_string_append(v___x_1813_, v___x_1815_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
v___x_1820_ = l_Lean_MessageData_ofFormat(v___x_1819_);
v___x_1821_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1820_, v_a_1801_, v_a_1802_);
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1823_, lean_object* v_decls_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_IR_getDecl_x27(v_n_1823_, v_decls_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec_ref(v_decls_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1829_, lean_object* v_declName_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_IR_findEnvDecl(v_env_1829_, v_declName_1830_);
if (lean_obj_tag(v___x_1831_) == 1)
{
lean_object* v_val_1832_; 
v_val_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v___x_1831_, 1);
if (lean_obj_tag(v_val_1832_) == 0)
{
lean_object* v_info_1833_; 
v_info_1833_ = lean_ctor_get(v_val_1832_, 4);
lean_inc(v_info_1833_);
lean_dec_ref_known(v_val_1832_, 5);
return v_info_1833_;
}
else
{
lean_object* v___x_1834_; 
lean_dec(v_val_1832_);
v___x_1834_ = lean_box(0);
return v___x_1834_;
}
}
else
{
lean_object* v___x_1835_; 
lean_dec(v___x_1831_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(uint8_t v_level_1836_, lean_object* v_env_1837_, uint8_t v_includeDecls_1838_, lean_object* v_as_1839_, size_t v_i_1840_, size_t v_stop_1841_, lean_object* v_b_1842_){
_start:
{
lean_object* v___y_1844_; uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_eq(v_i_1840_, v_stop_1841_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; uint8_t v___y_1851_; 
v___x_1849_ = lean_array_uget_borrowed(v_as_1839_, v_i_1840_);
if (v_includeDecls_1838_ == 0)
{
uint8_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = 1;
lean_inc(v___x_1849_);
lean_inc_ref(v_env_1837_);
v___x_1862_ = l_Lean_Environment_contains(v_env_1837_, v___x_1849_, v___x_1861_);
if (v___x_1862_ == 0)
{
goto v___jp_1853_;
}
else
{
v___y_1844_ = v_b_1842_;
goto v___jp_1843_;
}
}
else
{
goto v___jp_1853_;
}
v___jp_1850_:
{
if (v___y_1851_ == 0)
{
v___y_1844_ = v_b_1842_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1852_; 
lean_inc(v___x_1849_);
v___x_1852_ = lean_array_push(v_b_1842_, v___x_1849_);
v___y_1844_ = v___x_1852_;
goto v___jp_1843_;
}
}
v___jp_1853_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1854_ = lean_box(v_level_1836_);
v___x_1855_ = lean_obj_tag_nat(v___x_1854_);
lean_dec(v___x_1854_);
v___x_1856_ = lean_unsigned_to_nat(2u);
v___x_1857_ = lean_nat_dec_eq(v___x_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
uint8_t v___x_1858_; 
lean_inc_ref(v_env_1837_);
v___x_1858_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1837_, v___x_1849_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
lean_inc_ref(v_env_1837_);
v___x_1859_ = l_Lean_isDeclMeta(v_env_1837_, v___x_1849_);
v___y_1851_ = v___x_1859_;
goto v___jp_1850_;
}
else
{
v___y_1851_ = v___x_1858_;
goto v___jp_1850_;
}
}
else
{
lean_object* v___x_1860_; 
lean_inc(v___x_1849_);
v___x_1860_ = lean_array_push(v_b_1842_, v___x_1849_);
v___y_1844_ = v___x_1860_;
goto v___jp_1843_;
}
}
}
else
{
lean_dec_ref(v_env_1837_);
return v_b_1842_;
}
v___jp_1843_:
{
size_t v___x_1845_; size_t v___x_1846_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1840_, v___x_1845_);
v_i_1840_ = v___x_1846_;
v_b_1842_ = v___y_1844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_level_1863_, lean_object* v_env_1864_, lean_object* v_includeDecls_1865_, lean_object* v_as_1866_, lean_object* v_i_1867_, lean_object* v_stop_1868_, lean_object* v_b_1869_){
_start:
{
uint8_t v_level_boxed_1870_; uint8_t v_includeDecls_boxed_1871_; size_t v_i_boxed_1872_; size_t v_stop_boxed_1873_; lean_object* v_res_1874_; 
v_level_boxed_1870_ = lean_unbox(v_level_1863_);
v_includeDecls_boxed_1871_ = lean_unbox(v_includeDecls_1865_);
v_i_boxed_1872_ = lean_unbox_usize(v_i_1867_);
lean_dec(v_i_1867_);
v_stop_boxed_1873_ = lean_unbox_usize(v_stop_1868_);
lean_dec(v_stop_1868_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_boxed_1870_, v_env_1864_, v_includeDecls_boxed_1871_, v_as_1866_, v_i_boxed_1872_, v_stop_boxed_1873_, v_b_1869_);
lean_dec_ref(v_as_1866_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1875_, size_t v_i_1876_, lean_object* v_bs_1877_){
_start:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_usize_dec_lt(v_i_1876_, v_sz_1875_);
if (v___x_1878_ == 0)
{
return v_bs_1877_;
}
else
{
lean_object* v_v_1879_; lean_object* v___x_1880_; lean_object* v_bs_x27_1881_; lean_object* v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v_v_1879_ = lean_array_uget(v_bs_1877_, v_i_1876_);
v___x_1880_ = lean_unsigned_to_nat(0u);
v_bs_x27_1881_ = lean_array_uset(v_bs_1877_, v_i_1876_, v___x_1880_);
v___x_1882_ = l_Lean_IR_Decl_name(v_v_1879_);
lean_dec(v_v_1879_);
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_add(v_i_1876_, v___x_1883_);
v___x_1885_ = lean_array_uset(v_bs_x27_1881_, v_i_1876_, v___x_1882_);
v_i_1876_ = v___x_1884_;
v_bs_1877_ = v___x_1885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1887_, lean_object* v_i_1888_, lean_object* v_bs_1889_){
_start:
{
size_t v_sz_boxed_1890_; size_t v_i_boxed_1891_; lean_object* v_res_1892_; 
v_sz_boxed_1890_ = lean_unbox_usize(v_sz_1887_);
lean_dec(v_sz_1887_);
v_i_boxed_1891_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_res_1892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1890_, v_i_boxed_1891_, v_bs_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1895_, uint8_t v_level_1896_, uint8_t v_includeDecls_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v_toEnvExtension_1899_; lean_object* v_asyncMode_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v_env_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; size_t v_sz_1909_; size_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1898_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1899_ = lean_ctor_get(v___x_1898_, 0);
v_asyncMode_1900_ = lean_ctor_get(v_toEnvExtension_1899_, 2);
v___x_1901_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
v___x_1902_ = lean_box(v_level_1896_);
v___x_1903_ = lean_obj_tag_nat(v___x_1902_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_nat_dec_eq(v___x_1903_, v___x_1904_);
v_env_1906_ = l_Lean_Environment_setExporting(v_env_1895_, v___x_1905_);
lean_inc_ref(v_env_1906_);
v___x_1907_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1901_, v___x_1898_, v_env_1906_, v_asyncMode_1900_);
v___x_1908_ = lean_array_mk(v___x_1907_);
v_sz_1909_ = lean_array_size(v___x_1908_);
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1909_, v___x_1910_, v___x_1908_);
v___x_1912_ = lean_array_get_size(v___x_1911_);
v___x_1913_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1914_ = lean_nat_dec_lt(v___x_1904_, v___x_1912_);
if (v___x_1914_ == 0)
{
lean_dec_ref(v___x_1911_);
lean_dec_ref(v_env_1906_);
return v___x_1913_;
}
else
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_nat_dec_le(v___x_1912_, v___x_1912_);
if (v___x_1915_ == 0)
{
if (v___x_1914_ == 0)
{
lean_dec_ref(v___x_1911_);
lean_dec_ref(v_env_1906_);
return v___x_1913_;
}
else
{
size_t v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_usize_of_nat(v___x_1912_);
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1896_, v_env_1906_, v_includeDecls_1897_, v___x_1911_, v___x_1910_, v___x_1916_, v___x_1913_);
lean_dec_ref(v___x_1911_);
return v___x_1917_;
}
}
else
{
size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_usize_of_nat(v___x_1912_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_level_1896_, v_env_1906_, v_includeDecls_1897_, v___x_1911_, v___x_1910_, v___x_1918_, v___x_1913_);
lean_dec_ref(v___x_1911_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1920_, lean_object* v_level_1921_, lean_object* v_includeDecls_1922_){
_start:
{
uint8_t v_level_boxed_1923_; uint8_t v_includeDecls_boxed_1924_; lean_object* v_res_1925_; 
v_level_boxed_1923_ = lean_unbox(v_level_1921_);
v_includeDecls_boxed_1924_ = lean_unbox(v_includeDecls_1922_);
v_res_1925_ = lean_get_ir_extra_const_names(v_env_1920_, v_level_boxed_1923_, v_includeDecls_boxed_1924_);
return v_res_1925_;
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
