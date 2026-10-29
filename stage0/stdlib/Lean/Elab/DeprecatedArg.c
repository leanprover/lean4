// Lean compiler output
// Module: Lean.Elab.DeprecatedArg
// Imports: public import Lean.EnvExtension public import Lean.Message import Lean.Elab.Term import Lean.Linter.Deprecated
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_mkSinceHint(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(34, 76, 221, 236, 220, 4, 80, 27)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "if true, generate deprecation warnings and errors for deprecated parameters"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 137, 139, 132, 156, 105, 17, 87)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 255, 51, 83, 51, 207, 102, 168)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 17, 141, 46, 239, 35, 224, 220)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_linter_deprecated_arg;
static const lean_ctor_object l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry_default = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deprecatedArgExt"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 157, 100, 72, 87, 251, 253, 102)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedArgExt;
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__0 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__1;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parameter `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__2 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__3;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__4 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__5;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__6 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__7;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` has been deprecated, use `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__8 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__9;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__10 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 138, .m_capacity = 138, .m_length = 137, .m_data = "`[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is still a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`; rename it to `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "` before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` is not a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`; remove it before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Invalid `[deprecated_arg]` attribute syntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DeprecatedArg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 168, 92, 104, 219, 200, 6, 160)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 45, 177, 228, 29, 219, 125, 116)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 25, 22, 75, 158, 128, 229, 101)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(107, 124, 96, 157, 76, 98, 131, 88)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 213, 49, 250, 165, 149, 52, 239)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 47, 237, 141, 165, 175, 79, 67)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(126, 84, 26, 57, 180, 177, 26, 182)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(140, 241, 34, 119, 16, 121, 80, 72)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 144, 188, 92, 44, 216, 0, 99)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecated_arg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 7, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(45, 182, 86, 230, 168, 246, 164, 173)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark a parameter as deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(lean_object* v_s_67_, lean_object* v_e_68_){
_start:
{
lean_object* v_declName_69_; lean_object* v_oldArg_70_; lean_object* v___y_72_; lean_object* v___x_75_; 
v_declName_69_ = lean_ctor_get(v_e_68_, 0);
lean_inc(v_declName_69_);
v_oldArg_70_ = lean_ctor_get(v_e_68_, 1);
lean_inc(v_oldArg_70_);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_67_, v_declName_69_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
v___y_72_ = v___x_76_;
goto v___jp_71_;
}
else
{
lean_object* v_val_77_; 
v_val_77_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v___x_75_, 1);
v___y_72_ = v_val_77_;
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v_inner_73_; lean_object* v___x_74_; 
v_inner_73_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_oldArg_70_, v_e_68_, v___y_72_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_69_, v_inner_73_, v_s_67_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(lean_object* v_es_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_array_mk(v_es_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_85_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_85_);
v___x_86_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(v_b_83_, v___x_85_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_81_, v___x_87_);
v_i_81_ = v___x_88_;
v_b_83_ = v___x_86_;
goto _start;
}
else
{
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v_b_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; lean_object* v_res_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v_as_90_, v_i_boxed_94_, v_stop_boxed_95_, v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_97_, size_t v_i_98_, size_t v_stop_99_, lean_object* v_b_100_){
_start:
{
lean_object* v___y_102_; uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_eq(v_i_98_, v_stop_99_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_107_ = lean_array_uget_borrowed(v_as_97_, v_i_98_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_array_get_size(v___x_107_);
v___x_110_ = lean_nat_dec_lt(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
v___y_102_ = v_b_100_;
goto v___jp_101_;
}
else
{
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_of_nat(v___x_109_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_107_, v___x_111_, v___x_112_, v_b_100_);
v___y_102_ = v___x_113_;
goto v___jp_101_;
}
}
else
{
return v_b_100_;
}
v___jp_101_:
{
size_t v___x_103_; size_t v___x_104_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_98_, v___x_103_);
v_i_98_ = v___x_104_;
v_b_100_ = v___y_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v_b_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_114_, v_i_boxed_118_, v_stop_boxed_119_, v_b_117_);
lean_dec_ref(v_as_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object* v_initState_121_, lean_object* v_as_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_array_get_size(v_as_122_);
v___x_125_ = lean_nat_dec_lt(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
return v_initState_121_;
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_124_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_122_, v___x_126_, v___x_127_, v_initState_121_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_129_, lean_object* v_as_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(v_initState_129_, v_as_130_);
lean_dec_ref(v_as_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_));
v___x_151_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object* v_env_154_, lean_object* v_declName_155_, lean_object* v_argName_156_){
_start:
{
lean_object* v___x_157_; lean_object* v_toEnvExtension_158_; lean_object* v_asyncMode_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_158_ = lean_ctor_get(v___x_157_, 0);
v_asyncMode_159_ = lean_ctor_get(v_toEnvExtension_158_, 2);
v___x_160_ = lean_box(1);
v___x_161_ = lean_box(0);
v___x_162_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_160_, v___x_157_, v_env_154_, v_asyncMode_159_, v___x_161_);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_162_, v_declName_155_);
lean_dec(v___x_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v_val_165_; lean_object* v___x_166_; 
v_val_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_163_, 1);
v___x_166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_165_, v_argName_156_);
lean_dec(v_val_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object* v_env_167_, lean_object* v_declName_168_, lean_object* v_argName_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Elab_findDeprecatedArg_x3f(v_env_167_, v_declName_168_, v_argName_169_);
lean_dec(v_argName_169_);
lean_dec(v_declName_168_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__0));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__2));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__4));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__6));
v___x_182_ = l_Lean_stringToMessageData(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__8));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__10));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object* v_entry_189_){
_start:
{
lean_object* v_declName_190_; lean_object* v_oldArg_191_; lean_object* v_newArg_x3f_192_; lean_object* v_text_x3f_193_; lean_object* v___y_195_; 
v_declName_190_ = lean_ctor_get(v_entry_189_, 0);
lean_inc(v_declName_190_);
v_oldArg_191_ = lean_ctor_get(v_entry_189_, 1);
lean_inc(v_oldArg_191_);
v_newArg_x3f_192_ = lean_ctor_get(v_entry_189_, 2);
lean_inc(v_newArg_x3f_192_);
v_text_x3f_193_ = lean_ctor_get(v_entry_189_, 3);
lean_inc(v_text_x3f_193_);
lean_dec_ref(v_entry_189_);
if (lean_obj_tag(v_newArg_x3f_192_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_201_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_202_ = l_Lean_MessageData_ofName(v_oldArg_191_);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = 0;
v___x_207_ = l_Lean_MessageData_ofConstName(v_declName_190_, v___x_206_);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__7, &l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___y_195_ = v___x_210_;
goto v___jp_194_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_val_211_ = lean_ctor_get(v_newArg_x3f_192_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v_newArg_x3f_192_, 1);
v___x_212_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_213_ = l_Lean_MessageData_ofName(v_oldArg_191_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = 0;
v___x_218_ = l_Lean_MessageData_ofConstName(v_declName_190_, v___x_217_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_216_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__9, &l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_MessageData_ofName(v_val_211_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__11, &l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___y_195_ = v___x_225_;
goto v___jp_194_;
}
v___jp_194_:
{
if (lean_obj_tag(v_text_x3f_193_) == 0)
{
return v___y_195_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_val_196_ = lean_ctor_get(v_text_x3f_193_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v_text_x3f_193_, 1);
v___x_197_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__1, &l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1);
v___x_198_ = l_Lean_stringToMessageData(v_val_196_);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_195_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___lam__0(lean_object* v_k_226_, lean_object* v_b_227_, lean_object* v_c_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
v___x_234_ = lean_apply_7(v_k_226_, v_b_227_, v_c_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, lean_box(0));
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(lean_object* v_k_235_, lean_object* v_b_236_, lean_object* v_c_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___lam__0(v_k_235_, v_b_236_, v_c_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg(lean_object* v_type_244_, lean_object* v_k_245_, uint8_t v_cleanupAnnotations_246_, uint8_t v_whnfType_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_253_, 0, v_k_245_);
v___x_254_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_244_, v___f_253_, v_cleanupAnnotations_246_, v_whnfType_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_254_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_type_271_, lean_object* v_k_272_, lean_object* v_cleanupAnnotations_273_, lean_object* v_whnfType_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_280_; uint8_t v_whnfType_boxed_281_; lean_object* v_res_282_; 
v_cleanupAnnotations_boxed_280_ = lean_unbox(v_cleanupAnnotations_273_);
v_whnfType_boxed_281_ = lean_unbox(v_whnfType_274_);
v_res_282_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg(v_type_271_, v_k_272_, v_cleanupAnnotations_boxed_280_, v_whnfType_boxed_281_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_283_, lean_object* v_type_284_, lean_object* v_k_285_, uint8_t v_cleanupAnnotations_286_, uint8_t v_whnfType_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg(v_type_284_, v_k_285_, v_cleanupAnnotations_286_, v_whnfType_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_294_, lean_object* v_type_295_, lean_object* v_k_296_, lean_object* v_cleanupAnnotations_297_, lean_object* v_whnfType_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_304_; uint8_t v_whnfType_boxed_305_; lean_object* v_res_306_; 
v_cleanupAnnotations_boxed_304_ = lean_unbox(v_cleanupAnnotations_297_);
v_whnfType_boxed_305_ = lean_unbox(v_whnfType_298_);
v_res_306_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(v_00_u03b1_294_, v_type_295_, v_k_296_, v_cleanupAnnotations_boxed_304_, v_whnfType_boxed_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(size_t v_sz_307_, size_t v_i_308_, lean_object* v_bs_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_bs_309_);
return v___x_315_;
}
else
{
lean_object* v_v_316_; lean_object* v___x_317_; lean_object* v_bs_x27_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_v_316_ = lean_array_uget(v_bs_309_, v_i_308_);
v___x_317_ = lean_unsigned_to_nat(0u);
v_bs_x27_318_ = lean_array_uset(v_bs_309_, v_i_308_, v___x_317_);
v___x_319_ = l_Lean_Expr_fvarId_x21(v_v_316_);
lean_dec(v_v_316_);
v___x_320_ = l_Lean_FVarId_getDecl___redArg(v___x_319_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = l_Lean_LocalDecl_userName(v_a_321_);
lean_dec(v_a_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_308_, v___x_323_);
v___x_325_ = lean_array_uset(v_bs_x27_318_, v_i_308_, v___x_322_);
v_i_308_ = v___x_324_;
v_bs_309_ = v___x_325_;
goto _start;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_bs_x27_318_);
v_a_327_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_320_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_320_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_bs_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_343_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(v_sz_boxed_342_, v_i_boxed_343_, v_bs_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v_xs_345_, lean_object* v_x_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
size_t v_sz_352_; size_t v___x_353_; lean_object* v___x_354_; 
v_sz_352_ = lean_array_size(v_xs_345_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(v_sz_352_, v___x_353_, v_xs_345_, v___y_347_, v___y_349_, v___y_350_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v_xs_355_, lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(v_xs_355_, v_x_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_x_356_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v_addEntryFn_363_, lean_object* v___x_364_, lean_object* v_s_365_){
_start:
{
lean_object* v_importedEntries_366_; lean_object* v_state_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_importedEntries_366_ = lean_ctor_get(v_s_365_, 0);
v_state_367_ = lean_ctor_get(v_s_365_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_s_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v_s_365_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_state_367_);
lean_inc(v_importedEntries_366_);
lean_dec(v_s_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_state_371_; lean_object* v___x_373_; 
v_state_371_ = lean_apply_2(v_addEntryFn_363_, v_state_367_, v___x_364_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_state_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_importedEntries_366_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_state_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_376_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_380_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_ctor_set(v___x_382_, 2, v___x_381_);
lean_ctor_set(v___x_382_, 3, v___x_381_);
lean_ctor_set(v___x_382_, 4, v___x_380_);
lean_ctor_set(v___x_382_, 5, v___x_380_);
lean_ctor_set(v___x_382_, 6, v___x_380_);
lean_ctor_set(v___x_382_, 7, v___x_380_);
lean_ctor_set(v___x_382_, 8, v___x_380_);
lean_ctor_set(v___x_382_, 9, v___x_380_);
lean_ctor_set(v___x_382_, 10, v___x_380_);
lean_ctor_set(v___x_382_, 11, v___x_379_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_unsigned_to_nat(32u);
v___x_384_ = lean_mk_empty_array_with_capacity(v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_386_ = ((size_t)5ULL);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_unsigned_to_nat(32u);
v___x_389_ = lean_mk_empty_array_with_capacity(v___x_388_);
v___x_390_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_391_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_387_);
lean_ctor_set(v___x_391_, 3, v___x_387_);
lean_ctor_set_usize(v___x_391_, 4, v___x_386_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_box(1);
v___x_393_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4);
v___x_394_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
lean_ctor_set(v___x_395_, 2, v___x_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_toCold_401_; lean_object* v_env_402_; lean_object* v_options_403_; uint8_t v___x_404_; lean_object* v_env_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_400_ = lean_st_ref_get(v___y_398_);
v_toCold_401_ = lean_ctor_get(v___y_397_, 0);
v_env_402_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_400_);
v_options_403_ = lean_ctor_get(v_toCold_401_, 2);
v___x_404_ = 0;
v_env_405_ = l_Lean_Environment_setRecordingDeps(v_env_402_, v___x_404_);
v___x_406_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5);
lean_inc_ref(v_options_403_);
v___x_408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_408_, 0, v_env_405_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_407_);
lean_ctor_set(v___x_408_, 3, v_options_403_);
v___x_409_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_msgData_396_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(v_msgData_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_ref_420_; lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_ref_420_ = lean_ctor_get(v___y_417_, 2);
v___x_421_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(v_msg_416_, v___y_417_, v___y_418_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_ref_420_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_ref_420_);
lean_ctor_set(v___x_426_, 1, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v_msg_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg(lean_object* v_ref_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_toCold_441_; lean_object* v_currRecDepth_442_; lean_object* v_ref_443_; uint16_t v_optionFlags_444_; uint8_t v_suppressElabErrors_445_; uint8_t v_checkDeprecated_446_; uint8_t v_isRecordingDeps_447_; lean_object* v_ref_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_toCold_441_ = lean_ctor_get(v___y_438_, 0);
v_currRecDepth_442_ = lean_ctor_get(v___y_438_, 1);
v_ref_443_ = lean_ctor_get(v___y_438_, 2);
v_optionFlags_444_ = lean_ctor_get_uint16(v___y_438_, sizeof(void*)*3);
v_suppressElabErrors_445_ = lean_ctor_get_uint8(v___y_438_, sizeof(void*)*3 + 2);
v_checkDeprecated_446_ = lean_ctor_get_uint8(v___y_438_, sizeof(void*)*3 + 3);
v_isRecordingDeps_447_ = lean_ctor_get_uint8(v___y_438_, sizeof(void*)*3 + 4);
v_ref_448_ = l_Lean_replaceRef(v_ref_436_, v_ref_443_);
lean_inc(v_currRecDepth_442_);
lean_inc_ref(v_toCold_441_);
v___x_449_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_449_, 0, v_toCold_441_);
lean_ctor_set(v___x_449_, 1, v_currRecDepth_442_);
lean_ctor_set(v___x_449_, 2, v_ref_448_);
lean_ctor_set_uint16(v___x_449_, sizeof(void*)*3, v_optionFlags_444_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*3 + 2, v_suppressElabErrors_445_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*3 + 3, v_checkDeprecated_446_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*3 + 4, v_isRecordingDeps_447_);
v___x_450_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v_msg_437_, v___x_449_, v___y_439_);
lean_dec_ref_known(v___x_449_, 3);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg___boxed(lean_object* v_ref_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg(v_ref_451_, v_msg_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_ref_451_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_478_, lean_object* v_declHint_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_env_484_; uint8_t v___x_485_; 
v___x_482_ = lean_box(0);
v___x_483_ = lean_st_ref_get(v___y_480_);
v_env_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_env_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Lean_Name_isAnonymous(v_declHint_479_);
if (v___x_485_ == 0)
{
uint8_t v_isExporting_486_; 
v_isExporting_486_ = lean_ctor_get_uint8(v_env_484_, sizeof(void*)*13);
if (v_isExporting_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_msg_478_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
lean_inc_ref(v_env_484_);
v___x_488_ = l_Lean_Environment_setExporting(v_env_484_, v___x_485_);
lean_inc(v_declHint_479_);
lean_inc_ref(v___x_488_);
v___x_489_ = l_Lean_Environment_contains(v___x_488_, v_declHint_479_, v_isExporting_486_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v___x_488_);
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_msg_478_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_c_496_; lean_object* v___x_497_; 
v___x_491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_492_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5);
v___x_493_ = l_Lean_Options_empty;
lean_inc_ref(v___x_488_);
v___x_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_494_, 0, v___x_488_);
lean_ctor_set(v___x_494_, 1, v___x_491_);
lean_ctor_set(v___x_494_, 2, v___x_492_);
lean_ctor_set(v___x_494_, 3, v___x_493_);
lean_inc(v_declHint_479_);
v___x_495_ = l_Lean_MessageData_ofConstName(v_declHint_479_, v___x_485_);
v_c_496_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_496_, 0, v___x_494_);
lean_ctor_set(v_c_496_, 1, v___x_495_);
v___x_497_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_488_, v_declHint_479_);
lean_dec_ref(v___x_488_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_c_496_);
v___x_500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_MessageData_note(v___x_501_);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v_msg_478_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_539_; 
v_val_505_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_539_ == 0)
{
v___x_507_ = v___x_497_;
v_isShared_508_ = v_isSharedCheck_539_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v___x_497_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_539_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v_moduleNames_510_; lean_object* v_mod_511_; uint8_t v___x_512_; 
v___x_509_ = l_Lean_Environment_header(v_env_484_);
lean_dec_ref(v_env_484_);
v_moduleNames_510_ = lean_ctor_get(v___x_509_, 4);
lean_inc_ref(v_moduleNames_510_);
lean_dec_ref(v___x_509_);
v_mod_511_ = lean_array_get(v___x_482_, v_moduleNames_510_, v_val_505_);
lean_dec(v_val_505_);
lean_dec_ref(v_moduleNames_510_);
v___x_512_ = l_Lean_isPrivateName(v_declHint_479_);
lean_dec(v_declHint_479_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_513_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_c_496_);
v___x_515_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_MessageData_ofName(v_mod_511_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_MessageData_note(v___x_520_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v_msg_478_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_522_);
v___x_524_ = v___x_507_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_c_496_);
v___x_528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_MessageData_ofName(v_mod_511_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_MessageData_note(v___x_533_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v_msg_478_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_535_);
v___x_537_ = v___x_507_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_msg_478_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_541_, lean_object* v_declHint_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg(v_msg_541_, v_declHint_542_, v___y_543_);
lean_dec(v___y_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14(lean_object* v_msg_546_, lean_object* v_declHint_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
v___x_551_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg(v_msg_546_, v_declHint_547_, v___y_549_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = l_Lean_unknownIdentifierMessageTag;
v___x_557_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14___boxed(lean_object* v_msg_562_, lean_object* v_declHint_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14(v_msg_562_, v_declHint_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_ref_568_, lean_object* v_msg_569_, lean_object* v_declHint_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_576_; 
v___x_574_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14(v_msg_569_, v_declHint_570_, v___y_571_, v___y_572_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg(v_ref_568_, v_a_575_, v___y_571_, v___y_572_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_ref_577_, lean_object* v_msg_578_, lean_object* v_declHint_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg(v_ref_577_, v_msg_578_, v_declHint_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_ref_577_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object* v_ref_590_, lean_object* v_constName_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1);
v___x_596_ = 0;
lean_inc(v_constName_591_);
v___x_597_ = l_Lean_MessageData_ofConstName(v_constName_591_, v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg(v_ref_590_, v___x_600_, v_constName_591_, v___y_592_, v___y_593_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_ref_602_, lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_602_, v_constName_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v_ref_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_constName_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_ref_612_; lean_object* v___x_613_; 
v_ref_612_ = lean_ctor_get(v___y_609_, 2);
v___x_613_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_612_, v_constName_608_, v___y_609_, v___y_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_constName_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(lean_object* v_constName_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v_env_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_st_ref_get(v___y_621_);
v_env_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_env_624_);
lean_dec(v___x_623_);
v___x_625_ = 0;
lean_inc(v_constName_619_);
v___x_626_ = l_Lean_Environment_find_x3f(v_env_624_, v_constName_619_, v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_619_, v___y_620_, v___y_621_);
return v___x_627_;
}
else
{
lean_object* v_val_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_constName_619_);
v_val_628_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_626_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_val_628_);
lean_dec(v___x_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 0);
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_val_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3___boxed(lean_object* v_constName_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(v_constName_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg(){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(lean_object* v___dummy_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg();
return v_res_646_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 1)
{
lean_object* v_pre_656_; 
v_pre_656_ = lean_ctor_get(v_x_655_, 0);
switch(lean_obj_tag(v_pre_656_))
{
case 1:
{
lean_object* v_pre_657_; 
v_pre_657_ = lean_ctor_get(v_pre_656_, 0);
switch(lean_obj_tag(v_pre_657_))
{
case 0:
{
lean_object* v_str_658_; lean_object* v_str_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_str_658_ = lean_ctor_get(v_x_655_, 1);
v_str_659_ = lean_ctor_get(v_pre_656_, 1);
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_661_ = lean_string_dec_eq(v_str_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0));
v___x_663_ = lean_string_dec_eq(v_str_659_, v___x_662_);
if (v___x_663_ == 0)
{
return v___x_663_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1));
v___x_665_ = lean_string_dec_eq(v_str_658_, v___x_664_);
if (v___x_665_ == 0)
{
return v___x_665_;
}
else
{
return v_suppressElabErrors_654_;
}
}
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2));
v___x_667_ = lean_string_dec_eq(v_str_658_, v___x_666_);
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
return v_suppressElabErrors_654_;
}
}
}
case 1:
{
lean_object* v_pre_668_; 
v_pre_668_ = lean_ctor_get(v_pre_657_, 0);
if (lean_obj_tag(v_pre_668_) == 0)
{
lean_object* v_str_669_; lean_object* v_str_670_; lean_object* v_str_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_str_669_ = lean_ctor_get(v_x_655_, 1);
v_str_670_ = lean_ctor_get(v_pre_656_, 1);
v_str_671_ = lean_ctor_get(v_pre_657_, 1);
v___x_672_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3));
v___x_673_ = lean_string_dec_eq(v_str_671_, v___x_672_);
if (v___x_673_ == 0)
{
return v___x_673_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4));
v___x_675_ = lean_string_dec_eq(v_str_670_, v___x_674_);
if (v___x_675_ == 0)
{
return v___x_675_;
}
else
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5));
v___x_677_ = lean_string_dec_eq(v_str_669_, v___x_676_);
if (v___x_677_ == 0)
{
return v___x_677_;
}
else
{
return v_suppressElabErrors_654_;
}
}
}
}
else
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
default: 
{
uint8_t v___x_679_; 
v___x_679_ = 0;
return v___x_679_;
}
}
}
case 0:
{
lean_object* v_str_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_str_680_ = lean_ctor_get(v_x_655_, 1);
v___x_681_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6));
v___x_682_ = lean_string_dec_eq(v_str_680_, v___x_681_);
if (v___x_682_ == 0)
{
return v___x_682_;
}
else
{
return v_suppressElabErrors_654_;
}
}
default: 
{
uint8_t v___x_683_; 
v___x_683_ = 0;
return v___x_683_;
}
}
}
else
{
uint8_t v___x_684_; 
v___x_684_ = 0;
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_685_, lean_object* v_x_686_){
_start:
{
uint8_t v_suppressElabErrors_boxed_687_; uint8_t v_res_688_; lean_object* v_r_689_; 
v_suppressElabErrors_boxed_687_ = lean_unbox(v_suppressElabErrors_685_);
v_res_688_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_687_, v_x_686_);
lean_dec(v_x_686_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__10(lean_object* v_opts_690_, lean_object* v_opt_691_){
_start:
{
lean_object* v_name_692_; lean_object* v_defValue_693_; lean_object* v_map_694_; lean_object* v___x_695_; 
v_name_692_ = lean_ctor_get(v_opt_691_, 0);
v_defValue_693_ = lean_ctor_get(v_opt_691_, 1);
v_map_694_ = lean_ctor_get(v_opts_690_, 0);
v___x_695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_694_, v_name_692_);
if (lean_obj_tag(v___x_695_) == 0)
{
uint8_t v___x_696_; 
v___x_696_ = lean_unbox(v_defValue_693_);
return v___x_696_;
}
else
{
lean_object* v_val_697_; 
v_val_697_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v___x_695_, 1);
if (lean_obj_tag(v_val_697_) == 1)
{
uint8_t v_v_698_; 
v_v_698_ = lean_ctor_get_uint8(v_val_697_, 0);
lean_dec_ref_known(v_val_697_, 0);
return v_v_698_;
}
else
{
uint8_t v___x_699_; 
lean_dec(v_val_697_);
v___x_699_ = lean_unbox(v_defValue_693_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__10___boxed(lean_object* v_opts_700_, lean_object* v_opt_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__10(v_opts_700_, v_opt_701_);
lean_dec_ref(v_opt_701_);
lean_dec_ref(v_opts_700_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_ref_705_, lean_object* v_msgData_706_, uint8_t v_severity_707_, uint8_t v_isSilent_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
uint8_t v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v_toCold_720_; lean_object* v___y_721_; lean_object* v___y_750_; lean_object* v___y_751_; uint8_t v___y_752_; uint8_t v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; uint8_t v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; uint8_t v___y_780_; uint8_t v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; uint8_t v___y_787_; uint8_t v___y_788_; uint8_t v___x_798_; uint8_t v___y_800_; uint8_t v___x_806_; 
v___x_798_ = 2;
v___x_806_ = l_Lean_instBEqMessageSeverity_beq(v_severity_707_, v___x_798_);
if (v___x_806_ == 0)
{
v___y_800_ = v___x_806_;
goto v___jp_799_;
}
else
{
uint8_t v___x_807_; 
lean_inc_ref(v_msgData_706_);
v___x_807_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_706_);
if (v___x_807_ == 0)
{
v___y_800_ = v___x_807_;
goto v___jp_799_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v_msgData_706_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
v___jp_712_:
{
lean_object* v_currNamespace_722_; lean_object* v_openDecls_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_env_728_; lean_object* v_nextMacroScope_729_; lean_object* v_ngen_730_; lean_object* v_auxDeclNGen_731_; lean_object* v_traceState_732_; lean_object* v_cache_733_; lean_object* v_recordedDeps_734_; lean_object* v_messages_735_; lean_object* v_infoState_736_; lean_object* v_snapshotTasks_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_currNamespace_722_ = lean_ctor_get(v_toCold_720_, 4);
v_openDecls_723_ = lean_ctor_get(v_toCold_720_, 5);
lean_inc(v_openDecls_723_);
lean_inc(v_currNamespace_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_currNamespace_722_);
lean_ctor_set(v___x_724_, 1, v_openDecls_723_);
v___x_725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___y_714_);
lean_inc_ref(v___y_717_);
lean_inc_ref(v___y_719_);
v___x_726_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_726_, 0, v___y_719_);
lean_ctor_set(v___x_726_, 1, v___y_718_);
lean_ctor_set(v___x_726_, 2, v___y_716_);
lean_ctor_set(v___x_726_, 3, v___y_717_);
lean_ctor_set(v___x_726_, 4, v___x_725_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5, v___y_715_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5 + 1, v___y_713_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5 + 2, v_isSilent_708_);
v___x_727_ = lean_st_ref_take(v___y_721_);
v_env_728_ = lean_ctor_get(v___x_727_, 0);
v_nextMacroScope_729_ = lean_ctor_get(v___x_727_, 1);
v_ngen_730_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_731_ = lean_ctor_get(v___x_727_, 3);
v_traceState_732_ = lean_ctor_get(v___x_727_, 4);
v_cache_733_ = lean_ctor_get(v___x_727_, 5);
v_recordedDeps_734_ = lean_ctor_get(v___x_727_, 6);
v_messages_735_ = lean_ctor_get(v___x_727_, 7);
v_infoState_736_ = lean_ctor_get(v___x_727_, 8);
v_snapshotTasks_737_ = lean_ctor_get(v___x_727_, 9);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v___x_727_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snapshotTasks_737_);
lean_inc(v_infoState_736_);
lean_inc(v_messages_735_);
lean_inc(v_recordedDeps_734_);
lean_inc(v_cache_733_);
lean_inc(v_traceState_732_);
lean_inc(v_auxDeclNGen_731_);
lean_inc(v_ngen_730_);
lean_inc(v_nextMacroScope_729_);
lean_inc(v_env_728_);
lean_dec(v___x_727_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_741_ = lean_box(0);
v___x_742_ = l_Lean_MessageLog_add(v___x_726_, v_messages_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 7, v___x_742_);
v___x_744_ = v___x_739_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_env_728_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_nextMacroScope_729_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_ngen_730_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_auxDeclNGen_731_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_traceState_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 5, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_747_, 6, v_recordedDeps_734_);
lean_ctor_set(v_reuseFailAlloc_747_, 7, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_747_, 8, v_infoState_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 9, v_snapshotTasks_737_);
v___x_744_ = v_reuseFailAlloc_747_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_st_ref_put(v___y_721_, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_741_);
return v___x_746_;
}
}
}
v___jp_749_:
{
lean_object* v_fileName_758_; lean_object* v_fileMap_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_775_; 
v_fileName_758_ = lean_ctor_get(v___y_756_, 0);
v_fileMap_759_ = lean_ctor_get(v___y_756_, 1);
v___x_760_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_706_);
v___x_761_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(v___x_760_, v___y_709_, v___y_710_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_775_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_inc_ref_n(v_fileMap_759_, 2);
v___x_766_ = l_Lean_FileMap_toPosition(v_fileMap_759_, v___y_755_);
lean_dec(v___y_755_);
v___x_767_ = l_Lean_FileMap_toPosition(v_fileMap_759_, v___y_757_);
lean_dec(v___y_757_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0));
if (v___y_752_ == 0)
{
lean_del_object(v___x_764_);
lean_dec_ref(v___y_751_);
v___y_713_ = v___y_753_;
v___y_714_ = v_a_762_;
v___y_715_ = v___y_754_;
v___y_716_ = v___x_768_;
v___y_717_ = v___x_769_;
v___y_718_ = v___x_766_;
v___y_719_ = v_fileName_758_;
v_toCold_720_ = v___y_750_;
v___y_721_ = v___y_710_;
goto v___jp_712_;
}
else
{
uint8_t v___x_770_; 
lean_inc(v_a_762_);
v___x_770_ = l_Lean_MessageData_hasTag(v___y_751_, v_a_762_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec_ref_known(v___x_768_, 1);
lean_dec_ref(v___x_766_);
lean_dec(v_a_762_);
v___x_771_ = lean_box(0);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_771_);
v___x_773_ = v___x_764_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_del_object(v___x_764_);
v___y_713_ = v___y_753_;
v___y_714_ = v_a_762_;
v___y_715_ = v___y_754_;
v___y_716_ = v___x_768_;
v___y_717_ = v___x_769_;
v___y_718_ = v___x_766_;
v___y_719_ = v_fileName_758_;
v_toCold_720_ = v___y_750_;
v___y_721_ = v___y_710_;
goto v___jp_712_;
}
}
}
}
v___jp_776_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Syntax_getTailPos_x3f(v___y_782_, v___y_781_);
lean_dec(v___y_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_inc(v___y_783_);
v___y_750_ = v___y_778_;
v___y_751_ = v___y_779_;
v___y_752_ = v___y_777_;
v___y_753_ = v___y_780_;
v___y_754_ = v___y_781_;
v___y_755_ = v___y_783_;
v___y_756_ = v___y_778_;
v___y_757_ = v___y_783_;
goto v___jp_749_;
}
else
{
lean_object* v_val_785_; 
v_val_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v___x_784_, 1);
v___y_750_ = v___y_778_;
v___y_751_ = v___y_779_;
v___y_752_ = v___y_777_;
v___y_753_ = v___y_780_;
v___y_754_ = v___y_781_;
v___y_755_ = v___y_783_;
v___y_756_ = v___y_778_;
v___y_757_ = v_val_785_;
goto v___jp_749_;
}
}
v___jp_786_:
{
lean_object* v_toCold_789_; lean_object* v_ref_790_; uint8_t v_suppressElabErrors_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v_ref_794_; lean_object* v___x_795_; 
v_toCold_789_ = lean_ctor_get(v___y_709_, 0);
v_ref_790_ = lean_ctor_get(v___y_709_, 2);
v_suppressElabErrors_791_ = lean_ctor_get_uint8(v___y_709_, sizeof(void*)*3 + 2);
v___x_792_ = lean_box(v_suppressElabErrors_791_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_793_, 0, v___x_792_);
v_ref_794_ = l_Lean_replaceRef(v_ref_705_, v_ref_790_);
v___x_795_ = l_Lean_Syntax_getPos_x3f(v_ref_794_, v___y_787_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___y_777_ = v_suppressElabErrors_791_;
v___y_778_ = v_toCold_789_;
v___y_779_ = v___f_793_;
v___y_780_ = v___y_788_;
v___y_781_ = v___y_787_;
v___y_782_ = v_ref_794_;
v___y_783_ = v___x_796_;
goto v___jp_776_;
}
else
{
lean_object* v_val_797_; 
v_val_797_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_795_, 1);
v___y_777_ = v_suppressElabErrors_791_;
v___y_778_ = v_toCold_789_;
v___y_779_ = v___f_793_;
v___y_780_ = v___y_788_;
v___y_781_ = v___y_787_;
v___y_782_ = v_ref_794_;
v___y_783_ = v_val_797_;
goto v___jp_776_;
}
}
v___jp_799_:
{
uint8_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = 1;
v___x_802_ = l_Lean_instBEqMessageSeverity_beq(v_severity_707_, v___x_801_);
if (v___x_802_ == 0)
{
v___y_787_ = v___y_800_;
v___y_788_ = v_severity_707_;
goto v___jp_786_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_709_);
v___x_804_ = l_Lean_warningAsError;
v___x_805_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__10(v___x_803_, v___x_804_);
lean_dec_ref(v___x_803_);
if (v___x_805_ == 0)
{
v___y_787_ = v___y_800_;
v___y_788_ = v_severity_707_;
goto v___jp_786_;
}
else
{
v___y_787_ = v___y_800_;
v___y_788_ = v___x_798_;
goto v___jp_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___boxed(lean_object* v_ref_810_, lean_object* v_msgData_811_, lean_object* v_severity_812_, lean_object* v_isSilent_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_severity_boxed_817_; uint8_t v_isSilent_boxed_818_; lean_object* v_res_819_; 
v_severity_boxed_817_ = lean_unbox(v_severity_812_);
v_isSilent_boxed_818_ = lean_unbox(v_isSilent_813_);
v_res_819_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(v_ref_810_, v_msgData_811_, v_severity_boxed_817_, v_isSilent_boxed_818_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v_ref_810_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_msgData_820_, uint8_t v_severity_821_, uint8_t v_isSilent_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_ref_826_; lean_object* v___x_827_; 
v_ref_826_ = lean_ctor_get(v___y_823_, 2);
v___x_827_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(v_ref_826_, v_msgData_820_, v_severity_821_, v_isSilent_822_, v___y_823_, v___y_824_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_msgData_828_, lean_object* v_severity_829_, lean_object* v_isSilent_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v_severity_boxed_834_; uint8_t v_isSilent_boxed_835_; lean_object* v_res_836_; 
v_severity_boxed_834_ = lean_unbox(v_severity_829_);
v_isSilent_boxed_835_ = lean_unbox(v_isSilent_830_);
v_res_836_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(v_msgData_828_, v_severity_boxed_834_, v_isSilent_boxed_835_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(lean_object* v_msgData_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v___x_841_ = 1;
v___x_842_ = 0;
v___x_843_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(v_msgData_837_, v___x_841_, v___x_842_, v___y_838_, v___y_839_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2___boxed(lean_object* v_msgData_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(v_msgData_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_848_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6(lean_object* v_oldArg_849_, lean_object* v_as_850_, size_t v_i_851_, size_t v_stop_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_eq(v_i_851_, v_stop_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_array_uget_borrowed(v_as_850_, v_i_851_);
v___x_855_ = lean_name_eq(v___x_854_, v_oldArg_849_);
if (v___x_855_ == 0)
{
size_t v___x_856_; size_t v___x_857_; 
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_add(v_i_851_, v___x_856_);
v_i_851_ = v___x_857_;
goto _start;
}
else
{
return v___x_855_;
}
}
else
{
uint8_t v___x_859_; 
v___x_859_ = 0;
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6___boxed(lean_object* v_oldArg_860_, lean_object* v_as_861_, lean_object* v_i_862_, lean_object* v_stop_863_){
_start:
{
size_t v_i_boxed_864_; size_t v_stop_boxed_865_; uint8_t v_res_866_; lean_object* v_r_867_; 
v_i_boxed_864_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_stop_boxed_865_ = lean_unbox_usize(v_stop_863_);
lean_dec(v_stop_863_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6(v_oldArg_860_, v_as_861_, v_i_boxed_864_, v_stop_boxed_865_);
lean_dec_ref(v_as_861_);
lean_dec(v_oldArg_860_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7___redArg();
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_891_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_892_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_890_);
lean_ctor_set(v___x_892_, 2, v___x_890_);
lean_ctor_set(v___x_892_, 3, v___x_890_);
lean_ctor_set(v___x_892_, 4, v___x_890_);
lean_ctor_set(v___x_892_, 5, v___x_890_);
lean_ctor_set(v___x_892_, 6, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
lean_ctor_set(v___x_894_, 2, v___x_893_);
lean_ctor_set(v___x_894_, 3, v___x_893_);
lean_ctor_set(v___x_894_, 4, v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___f_906_, lean_object* v___x_907_, lean_object* v_declName_908_, lean_object* v_stx_909_, uint8_t v___kind_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v_nextMacroScope_917_; lean_object* v_ngen_918_; lean_object* v_auxDeclNGen_919_; lean_object* v_traceState_920_; lean_object* v_recordedDeps_921_; lean_object* v_messages_922_; lean_object* v_infoState_923_; lean_object* v_snapshotTasks_924_; lean_object* v___y_925_; lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; 
v___x_930_ = l_Lean_Name_mkStr2(v___x_901_, v___x_902_);
lean_inc(v_stx_909_);
v___x_931_ = l_Lean_Syntax_isOfKind(v_stx_909_, v___x_930_);
lean_dec(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v_stx_909_);
lean_dec(v_declName_908_);
lean_dec_ref(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___x_1136_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1137_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1136_, v___y_911_, v___y_912_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v_oldId_1139_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_since_x3f_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v_text_x3f_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v_newId_x3f_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v_oldId_1139_ = l_Lean_Syntax_getArg(v_stx_909_, v___x_1138_);
v___x_1186_ = l_Lean_Syntax_getArg(v_stx_909_, v___x_907_);
v___x_1187_ = l_Lean_Syntax_isNone(v___x_1186_);
if (v___x_1187_ == 0)
{
uint8_t v___x_1188_; 
lean_inc(v___x_1186_);
v___x_1188_ = l_Lean_Syntax_matchesNull(v___x_1186_, v___x_1138_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v___x_1186_);
lean_dec(v_oldId_1139_);
lean_dec(v_stx_909_);
lean_dec(v_declName_908_);
lean_dec_ref(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___x_1189_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1190_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1189_, v___y_911_, v___y_912_);
return v___x_1190_;
}
else
{
lean_object* v_newId_x3f_1191_; lean_object* v___x_1192_; 
v_newId_x3f_1191_ = l_Lean_Syntax_getArg(v___x_1186_, v___x_904_);
lean_dec(v___x_1186_);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_newId_x3f_1191_);
v_newId_x3f_1174_ = v___x_1192_;
v___y_1175_ = v___y_911_;
v___y_1176_ = v___y_912_;
goto v___jp_1173_;
}
}
else
{
lean_object* v___x_1193_; 
lean_dec(v___x_1186_);
v___x_1193_ = lean_box(0);
v_newId_x3f_1174_ = v___x_1193_;
v___y_1175_ = v___y_911_;
v___y_1176_ = v___y_912_;
goto v___jp_1173_;
}
v___jp_1140_:
{
lean_object* v_oldArg_1146_; 
v_oldArg_1146_ = l_Lean_TSyntax_getId(v_oldId_1139_);
lean_dec(v_oldId_1139_);
if (lean_obj_tag(v___y_1142_) == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_box(0);
v___y_1117_ = v___y_1144_;
v___y_1118_ = v___y_1141_;
v___y_1119_ = v_since_x3f_1143_;
v___y_1120_ = v_oldArg_1146_;
v___y_1121_ = v___y_1145_;
v___y_1122_ = v___x_1147_;
goto v___jp_1116_;
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_val_1148_ = lean_ctor_get(v___y_1142_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___y_1142_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v___y_1142_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_val_1148_);
lean_dec(v___y_1142_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Lean_TSyntax_getId(v_val_1148_);
lean_dec(v_val_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
v___y_1117_ = v___y_1144_;
v___y_1118_ = v___y_1141_;
v___y_1119_ = v_since_x3f_1143_;
v___y_1120_ = v_oldArg_1146_;
v___y_1121_ = v___y_1145_;
v___y_1122_ = v___x_1154_;
goto v___jp_1116_;
}
}
}
}
v___jp_1157_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(4u);
v___x_1164_ = l_Lean_Syntax_getArg(v_stx_909_, v___x_1163_);
v___x_1165_ = l_Lean_Syntax_isNone(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1164_);
v___x_1167_ = l_Lean_Syntax_matchesNull(v___x_1164_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v___x_1164_);
lean_dec(v_text_x3f_1160_);
lean_dec(v___y_1159_);
lean_dec(v_oldId_1139_);
lean_dec(v_stx_909_);
lean_dec(v_declName_908_);
lean_dec_ref(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___x_1168_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1169_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1168_, v___y_1161_, v___y_1162_);
return v___x_1169_;
}
else
{
lean_object* v_since_x3f_1170_; lean_object* v___x_1171_; 
v_since_x3f_1170_ = l_Lean_Syntax_getArg(v___x_1164_, v___y_1158_);
lean_dec(v___x_1164_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_since_x3f_1170_);
v___y_1141_ = v_text_x3f_1160_;
v___y_1142_ = v___y_1159_;
v_since_x3f_1143_ = v___x_1171_;
v___y_1144_ = v___y_1161_;
v___y_1145_ = v___y_1162_;
goto v___jp_1140_;
}
}
else
{
lean_object* v___x_1172_; 
lean_dec(v___x_1164_);
v___x_1172_ = lean_box(0);
v___y_1141_ = v_text_x3f_1160_;
v___y_1142_ = v___y_1159_;
v_since_x3f_1143_ = v___x_1172_;
v___y_1144_ = v___y_1161_;
v___y_1145_ = v___y_1162_;
goto v___jp_1140_;
}
}
v___jp_1173_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(3u);
v___x_1178_ = l_Lean_Syntax_getArg(v_stx_909_, v___x_1177_);
v___x_1179_ = l_Lean_Syntax_isNone(v___x_1178_);
if (v___x_1179_ == 0)
{
uint8_t v___x_1180_; 
lean_inc(v___x_1178_);
v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1138_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___x_1178_);
lean_dec(v_newId_x3f_1174_);
lean_dec(v_oldId_1139_);
lean_dec(v_stx_909_);
lean_dec(v_declName_908_);
lean_dec_ref(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1182_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1181_, v___y_1175_, v___y_1176_);
return v___x_1182_;
}
else
{
lean_object* v_text_x3f_1183_; lean_object* v___x_1184_; 
v_text_x3f_1183_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_904_);
lean_dec(v___x_1178_);
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_text_x3f_1183_);
v___y_1158_ = v___x_1177_;
v___y_1159_ = v_newId_x3f_1174_;
v_text_x3f_1160_ = v___x_1184_;
v___y_1161_ = v___y_1175_;
v___y_1162_ = v___y_1176_;
goto v___jp_1157_;
}
}
else
{
lean_object* v___x_1185_; 
lean_dec(v___x_1178_);
v___x_1185_ = lean_box(0);
v___y_1158_ = v___x_1177_;
v___y_1159_ = v_newId_x3f_1174_;
v_text_x3f_1160_ = v___x_1185_;
v___y_1161_ = v___y_1175_;
v___y_1162_ = v___y_1176_;
goto v___jp_1157_;
}
}
}
v___jp_914_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_927_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_927_, 0, v___y_925_);
lean_ctor_set(v___x_927_, 1, v_nextMacroScope_917_);
lean_ctor_set(v___x_927_, 2, v_ngen_918_);
lean_ctor_set(v___x_927_, 3, v_auxDeclNGen_919_);
lean_ctor_set(v___x_927_, 4, v_traceState_920_);
lean_ctor_set(v___x_927_, 5, v___x_926_);
lean_ctor_set(v___x_927_, 6, v_recordedDeps_921_);
lean_ctor_set(v___x_927_, 7, v_messages_922_);
lean_ctor_set(v___x_927_, 8, v_infoState_923_);
lean_ctor_set(v___x_927_, 9, v_snapshotTasks_924_);
v___x_928_ = lean_st_ref_put(v___y_915_, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___y_916_);
return v___x_929_;
}
v___jp_932_:
{
lean_object* v___x_938_; lean_object* v_env_939_; lean_object* v_nextMacroScope_940_; lean_object* v_ngen_941_; lean_object* v_auxDeclNGen_942_; lean_object* v_traceState_943_; lean_object* v_recordedDeps_944_; lean_object* v_messages_945_; lean_object* v_infoState_946_; lean_object* v_snapshotTasks_947_; lean_object* v___x_948_; lean_object* v_toEnvExtension_949_; lean_object* v_addEntryFn_950_; lean_object* v_asyncMode_951_; uint8_t v_logWrites_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___f_955_; 
v___x_938_ = lean_st_ref_take(v___y_937_);
v_env_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc_ref(v_env_939_);
v_nextMacroScope_940_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_nextMacroScope_940_);
v_ngen_941_ = lean_ctor_get(v___x_938_, 2);
lean_inc_ref(v_ngen_941_);
v_auxDeclNGen_942_ = lean_ctor_get(v___x_938_, 3);
lean_inc_ref(v_auxDeclNGen_942_);
v_traceState_943_ = lean_ctor_get(v___x_938_, 4);
lean_inc_ref(v_traceState_943_);
v_recordedDeps_944_ = lean_ctor_get(v___x_938_, 6);
lean_inc_ref(v_recordedDeps_944_);
v_messages_945_ = lean_ctor_get(v___x_938_, 7);
lean_inc_ref(v_messages_945_);
v_infoState_946_ = lean_ctor_get(v___x_938_, 8);
lean_inc_ref(v_infoState_946_);
v_snapshotTasks_947_ = lean_ctor_get(v___x_938_, 9);
lean_inc_ref(v_snapshotTasks_947_);
lean_dec(v___x_938_);
v___x_948_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_949_ = lean_ctor_get(v___x_948_, 0);
v_addEntryFn_950_ = lean_ctor_get(v___x_948_, 3);
v_asyncMode_951_ = lean_ctor_get(v_toEnvExtension_949_, 2);
v_logWrites_952_ = lean_ctor_get_uint8(v_toEnvExtension_949_, sizeof(void*)*6);
v___x_953_ = lean_box(0);
v___x_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_954_, 0, v_declName_908_);
lean_ctor_set(v___x_954_, 1, v___y_935_);
lean_ctor_set(v___x_954_, 2, v___y_933_);
lean_ctor_set(v___x_954_, 3, v___y_934_);
lean_ctor_set(v___x_954_, 4, v___y_936_);
lean_inc(v_addEntryFn_950_);
v___f_955_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_955_, 0, v_addEntryFn_950_);
lean_closure_set(v___f_955_, 1, v___x_954_);
if (v_logWrites_952_ == 0)
{
lean_object* v___x_956_; 
lean_inc_ref(v_toEnvExtension_949_);
v___x_956_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_949_, v_env_939_, v___f_955_, v_asyncMode_951_, v___x_903_, v___x_931_);
v___y_915_ = v___y_937_;
v___y_916_ = v___x_953_;
v_nextMacroScope_917_ = v_nextMacroScope_940_;
v_ngen_918_ = v_ngen_941_;
v_auxDeclNGen_919_ = v_auxDeclNGen_942_;
v_traceState_920_ = v_traceState_943_;
v_recordedDeps_921_ = v_recordedDeps_944_;
v_messages_922_ = v_messages_945_;
v_infoState_923_ = v_infoState_946_;
v_snapshotTasks_924_ = v_snapshotTasks_947_;
v___y_925_ = v___x_956_;
goto v___jp_914_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc_ref_n(v_toEnvExtension_949_, 2);
v___x_957_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_949_, v_env_939_);
lean_dec_ref(v_env_939_);
v___x_958_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_949_, v___x_957_, v___f_955_, v_asyncMode_951_, v___x_903_, v___x_931_);
v___y_915_ = v___y_937_;
v___y_916_ = v___x_953_;
v_nextMacroScope_917_ = v_nextMacroScope_940_;
v_ngen_918_ = v_ngen_941_;
v_auxDeclNGen_919_ = v_auxDeclNGen_942_;
v_traceState_920_ = v_traceState_943_;
v_recordedDeps_921_ = v_recordedDeps_944_;
v_messages_922_ = v_messages_945_;
v_infoState_923_ = v_infoState_946_;
v_snapshotTasks_924_ = v_snapshotTasks_947_;
v___y_925_ = v___x_958_;
goto v___jp_914_;
}
}
v___jp_959_:
{
if (lean_obj_tag(v___y_963_) == 0)
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Linter_mkSinceHint(v_stx_909_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_a_967_);
v___x_970_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(v___x_969_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_dec_ref_known(v___x_970_, 1);
v___y_933_ = v___y_960_;
v___y_934_ = v___y_961_;
v___y_935_ = v___y_962_;
v___y_936_ = v___y_963_;
v___y_937_ = v___y_965_;
goto v___jp_932_;
}
else
{
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v_declName_908_);
lean_dec(v___x_903_);
return v___x_970_;
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v_declName_908_);
lean_dec(v___x_903_);
v_a_971_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_966_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_966_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_dec(v_stx_909_);
v___y_933_ = v___y_960_;
v___y_934_ = v___y_961_;
v___y_935_ = v___y_962_;
v___y_936_ = v___y_963_;
v___y_937_ = v___y_965_;
goto v___jp_932_;
}
}
v___jp_979_:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_array_get_size(v___y_983_);
v___x_989_ = lean_nat_dec_lt(v___x_904_, v___x_988_);
lean_dec(v___x_904_);
if (v___x_989_ == 0)
{
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
v___y_960_ = v___y_980_;
v___y_961_ = v___y_981_;
v___y_962_ = v___y_982_;
v___y_963_ = v___y_985_;
v___y_964_ = v___y_986_;
v___y_965_ = v___y_987_;
goto v___jp_959_;
}
else
{
if (v___x_989_ == 0)
{
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
v___y_960_ = v___y_980_;
v___y_961_ = v___y_981_;
v___y_962_ = v___y_982_;
v___y_963_ = v___y_985_;
v___y_964_ = v___y_986_;
v___y_965_ = v___y_987_;
goto v___jp_959_;
}
else
{
size_t v___x_990_; size_t v___x_991_; uint8_t v___x_992_; 
v___x_990_ = ((size_t)0ULL);
v___x_991_ = lean_usize_of_nat(v___x_988_);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6(v___y_982_, v___y_983_, v___x_990_, v___x_991_);
lean_dec_ref(v___y_983_);
if (v___x_992_ == 0)
{
lean_dec(v___y_984_);
v___y_960_ = v___y_980_;
v___y_961_ = v___y_981_;
v___y_962_ = v___y_982_;
v___y_963_ = v___y_985_;
v___y_964_ = v___y_986_;
v___y_965_ = v___y_987_;
goto v___jp_959_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec(v___y_985_);
lean_dec(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v_stx_909_);
lean_dec(v___x_903_);
v___x_993_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_994_ = l_Lean_MessageData_ofName(v___y_982_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_MessageData_ofName(v_declName_908_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_MessageData_ofName(v___y_984_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1005_, v___y_986_, v___y_987_);
return v___x_1006_;
}
}
}
}
v___jp_1007_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v___y_1014_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec(v___y_1008_);
v___x_1016_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_1017_ = l_Lean_MessageData_ofName(v___y_1013_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_MessageData_ofName(v_declName_908_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1016_);
v___x_1024_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1023_, v___y_1009_, v___y_1015_);
return v___x_1024_;
}
v___jp_1025_:
{
lean_object* v___x_1032_; 
lean_inc(v_declName_908_);
v___x_1032_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(v_declName_908_, v___y_1026_, v___y_1030_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; uint64_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = l_Lean_ConstantInfo_type(v_a_1033_);
lean_dec(v_a_1033_);
v___x_1035_ = 0;
v___x_1036_ = 1;
v___x_1037_ = 0;
v___x_1038_ = 2;
v___x_1039_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1039_, 0, v___x_1035_);
lean_ctor_set_uint8(v___x_1039_, 1, v___x_1035_);
lean_ctor_set_uint8(v___x_1039_, 2, v___x_1035_);
lean_ctor_set_uint8(v___x_1039_, 3, v___x_1035_);
lean_ctor_set_uint8(v___x_1039_, 4, v___x_1035_);
lean_ctor_set_uint8(v___x_1039_, 5, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 6, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 7, v___x_1035_);
lean_ctor_set_uint8(v___x_1039_, 8, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 9, v___x_1036_);
lean_ctor_set_uint8(v___x_1039_, 10, v___x_1037_);
lean_ctor_set_uint8(v___x_1039_, 11, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 12, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 13, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 14, v___x_1038_);
lean_ctor_set_uint8(v___x_1039_, 15, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 16, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 17, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 18, v___x_931_);
lean_ctor_set_uint8(v___x_1039_, 19, v___x_1035_);
v___x_1040_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set_uint64(v___x_1041_, sizeof(void*)*1, v___x_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1043_ = lean_unsigned_to_nat(32u);
v___x_1044_ = lean_mk_empty_array_with_capacity(v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_1046_ = ((size_t)5ULL);
lean_inc_n(v___x_904_, 7);
v___x_1047_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1044_);
lean_ctor_set(v___x_1047_, 2, v___x_904_);
lean_ctor_set(v___x_1047_, 3, v___x_904_);
lean_ctor_set_usize(v___x_1047_, 4, v___x_1046_);
v___x_1048_ = lean_box(1);
lean_inc_ref(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1042_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_904_);
v___x_1051_ = lean_box(0);
lean_inc(v___x_905_);
v___x_1052_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1052_, 0, v___x_1041_);
lean_ctor_set(v___x_1052_, 1, v___x_905_);
lean_ctor_set(v___x_1052_, 2, v___x_1049_);
lean_ctor_set(v___x_1052_, 3, v___x_1050_);
lean_ctor_set(v___x_1052_, 4, v___x_1051_);
lean_ctor_set(v___x_1052_, 5, v___x_904_);
lean_ctor_set(v___x_1052_, 6, v___x_1051_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7, v___x_1035_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7 + 1, v___x_1035_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7 + 2, v___x_1035_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7 + 3, v___x_931_);
v___x_1053_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1054_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1054_, 0, v___x_904_);
lean_ctor_set(v___x_1054_, 1, v___x_904_);
lean_ctor_set(v___x_1054_, 2, v___x_904_);
lean_ctor_set(v___x_1054_, 3, v___x_904_);
lean_ctor_set(v___x_1054_, 4, v___x_1042_);
lean_ctor_set(v___x_1054_, 5, v___x_1042_);
lean_ctor_set(v___x_1054_, 6, v___x_1042_);
lean_ctor_set(v___x_1054_, 7, v___x_1042_);
lean_ctor_set(v___x_1054_, 8, v___x_1042_);
lean_ctor_set(v___x_1054_, 9, v___x_1042_);
lean_ctor_set(v___x_1054_, 10, v___x_1042_);
lean_ctor_set(v___x_1054_, 11, v___x_1053_);
v___x_1055_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1056_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
lean_ctor_set(v___x_1057_, 2, v___x_905_);
lean_ctor_set(v___x_1057_, 3, v___x_1047_);
lean_ctor_set(v___x_1057_, 4, v___x_1056_);
v___x_1058_ = lean_st_mk_ref(v___x_1057_);
v___x_1059_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___redArg(v___x_1034_, v___f_906_, v___x_1035_, v___x_1035_, v___x_1052_, v___x_1058_, v___y_1026_, v___y_1030_);
lean_dec_ref_known(v___x_1052_, 7);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_st_ref_get(v___x_1058_);
lean_dec(v___x_1058_);
lean_dec(v___x_1061_);
if (lean_obj_tag(v___y_1027_) == 1)
{
lean_object* v_val_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_val_1062_ = lean_ctor_get(v___y_1027_, 0);
lean_inc(v_val_1062_);
v___x_1063_ = lean_array_get_size(v_a_1060_);
v___x_1064_ = lean_nat_dec_lt(v___x_904_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_dec(v_stx_909_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___y_1008_ = v___y_1027_;
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1028_;
v___y_1011_ = v_a_1060_;
v___y_1012_ = v___y_1029_;
v___y_1013_ = v_val_1062_;
v___y_1014_ = v___y_1031_;
v___y_1015_ = v___y_1030_;
goto v___jp_1007_;
}
else
{
if (v___x_1064_ == 0)
{
lean_dec(v_stx_909_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___y_1008_ = v___y_1027_;
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1028_;
v___y_1011_ = v_a_1060_;
v___y_1012_ = v___y_1029_;
v___y_1013_ = v_val_1062_;
v___y_1014_ = v___y_1031_;
v___y_1015_ = v___y_1030_;
goto v___jp_1007_;
}
else
{
size_t v___x_1065_; size_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1063_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6(v_val_1062_, v_a_1060_, v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec(v_stx_909_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v___y_1008_ = v___y_1027_;
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1028_;
v___y_1011_ = v_a_1060_;
v___y_1012_ = v___y_1029_;
v___y_1013_ = v_val_1062_;
v___y_1014_ = v___y_1031_;
v___y_1015_ = v___y_1030_;
goto v___jp_1007_;
}
else
{
v___y_980_ = v___y_1027_;
v___y_981_ = v___y_1028_;
v___y_982_ = v___y_1029_;
v___y_983_ = v_a_1060_;
v___y_984_ = v_val_1062_;
v___y_985_ = v___y_1031_;
v___y_986_ = v___y_1026_;
v___y_987_ = v___y_1030_;
goto v___jp_979_;
}
}
}
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_array_get_size(v_a_1060_);
v___x_1069_ = lean_nat_dec_lt(v___x_904_, v___x_1068_);
lean_dec(v___x_904_);
if (v___x_1069_ == 0)
{
lean_dec(v_a_1060_);
v___y_960_ = v___y_1027_;
v___y_961_ = v___y_1028_;
v___y_962_ = v___y_1029_;
v___y_963_ = v___y_1031_;
v___y_964_ = v___y_1026_;
v___y_965_ = v___y_1030_;
goto v___jp_959_;
}
else
{
if (v___x_1069_ == 0)
{
lean_dec(v_a_1060_);
v___y_960_ = v___y_1027_;
v___y_961_ = v___y_1028_;
v___y_962_ = v___y_1029_;
v___y_963_ = v___y_1031_;
v___y_964_ = v___y_1026_;
v___y_965_ = v___y_1030_;
goto v___jp_959_;
}
else
{
size_t v___x_1070_; size_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = lean_usize_of_nat(v___x_1068_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__6(v___y_1029_, v_a_1060_, v___x_1070_, v___x_1071_);
lean_dec(v_a_1060_);
if (v___x_1072_ == 0)
{
v___y_960_ = v___y_1027_;
v___y_961_ = v___y_1028_;
v___y_962_ = v___y_1029_;
v___y_963_ = v___y_1031_;
v___y_964_ = v___y_1026_;
v___y_965_ = v___y_1030_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v___y_1031_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec(v_stx_909_);
lean_dec(v___x_903_);
v___x_1073_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_1074_ = l_Lean_MessageData_ofName(v___y_1029_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_MessageData_ofName(v_declName_908_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1081_, v___y_1026_, v___y_1030_);
return v___x_1082_;
}
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v___x_1058_);
lean_dec(v___y_1031_);
lean_dec(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec(v_stx_909_);
lean_dec(v_declName_908_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v_a_1083_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1059_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1059_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v___y_1031_);
lean_dec(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec(v_stx_909_);
lean_dec(v_declName_908_);
lean_dec_ref(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
v_a_1091_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1032_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1032_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
v___jp_1099_:
{
if (lean_obj_tag(v___y_1102_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_box(0);
v___y_1026_ = v___y_1101_;
v___y_1027_ = v___y_1100_;
v___y_1028_ = v___y_1105_;
v___y_1029_ = v___y_1103_;
v___y_1030_ = v___y_1104_;
v___y_1031_ = v___x_1106_;
goto v___jp_1025_;
}
else
{
lean_object* v_val_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1115_; 
v_val_1107_ = lean_ctor_get(v___y_1102_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___y_1102_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1109_ = v___y_1102_;
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_val_1107_);
lean_dec(v___y_1102_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = l_Lean_TSyntax_getString(v_val_1107_);
lean_dec(v_val_1107_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1026_ = v___y_1101_;
v___y_1027_ = v___y_1100_;
v___y_1028_ = v___y_1105_;
v___y_1029_ = v___y_1103_;
v___y_1030_ = v___y_1104_;
v___y_1031_ = v___x_1113_;
goto v___jp_1025_;
}
}
}
}
v___jp_1116_:
{
if (lean_obj_tag(v___y_1118_) == 0)
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_box(0);
v___y_1100_ = v___y_1122_;
v___y_1101_ = v___y_1117_;
v___y_1102_ = v___y_1119_;
v___y_1103_ = v___y_1120_;
v___y_1104_ = v___y_1121_;
v___y_1105_ = v___x_1123_;
goto v___jp_1099_;
}
else
{
lean_object* v_val_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1135_; 
v_val_1124_ = lean_ctor_get(v___y_1118_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___y_1118_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1126_ = v___y_1118_;
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_val_1124_);
lean_dec(v___y_1118_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = l_Lean_TSyntax_getString(v_val_1124_);
lean_dec(v_val_1124_);
v___x_1129_ = lean_string_utf8_byte_size(v___x_1128_);
v___x_1130_ = lean_nat_dec_eq(v___x_1129_, v___x_904_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1132_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1128_);
v___x_1132_ = v___x_1126_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1128_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v___y_1100_ = v___y_1122_;
v___y_1101_ = v___y_1117_;
v___y_1102_ = v___y_1119_;
v___y_1103_ = v___y_1120_;
v___y_1104_ = v___y_1121_;
v___y_1105_ = v___x_1132_;
goto v___jp_1099_;
}
}
else
{
lean_object* v___x_1134_; 
lean_dec_ref(v___x_1128_);
lean_del_object(v___x_1126_);
v___x_1134_ = lean_box(0);
v___y_1100_ = v___y_1122_;
v___y_1101_ = v___y_1117_;
v___y_1102_ = v___y_1119_;
v___y_1103_ = v___y_1120_;
v___y_1104_ = v___y_1121_;
v___y_1105_ = v___x_1134_;
goto v___jp_1099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___f_1199_, lean_object* v___x_1200_, lean_object* v_declName_1201_, lean_object* v_stx_1202_, lean_object* v___kind_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v___kind_boxed_1207_; lean_object* v_res_1208_; 
v___kind_boxed_1207_ = lean_unbox(v___kind_1203_);
v_res_1208_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(v___x_1194_, v___x_1195_, v___x_1196_, v___x_1197_, v___x_1198_, v___f_1199_, v___x_1200_, v_declName_1201_, v_stx_1202_, v___kind_boxed_1207_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___x_1200_);
return v_res_1208_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1214_ = l_Lean_stringToMessageData(v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v___x_1215_, lean_object* v_decl_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1220_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1221_ = l_Lean_MessageData_ofName(v___x_1215_);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1224_, v___y_1217_, v___y_1218_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v___x_1226_, lean_object* v_decl_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(v___x_1226_, v_decl_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v_decl_1227_);
return v_res_1231_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_unsigned_to_nat(3307094584u);
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1275_ = l_Lean_Name_num___override(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1278_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1279_ = l_Lean_Name_str___override(v___x_1278_, v___x_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1282_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1283_ = l_Lean_Name_str___override(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(2u);
v___x_1285_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1286_ = l_Lean_Name_num___override(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1301_ = 0;
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1303_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1304_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1305_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1302_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*3, v___x_1301_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___f_1306_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___f_1307_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1308_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___f_1307_);
lean_ctor_set(v___x_1309_, 2, v___f_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1312_ = l_Lean_registerBuiltinAttribute(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_();
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0(size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_bs_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(v_sz_1315_, v_i_1316_, v_bs_1317_, v___y_1318_, v___y_1320_, v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___boxed(lean_object* v_sz_1324_, lean_object* v_i_1325_, lean_object* v_bs_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1324_);
lean_dec(v_sz_1324_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0(v_sz_boxed_1332_, v_i_boxed_1333_, v_bs_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v_msg_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1(v_00_u03b1_1341_, v_msg_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4_spec__7(lean_object* v_00_u03b2_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg(){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v___dummy_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg();
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b1_1355_, lean_object* v_constName_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_1356_, v___y_1357_, v___y_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b1_1361_, lean_object* v_constName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b1_1361_, v_constName_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1367_, lean_object* v_ref_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_1368_, v_constName_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_ref_1375_, lean_object* v_constName_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b1_1374_, v_ref_1375_, v_constName_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v_ref_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13(lean_object* v_00_u03b1_1381_, lean_object* v_ref_1382_, lean_object* v_msg_1383_, lean_object* v_declHint_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___redArg(v_ref_1382_, v_msg_1383_, v_declHint_1384_, v___y_1385_, v___y_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b1_1389_, lean_object* v_ref_1390_, lean_object* v_msg_1391_, lean_object* v_declHint_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13(v_00_u03b1_1389_, v_ref_1390_, v_msg_1391_, v_declHint_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v_ref_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15(lean_object* v_msg_1397_, lean_object* v_declHint_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___redArg(v_msg_1397_, v_declHint_1398_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_1403_, lean_object* v_declHint_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__14_spec__15(v_msg_1403_, v_declHint_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15(lean_object* v_00_u03b1_1409_, lean_object* v_ref_1410_, lean_object* v_msg_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___redArg(v_ref_1410_, v_msg_1411_, v___y_1412_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ref_1417_, lean_object* v_msg_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__13_spec__15(v_00_u03b1_1416_, v_ref_1417_, v_msg_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v_ref_1417_);
return v_res_1422_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_linter_deprecated_arg = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_linter_deprecated_arg);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_deprecatedArgExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_deprecatedArgExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeprecatedArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeprecatedArg(builtin);
}
#ifdef __cplusplus
}
#endif
