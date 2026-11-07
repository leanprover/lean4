// Lean compiler output
// Module: Lean.Compiler.LCNF.Visibility
// Imports: public import Lean.Compiler.ImplementedByAttr import Lean.ExtraModUses import Lean.Compiler.Options import Lean.Compiler.LCNF.PhaseExt public import Lean.Compiler.LCNF.PassManager
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21(uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_getIRPhases(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
extern lean_object* l_Lean_Compiler_LCNF_baseExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclTransparent(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqConstantKind_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_compiler_small;
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isDeclTransparent(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_checkMeta;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferVisibility"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 148, 126, 193, 57, 193, 124, 170)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Marking "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = " as transparent because it is opaque and its body looks relevant"};
static const lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = " as opaque because it is used by transparent "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Invalid definition `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`, may not access declaration `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` marked as `meta`"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` imported as `meta`; consider adding `import "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Invalid `meta` definition `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "`, `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is not accessible here; consider adding `public meta import "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` not marked `meta`"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Invalid public `meta` definition `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "` is not accessible here; consider adding `public import "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Cannot compile inline/specializing declaration `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "` as it uses `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "` of module `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "` which must be imported publicly. This limitation may be lifted in the future."};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "checkTemplateVisibility"};
static const lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 236, 106, 96, 57, 116, 191, 210)}};
static const lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility = (const lean_object*)&l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = " as opaque because it is a public def"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_inferVisibility___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 35, 224, 65, 124, 253, 116, 42)}};
static const lean_object* l_Lean_Compiler_LCNF_inferVisibility___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_inferVisibility___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Visibility"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 82, 52, 247, 236, 142, 37, 109)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(150, 51, 180, 137, 17, 237, 191, 3)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 182, 156, 72, 139, 133, 172, 161)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 131, 155, 180, 213, 83, 222, 140)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 122, 119, 36, 117, 84, 171, 219)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 95, 243, 72, 154, 154, 183, 203)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 192, 172, 53, 210, 115, 169, 135)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 216, 73, 76, 97, 190, 226, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 131, 155, 215, 242, 32, 126)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 14, 228, 207, 30, 8, 113, 61)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 63, 184, 183, 39, 110, 108, 217)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(lean_object* v_e_1_, lean_object* v_s_2_){
_start:
{
switch(lean_obj_tag(v_e_1_))
{
case 3:
{
lean_object* v_declName_3_; lean_object* v___x_4_; 
v_declName_3_ = lean_ctor_get(v_e_1_, 0);
lean_inc(v_declName_3_);
lean_dec_ref_known(v_e_1_, 3);
v___x_4_ = l_Lean_NameSet_insert(v_s_2_, v_declName_3_);
return v___x_4_;
}
case 9:
{
lean_object* v_fn_5_; lean_object* v___x_6_; 
v_fn_5_ = lean_ctor_get(v_e_1_, 0);
lean_inc(v_fn_5_);
lean_dec_ref_known(v_e_1_, 2);
v___x_6_ = l_Lean_NameSet_insert(v_s_2_, v_fn_5_);
return v___x_6_;
}
case 10:
{
lean_object* v_fn_7_; lean_object* v___x_8_; 
v_fn_7_ = lean_ctor_get(v_e_1_, 0);
lean_inc(v_fn_7_);
lean_dec_ref_known(v_e_1_, 2);
v___x_8_ = l_Lean_NameSet_insert(v_s_2_, v_fn_7_);
return v___x_8_;
}
default: 
{
lean_dec(v_e_1_);
return v_s_2_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(uint8_t v_pu_9_, lean_object* v_e_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_e_10_, v_s_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___boxed(lean_object* v_pu_13_, lean_object* v_e_14_, lean_object* v_s_15_){
_start:
{
uint8_t v_pu_boxed_16_; lean_object* v_res_17_; 
v_pu_boxed_16_ = lean_unbox(v_pu_13_);
v_res_17_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(v_pu_boxed_16_, v_e_14_, v_s_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(uint8_t v_pu_18_, lean_object* v_code_19_, lean_object* v_s_20_){
_start:
{
switch(lean_obj_tag(v_code_19_))
{
case 0:
{
lean_object* v_decl_21_; lean_object* v_k_22_; lean_object* v_value_23_; lean_object* v___x_24_; 
v_decl_21_ = lean_ctor_get(v_code_19_, 0);
lean_inc_ref(v_decl_21_);
v_k_22_ = lean_ctor_get(v_code_19_, 1);
lean_inc_ref(v_k_22_);
lean_dec_ref_known(v_code_19_, 2);
v_value_23_ = lean_ctor_get(v_decl_21_, 3);
lean_inc(v_value_23_);
lean_dec_ref(v_decl_21_);
v___x_24_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_value_23_, v_s_20_);
v_code_19_ = v_k_22_;
v_s_20_ = v___x_24_;
goto _start;
}
case 2:
{
lean_object* v_decl_26_; lean_object* v_k_27_; lean_object* v_value_28_; lean_object* v___x_29_; 
v_decl_26_ = lean_ctor_get(v_code_19_, 0);
lean_inc_ref(v_decl_26_);
v_k_27_ = lean_ctor_get(v_code_19_, 1);
lean_inc_ref(v_k_27_);
lean_dec_ref_known(v_code_19_, 2);
v_value_28_ = lean_ctor_get(v_decl_26_, 4);
lean_inc_ref(v_value_28_);
lean_dec_ref(v_decl_26_);
v___x_29_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_18_, v_k_27_, v_s_20_);
v_code_19_ = v_value_28_;
v_s_20_ = v___x_29_;
goto _start;
}
case 1:
{
lean_object* v_decl_31_; lean_object* v_k_32_; lean_object* v_value_33_; lean_object* v___x_34_; 
v_decl_31_ = lean_ctor_get(v_code_19_, 0);
lean_inc_ref(v_decl_31_);
v_k_32_ = lean_ctor_get(v_code_19_, 1);
lean_inc_ref(v_k_32_);
lean_dec_ref_known(v_code_19_, 2);
v_value_33_ = lean_ctor_get(v_decl_31_, 4);
lean_inc_ref(v_value_33_);
lean_dec_ref(v_decl_31_);
v___x_34_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_18_, v_k_32_, v_s_20_);
v_code_19_ = v_value_33_;
v_s_20_ = v___x_34_;
goto _start;
}
case 4:
{
lean_object* v_cases_36_; lean_object* v_alts_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_cases_36_ = lean_ctor_get(v_code_19_, 0);
lean_inc_ref(v_cases_36_);
lean_dec_ref_known(v_code_19_, 1);
v_alts_37_ = lean_ctor_get(v_cases_36_, 3);
lean_inc_ref(v_alts_37_);
lean_dec_ref(v_cases_36_);
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_array_get_size(v_alts_37_);
v___x_40_ = lean_nat_dec_lt(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_dec_ref(v_alts_37_);
return v_s_20_;
}
else
{
size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((size_t)0ULL);
v___x_42_ = lean_usize_of_nat(v___x_39_);
v___x_43_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_18_, v_alts_37_, v___x_41_, v___x_42_, v_s_20_);
lean_dec_ref(v_alts_37_);
return v___x_43_;
}
}
default: 
{
lean_dec_ref(v_code_19_);
return v_s_20_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(uint8_t v_pu_44_, lean_object* v_as_45_, size_t v_i_46_, size_t v_stop_47_, lean_object* v_b_48_){
_start:
{
lean_object* v___y_50_; uint8_t v___x_54_; 
v___x_54_ = lean_usize_dec_eq(v_i_46_, v_stop_47_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_array_uget_borrowed(v_as_45_, v_i_46_);
switch(lean_obj_tag(v___x_55_))
{
case 0:
{
lean_object* v_code_56_; lean_object* v___x_57_; 
v_code_56_ = lean_ctor_get(v___x_55_, 2);
lean_inc_ref(v_code_56_);
v___x_57_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_44_, v_code_56_, v_b_48_);
v___y_50_ = v___x_57_;
goto v___jp_49_;
}
case 1:
{
lean_object* v_code_58_; lean_object* v___x_59_; 
v_code_58_ = lean_ctor_get(v___x_55_, 1);
lean_inc_ref(v_code_58_);
v___x_59_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_44_, v_code_58_, v_b_48_);
v___y_50_ = v___x_59_;
goto v___jp_49_;
}
default: 
{
lean_object* v_code_60_; lean_object* v___x_61_; 
v_code_60_ = lean_ctor_get(v___x_55_, 0);
lean_inc_ref(v_code_60_);
v___x_61_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_44_, v_code_60_, v_b_48_);
v___y_50_ = v___x_61_;
goto v___jp_49_;
}
}
}
else
{
return v_b_48_;
}
v___jp_49_:
{
size_t v___x_51_; size_t v___x_52_; 
v___x_51_ = ((size_t)1ULL);
v___x_52_ = lean_usize_add(v_i_46_, v___x_51_);
v_i_46_ = v___x_52_;
v_b_48_ = v___y_50_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0___boxed(lean_object* v_pu_62_, lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_){
_start:
{
uint8_t v_pu_boxed_67_; size_t v_i_boxed_68_; size_t v_stop_boxed_69_; lean_object* v_res_70_; 
v_pu_boxed_67_ = lean_unbox(v_pu_62_);
v_i_boxed_68_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_69_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_boxed_67_, v_as_63_, v_i_boxed_68_, v_stop_boxed_69_, v_b_66_);
lean_dec_ref(v_as_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object* v_pu_71_, lean_object* v_code_72_, lean_object* v_s_73_){
_start:
{
uint8_t v_pu_boxed_74_; lean_object* v_res_75_; 
v_pu_boxed_74_ = lean_unbox(v_pu_71_);
v_res_75_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_boxed_74_, v_code_72_, v_s_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(lean_object* v_opts_76_, lean_object* v_opt_77_){
_start:
{
lean_object* v_name_78_; lean_object* v_defValue_79_; lean_object* v_map_80_; lean_object* v___x_81_; 
v_name_78_ = lean_ctor_get(v_opt_77_, 0);
v_defValue_79_ = lean_ctor_get(v_opt_77_, 1);
v_map_80_ = lean_ctor_get(v_opts_76_, 0);
v___x_81_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_80_, v_name_78_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_inc(v_defValue_79_);
return v_defValue_79_;
}
else
{
lean_object* v_val_82_; 
v_val_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v___x_81_, 1);
if (lean_obj_tag(v_val_82_) == 3)
{
lean_object* v_v_83_; 
v_v_83_ = lean_ctor_get(v_val_82_, 0);
lean_inc(v_v_83_);
lean_dec_ref_known(v_val_82_, 1);
return v_v_83_;
}
else
{
lean_dec(v_val_82_);
lean_inc(v_defValue_79_);
return v_defValue_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0___boxed(lean_object* v_opts_84_, lean_object* v_opt_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_opts_84_, v_opt_85_);
lean_dec_ref(v_opt_85_);
lean_dec_ref(v_opts_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(lean_object* v_v_87_, lean_object* v_f_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
if (lean_obj_tag(v_v_87_) == 0)
{
lean_object* v_code_94_; lean_object* v___x_95_; 
v_code_94_ = lean_ctor_get(v_v_87_, 0);
lean_inc_ref(v_code_94_);
lean_dec_ref_known(v_v_87_, 1);
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
v___x_95_ = lean_apply_6(v_f_88_, v_code_94_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, lean_box(0));
return v___x_95_;
}
else
{
lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_f_88_);
v_isSharedCheck_104_ = !lean_is_exclusive(v_v_87_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_v_87_, 0);
lean_dec(v_unused_105_);
v___x_97_ = v_v_87_;
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
else
{
lean_dec(v_v_87_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_99_ = 0;
v___x_100_ = lean_box(v___x_99_);
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 0);
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg___boxed(lean_object* v_v_106_, lean_object* v_f_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_106_, v_f_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(uint8_t v_pu_114_, lean_object* v_v_115_, lean_object* v_f_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_115_, v_f_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___boxed(lean_object* v_pu_123_, lean_object* v_v_124_, lean_object* v_f_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
uint8_t v_pu_boxed_131_; lean_object* v_res_132_; 
v_pu_boxed_131_ = lean_unbox(v_pu_123_);
v_res_132_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(v_pu_boxed_131_, v_v_124_, v_f_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(lean_object* v_toSignature_133_, uint8_t v_a_134_, uint8_t v_pu_135_, lean_object* v_code_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v_env_143_; lean_object* v_name_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_142_ = lean_st_ref_get(v___y_140_);
v_env_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc_ref(v_env_143_);
lean_dec(v___x_142_);
v_name_144_ = lean_ctor_get(v_toSignature_133_, 0);
lean_inc(v_name_144_);
lean_dec_ref(v_toSignature_133_);
v___x_145_ = 1;
v___x_146_ = l_Lean_Environment_setExporting(v_env_143_, v___x_145_);
v___x_147_ = l_Lean_Environment_findAsync_x3f(v___x_146_, v_name_144_, v_a_134_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_box(v_a_134_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_169_; 
v_val_150_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_169_ == 0)
{
v___x_152_ = v___x_147_;
v_isShared_153_ = v_isSharedCheck_169_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v___x_147_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_169_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
uint8_t v_kind_154_; uint8_t v___x_155_; uint8_t v___x_156_; 
v_kind_154_ = lean_ctor_get_uint8(v_val_150_, sizeof(void*)*3);
lean_dec(v_val_150_);
v___x_155_ = 0;
v___x_156_ = l_Lean_instBEqConstantKind_beq(v_kind_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_box(v___x_156_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 0);
lean_ctor_set(v___x_152_, 0, v___x_157_);
v___x_159_ = v___x_152_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_161_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_139_);
v___x_162_ = l_Lean_Compiler_LCNF_compiler_small;
v___x_163_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v___x_161_, v___x_162_);
lean_dec_ref(v___x_161_);
v___x_164_ = l_Lean_Compiler_LCNF_Code_sizeLe(v_pu_135_, v_code_136_, v___x_163_);
lean_dec(v___x_163_);
v___x_165_ = lean_box(v___x_164_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 0);
lean_ctor_set(v___x_152_, 0, v___x_165_);
v___x_167_ = v___x_152_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed(lean_object* v_toSignature_170_, lean_object* v_a_171_, lean_object* v_pu_172_, lean_object* v_code_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v_a_965__boxed_179_; uint8_t v_pu_boxed_180_; lean_object* v_res_181_; 
v_a_965__boxed_179_ = lean_unbox(v_a_171_);
v_pu_boxed_180_ = lean_unbox(v_pu_172_);
v_res_181_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_170_, v_a_965__boxed_179_, v_pu_boxed_180_, v_code_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec_ref(v_code_173_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(uint8_t v_pu_182_, lean_object* v_decl_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
lean_inc_ref(v_decl_183_);
v___x_189_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_183_, v_a_186_, v_a_187_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; uint8_t v___x_191_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v___x_191_ = lean_unbox(v_a_190_);
if (v___x_191_ == 0)
{
lean_object* v_toSignature_192_; lean_object* v_value_193_; lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v___x_196_; 
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
v_toSignature_192_ = lean_ctor_get(v_decl_183_, 0);
lean_inc_ref(v_toSignature_192_);
v_value_193_ = lean_ctor_get(v_decl_183_, 1);
lean_inc_ref(v_value_193_);
lean_dec_ref(v_decl_183_);
v___x_194_ = lean_box(v_pu_182_);
v___f_195_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed), 9, 3);
lean_closure_set(v___f_195_, 0, v_toSignature_192_);
lean_closure_set(v___f_195_, 1, v_a_190_);
lean_closure_set(v___f_195_, 2, v___x_194_);
v___x_196_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_value_193_, v___f_195_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_196_;
}
else
{
lean_dec_ref(v_decl_183_);
return v___x_189_;
}
}
else
{
lean_dec_ref(v_decl_183_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(lean_object* v_pu_197_, lean_object* v_decl_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
uint8_t v_pu_boxed_204_; lean_object* v_res_205_; 
v_pu_boxed_204_ = lean_unbox(v_pu_197_);
v_res_205_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_boxed_204_, v_decl_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_205_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_206_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v___x_210_);
lean_ctor_set(v___x_211_, 3, v___x_210_);
lean_ctor_set(v___x_211_, 4, v___x_209_);
lean_ctor_set(v___x_211_, 5, v___x_209_);
lean_ctor_set(v___x_211_, 6, v___x_209_);
lean_ctor_set(v___x_211_, 7, v___x_209_);
lean_ctor_set(v___x_211_, 8, v___x_209_);
lean_ctor_set(v___x_211_, 9, v___x_209_);
lean_ctor_set(v___x_211_, 10, v___x_209_);
return v___x_211_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_212_; double v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_float_of_nat(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(lean_object* v_cls_217_, lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_ref_224_; lean_object* v___x_225_; lean_object* v_env_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_ref_224_ = lean_ctor_get(v___y_221_, 2);
v___x_225_ = lean_st_ref_get(v___y_222_);
v_env_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_env_226_);
lean_dec(v___x_225_);
v___x_227_ = lean_st_ref_get(v___y_220_);
v___x_228_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_219_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_288_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_288_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_288_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_288_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_lctx_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_286_; 
v_lctx_233_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_227_, 1);
lean_dec(v_unused_287_);
v___x_235_ = v___x_227_;
v_isShared_236_ = v_isSharedCheck_286_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_lctx_233_);
lean_dec(v___x_227_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_286_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_237_ = lean_unbox(v_a_229_);
lean_dec(v_a_229_);
v___x_238_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_233_, v___x_237_);
lean_dec_ref(v_lctx_233_);
v___x_239_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_221_);
v___x_240_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_241_, 0, v_env_226_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
lean_ctor_set(v___x_241_, 2, v___x_238_);
lean_ctor_set(v___x_241_, 3, v___x_239_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 3);
lean_ctor_set(v___x_235_, 1, v_msg_218_);
lean_ctor_set(v___x_235_, 0, v___x_241_);
v___x_243_ = v___x_235_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_msg_218_);
v___x_243_ = v_reuseFailAlloc_285_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v_traceState_245_; lean_object* v_env_246_; lean_object* v_nextMacroScope_247_; lean_object* v_ngen_248_; lean_object* v_auxDeclNGen_249_; lean_object* v_cache_250_; lean_object* v_recordedDeps_251_; lean_object* v_messages_252_; lean_object* v_infoState_253_; lean_object* v_snapshotTasks_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_284_; 
v___x_244_ = lean_st_ref_take(v___y_222_);
v_traceState_245_ = lean_ctor_get(v___x_244_, 4);
v_env_246_ = lean_ctor_get(v___x_244_, 0);
v_nextMacroScope_247_ = lean_ctor_get(v___x_244_, 1);
v_ngen_248_ = lean_ctor_get(v___x_244_, 2);
v_auxDeclNGen_249_ = lean_ctor_get(v___x_244_, 3);
v_cache_250_ = lean_ctor_get(v___x_244_, 5);
v_recordedDeps_251_ = lean_ctor_get(v___x_244_, 6);
v_messages_252_ = lean_ctor_get(v___x_244_, 7);
v_infoState_253_ = lean_ctor_get(v___x_244_, 8);
v_snapshotTasks_254_ = lean_ctor_get(v___x_244_, 9);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_284_ == 0)
{
v___x_256_ = v___x_244_;
v_isShared_257_ = v_isSharedCheck_284_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_snapshotTasks_254_);
lean_inc(v_infoState_253_);
lean_inc(v_messages_252_);
lean_inc(v_recordedDeps_251_);
lean_inc(v_cache_250_);
lean_inc(v_traceState_245_);
lean_inc(v_auxDeclNGen_249_);
lean_inc(v_ngen_248_);
lean_inc(v_nextMacroScope_247_);
lean_inc(v_env_246_);
lean_dec(v___x_244_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_284_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
uint64_t v_tid_258_; lean_object* v_traces_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_283_; 
v_tid_258_ = lean_ctor_get_uint64(v_traceState_245_, sizeof(void*)*1);
v_traces_259_ = lean_ctor_get(v_traceState_245_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_traceState_245_);
if (v_isSharedCheck_283_ == 0)
{
v___x_261_ = v_traceState_245_;
v_isShared_262_ = v_isSharedCheck_283_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_traces_259_);
lean_dec(v_traceState_245_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_283_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; double v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_box(0);
v___x_265_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_266_ = 0;
v___x_267_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_268_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_268_, 0, v_cls_217_);
lean_ctor_set(v___x_268_, 1, v___x_264_);
lean_ctor_set(v___x_268_, 2, v___x_267_);
lean_ctor_set_float(v___x_268_, sizeof(void*)*3, v___x_265_);
lean_ctor_set_float(v___x_268_, sizeof(void*)*3 + 8, v___x_265_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*3 + 16, v___x_266_);
v___x_269_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_270_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_243_);
lean_ctor_set(v___x_270_, 2, v___x_269_);
lean_inc(v_ref_224_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_ref_224_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = l_Lean_PersistentArray_push___redArg(v_traces_259_, v___x_271_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_272_);
v___x_274_ = v___x_261_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_272_);
lean_ctor_set_uint64(v_reuseFailAlloc_282_, sizeof(void*)*1, v_tid_258_);
v___x_274_ = v_reuseFailAlloc_282_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v___x_274_);
v___x_276_ = v___x_256_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_env_246_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_nextMacroScope_247_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_ngen_248_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_auxDeclNGen_249_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_cache_250_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_recordedDeps_251_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_messages_252_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_infoState_253_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_snapshotTasks_254_);
v___x_276_ = v_reuseFailAlloc_281_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_st_ref_put(v___y_222_, v___x_276_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_263_);
v___x_279_ = v___x_231_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_263_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v___x_227_);
lean_dec_ref(v_env_226_);
lean_dec_ref(v_msg_218_);
lean_dec(v_cls_217_);
v_a_289_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_228_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_228_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___boxed(lean_object* v_cls_297_, lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v_cls_297_, v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(lean_object* v_f_305_, lean_object* v_v_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
if (lean_obj_tag(v_v_306_) == 0)
{
lean_object* v_code_312_; lean_object* v___x_313_; 
v_code_312_ = lean_ctor_get(v_v_306_, 0);
lean_inc_ref(v_code_312_);
lean_dec_ref_known(v_v_306_, 1);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
v___x_313_ = lean_apply_6(v_f_305_, v_code_312_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
return v___x_313_;
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_f_305_);
v_isSharedCheck_321_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_v_306_, 0);
lean_dec(v_unused_322_);
v___x_315_ = v_v_306_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_v_306_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 0);
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg___boxed(lean_object* v_f_323_, lean_object* v_v_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_323_, v_v_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(uint8_t v_pu_331_, lean_object* v_f_332_, lean_object* v_v_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_332_, v_v_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(lean_object* v_pu_340_, lean_object* v_f_341_, lean_object* v_v_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v_pu_boxed_348_; lean_object* v_res_349_; 
v_pu_boxed_348_ = lean_unbox(v_pu_340_);
v_res_349_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_boxed_348_, v_f_341_, v_v_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object* v_pu_350_, lean_object* v_phase_351_, lean_object* v_decl_352_, lean_object* v_code_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
uint8_t v_pu_boxed_359_; uint8_t v_phase_boxed_360_; lean_object* v_res_361_; 
v_pu_boxed_359_ = lean_unbox(v_pu_350_);
v_phase_boxed_360_ = lean_unbox(v_phase_351_);
v_res_361_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(v_pu_boxed_359_, v_phase_boxed_360_, v_decl_352_, v_code_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_375_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_376_ = l_Lean_Name_append(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec(uint8_t v_pu_383_, uint8_t v_phase_384_, lean_object* v_decl_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___x_401_; lean_object* v_toSignature_402_; lean_object* v_env_403_; lean_object* v_nextMacroScope_404_; lean_object* v_ngen_405_; lean_object* v_auxDeclNGen_406_; lean_object* v_traceState_407_; lean_object* v_recordedDeps_408_; lean_object* v_messages_409_; lean_object* v_infoState_410_; lean_object* v_snapshotTasks_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_482_; 
v___x_391_ = lean_box(v_pu_383_);
v___x_392_ = lean_box(v_phase_384_);
lean_inc_ref(v_decl_385_);
v___f_393_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed), 9, 3);
lean_closure_set(v___f_393_, 0, v___x_391_);
lean_closure_set(v___f_393_, 1, v___x_392_);
lean_closure_set(v___f_393_, 2, v_decl_385_);
v___x_401_ = lean_st_ref_take(v_a_389_);
v_toSignature_402_ = lean_ctor_get(v_decl_385_, 0);
v_env_403_ = lean_ctor_get(v___x_401_, 0);
v_nextMacroScope_404_ = lean_ctor_get(v___x_401_, 1);
v_ngen_405_ = lean_ctor_get(v___x_401_, 2);
v_auxDeclNGen_406_ = lean_ctor_get(v___x_401_, 3);
v_traceState_407_ = lean_ctor_get(v___x_401_, 4);
v_recordedDeps_408_ = lean_ctor_get(v___x_401_, 6);
v_messages_409_ = lean_ctor_get(v___x_401_, 7);
v_infoState_410_ = lean_ctor_get(v___x_401_, 8);
v_snapshotTasks_411_ = lean_ctor_get(v___x_401_, 9);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_401_, 5);
lean_dec(v_unused_483_);
v___x_413_ = v___x_401_;
v_isShared_414_ = v_isSharedCheck_482_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snapshotTasks_411_);
lean_inc(v_infoState_410_);
lean_inc(v_messages_409_);
lean_inc(v_recordedDeps_408_);
lean_inc(v_traceState_407_);
lean_inc(v_auxDeclNGen_406_);
lean_inc(v_ngen_405_);
lean_inc(v_nextMacroScope_404_);
lean_inc(v_env_403_);
lean_dec(v___x_401_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_482_;
goto v_resetjp_412_;
}
v___jp_394_:
{
lean_object* v_value_399_; lean_object* v___x_400_; 
v_value_399_ = lean_ctor_get(v_decl_385_, 1);
lean_inc_ref(v_value_399_);
lean_dec_ref(v_decl_385_);
v___x_400_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_393_, v_value_399_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v___x_400_;
}
v_resetjp_412_:
{
lean_object* v_name_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___x_444_; 
v_name_415_ = lean_ctor_get(v_toSignature_402_, 0);
lean_inc(v_name_415_);
v___x_416_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_403_, v_name_415_);
v___x_417_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 5, v___x_417_);
lean_ctor_set(v___x_413_, 0, v___x_416_);
v___x_444_ = v___x_413_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_404_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_405_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_406_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_traceState_407_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_recordedDeps_408_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_messages_409_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_infoState_410_);
lean_ctor_set(v_reuseFailAlloc_481_, 9, v_snapshotTasks_411_);
v___x_444_ = v_reuseFailAlloc_481_;
goto v_reusejp_443_;
}
v___jp_418_:
{
lean_object* v___x_423_; lean_object* v_env_424_; lean_object* v_nextMacroScope_425_; lean_object* v_ngen_426_; lean_object* v_auxDeclNGen_427_; lean_object* v_traceState_428_; lean_object* v_recordedDeps_429_; lean_object* v_messages_430_; lean_object* v_infoState_431_; lean_object* v_snapshotTasks_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v___x_423_ = lean_st_ref_take(v___y_422_);
v_env_424_ = lean_ctor_get(v___x_423_, 0);
v_nextMacroScope_425_ = lean_ctor_get(v___x_423_, 1);
v_ngen_426_ = lean_ctor_get(v___x_423_, 2);
v_auxDeclNGen_427_ = lean_ctor_get(v___x_423_, 3);
v_traceState_428_ = lean_ctor_get(v___x_423_, 4);
v_recordedDeps_429_ = lean_ctor_get(v___x_423_, 6);
v_messages_430_ = lean_ctor_get(v___x_423_, 7);
v_infoState_431_ = lean_ctor_get(v___x_423_, 8);
v_snapshotTasks_432_ = lean_ctor_get(v___x_423_, 9);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_423_, 5);
lean_dec(v_unused_442_);
v___x_434_ = v___x_423_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snapshotTasks_432_);
lean_inc(v_infoState_431_);
lean_inc(v_messages_430_);
lean_inc(v_recordedDeps_429_);
lean_inc(v_traceState_428_);
lean_inc(v_auxDeclNGen_427_);
lean_inc(v_ngen_426_);
lean_inc(v_nextMacroScope_425_);
lean_inc(v_env_424_);
lean_dec(v___x_423_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v_name_415_);
v___x_436_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_424_, v_phase_384_, v_name_415_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 5, v___x_417_);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_ngen_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_auxDeclNGen_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_traceState_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_recordedDeps_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_messages_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_infoState_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_snapshotTasks_432_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_st_ref_put(v___y_422_, v___x_438_);
v___y_395_ = v___y_419_;
v___y_396_ = v___y_420_;
v___y_397_ = v___y_421_;
v___y_398_ = v___y_422_;
goto v___jp_394_;
}
}
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_st_ref_put(v_a_389_, v___x_444_);
lean_inc_ref(v_decl_385_);
v___x_446_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_383_, v_decl_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_472_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_472_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_472_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_472_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec_ref(v___f_393_);
lean_dec_ref(v_decl_385_);
v___x_452_ = lean_box(0);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_456_; lean_object* v_env_457_; uint8_t v___x_458_; 
lean_del_object(v___x_449_);
v___x_456_ = lean_st_ref_get(v_a_389_);
v_env_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc_ref(v_env_457_);
lean_dec(v___x_456_);
v___x_458_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_457_, v_phase_384_, v_name_415_);
if (v___x_458_ == 0)
{
lean_object* v_toCold_459_; lean_object* v_options_460_; uint8_t v_hasTrace_461_; 
v_toCold_459_ = lean_ctor_get(v_a_388_, 0);
v_options_460_ = lean_ctor_get(v_toCold_459_, 2);
v_hasTrace_461_ = lean_ctor_get_uint8(v_options_460_, sizeof(void*)*1);
if (v_hasTrace_461_ == 0)
{
v___y_419_ = v_a_386_;
v___y_420_ = v_a_387_;
v___y_421_ = v_a_388_;
v___y_422_ = v_a_389_;
goto v___jp_418_;
}
else
{
lean_object* v_inheritedTraceOptions_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_inheritedTraceOptions_462_ = lean_ctor_get(v_toCold_459_, 11);
v___x_463_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_464_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_465_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_462_, v_options_460_, v___x_464_);
if (v___x_465_ == 0)
{
v___y_419_ = v_a_386_;
v___y_420_ = v_a_387_;
v___y_421_ = v_a_388_;
v___y_422_ = v_a_389_;
goto v___jp_418_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_415_);
v___x_467_ = l_Lean_MessageData_ofName(v_name_415_);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_463_, v___x_470_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec_ref_known(v___x_471_, 1);
v___y_419_ = v_a_386_;
v___y_420_ = v_a_387_;
v___y_421_ = v_a_388_;
v___y_422_ = v_a_389_;
goto v___jp_418_;
}
else
{
lean_dec_ref(v___f_393_);
lean_dec_ref(v_decl_385_);
return v___x_471_;
}
}
}
}
else
{
v___y_395_ = v_a_386_;
v___y_396_ = v_a_387_;
v___y_397_ = v_a_388_;
v___y_398_ = v_a_389_;
goto v___jp_394_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v___f_393_);
lean_dec_ref(v_decl_385_);
v_a_473_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_446_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_446_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(uint8_t v_phase_487_, lean_object* v_decl_488_, lean_object* v_init_489_, lean_object* v_x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v_k_496_; lean_object* v_l_497_; lean_object* v_r_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_k_496_ = lean_ctor_get(v_x_490_, 1);
lean_inc(v_k_496_);
v_l_497_ = lean_ctor_get(v_x_490_, 3);
lean_inc(v_l_497_);
v_r_498_ = lean_ctor_get(v_x_490_, 4);
lean_inc(v_r_498_);
lean_dec_ref_known(v_x_490_, 5);
v___x_499_ = lean_box(0);
lean_inc_ref(v_decl_488_);
v___x_500_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_487_, v_decl_488_, v_init_489_, v_l_497_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v___x_501_; 
lean_dec_ref_known(v___x_500_, 1);
v___x_501_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_496_, v_phase_487_, v___y_494_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
if (lean_obj_tag(v_a_502_) == 1)
{
lean_object* v_val_503_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___x_520_; lean_object* v_env_521_; uint8_t v___x_522_; 
v_val_503_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_502_, 1);
v___x_520_ = lean_st_ref_get(v___y_494_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
v___x_522_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_521_, v_k_496_);
if (v___x_522_ == 0)
{
lean_object* v_toCold_523_; lean_object* v_options_524_; uint8_t v_hasTrace_525_; 
v_toCold_523_ = lean_ctor_get(v___y_493_, 0);
v_options_524_ = lean_ctor_get(v_toCold_523_, 2);
v_hasTrace_525_ = lean_ctor_get_uint8(v_options_524_, sizeof(void*)*1);
if (v_hasTrace_525_ == 0)
{
lean_dec(v_k_496_);
v___y_505_ = v___y_491_;
v___y_506_ = v___y_492_;
v___y_507_ = v___y_493_;
v___y_508_ = v___y_494_;
goto v___jp_504_;
}
else
{
lean_object* v_inheritedTraceOptions_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_inheritedTraceOptions_526_ = lean_ctor_get(v_toCold_523_, 11);
v___x_527_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_528_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_526_, v_options_524_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v_k_496_);
v___y_505_ = v___y_491_;
v___y_506_ = v___y_492_;
v___y_507_ = v___y_493_;
v___y_508_ = v___y_494_;
goto v___jp_504_;
}
else
{
lean_object* v_toSignature_530_; lean_object* v_name_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_toSignature_530_ = lean_ctor_get(v_decl_488_, 0);
v_name_531_ = lean_ctor_get(v_toSignature_530_, 0);
v___x_532_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
v___x_533_ = l_Lean_MessageData_ofName(v_k_496_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_inc(v_name_531_);
v___x_537_ = l_Lean_MessageData_ofName(v_name_531_);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_527_, v___x_538_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_dec_ref_known(v___x_539_, 1);
v___y_505_ = v___y_491_;
v___y_506_ = v___y_492_;
v___y_507_ = v___y_493_;
v___y_508_ = v___y_494_;
goto v___jp_504_;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_val_503_);
lean_dec(v_r_498_);
lean_dec_ref(v_decl_488_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
else
{
lean_dec(v_val_503_);
lean_dec(v_k_496_);
v_init_489_ = v___x_499_;
v_x_490_ = v_r_498_;
goto _start;
}
v___jp_504_:
{
uint8_t v___x_509_; lean_object* v___x_510_; 
v___x_509_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_487_);
v___x_510_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_509_, v_phase_487_, v_val_503_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_dec_ref_known(v___x_510_, 1);
v_init_489_ = v___x_499_;
v_x_490_ = v_r_498_;
goto _start;
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_r_498_);
lean_dec_ref(v_decl_488_);
v_a_512_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
else
{
lean_dec(v_a_502_);
lean_dec(v_k_496_);
v_init_489_ = v___x_499_;
v_x_490_ = v_r_498_;
goto _start;
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_r_498_);
lean_dec(v_k_496_);
lean_dec_ref(v_decl_488_);
v_a_550_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_501_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_501_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_dec(v_r_498_);
lean_dec(v_k_496_);
lean_dec_ref(v_decl_488_);
return v___x_500_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_decl_488_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_init_489_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t v_pu_560_, uint8_t v_phase_561_, lean_object* v_decl_562_, lean_object* v_code_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = l_Lean_NameSet_empty;
v___x_570_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_560_, v_code_563_, v___x_569_);
v___x_571_ = lean_box(0);
v___x_572_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_561_, v_decl_562_, v___x_571_, v___x_570_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_580_);
v___x_574_ = v___x_572_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_dec(v___x_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_571_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_571_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object* v_phase_589_, lean_object* v_decl_590_, lean_object* v_init_591_, lean_object* v_x_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_phase_boxed_598_; lean_object* v_res_599_; 
v_phase_boxed_598_ = lean_unbox(v_phase_589_);
v_res_599_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_598_, v_decl_590_, v_init_591_, v_x_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object* v_pu_600_, lean_object* v_phase_601_, lean_object* v_decl_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
uint8_t v_pu_boxed_608_; uint8_t v_phase_boxed_609_; lean_object* v_res_610_; 
v_pu_boxed_608_ = lean_unbox(v_pu_600_);
v_phase_boxed_609_ = lean_unbox(v_phase_601_);
v_res_610_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_boxed_608_, v_phase_boxed_609_, v_decl_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_ref_617_; lean_object* v___x_618_; lean_object* v_env_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_ref_617_ = lean_ctor_get(v___y_614_, 2);
v___x_618_ = lean_st_ref_get(v___y_615_);
v_env_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_619_);
lean_dec(v___x_618_);
v___x_620_ = lean_st_ref_get(v___y_613_);
v___x_621_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_612_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_644_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_644_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_lctx_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_642_; 
v_lctx_626_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___x_620_, 1);
lean_dec(v_unused_643_);
v___x_628_ = v___x_620_;
v_isShared_629_ = v_isSharedCheck_642_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_lctx_626_);
lean_dec(v___x_620_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_642_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_630_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
v___x_631_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_626_, v___x_630_);
lean_dec_ref(v_lctx_626_);
v___x_632_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_614_);
v___x_633_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_634_, 0, v_env_619_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v___x_631_);
lean_ctor_set(v___x_634_, 3, v___x_632_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 3);
lean_ctor_set(v___x_628_, 1, v_msg_611_);
lean_ctor_set(v___x_628_, 0, v___x_634_);
v___x_636_ = v___x_628_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_msg_611_);
v___x_636_ = v_reuseFailAlloc_641_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
lean_inc(v_ref_617_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_ref_617_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 1);
lean_ctor_set(v___x_624_, 0, v___x_637_);
v___x_639_ = v___x_624_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v___x_620_);
lean_dec_ref(v_env_619_);
lean_dec_ref(v_msg_611_);
v_a_645_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_621_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_621_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_661_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_669_, lean_object* v_msg_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_669_, v_msg_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
return v_res_677_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_678_, lean_object* v_opt_679_){
_start:
{
lean_object* v_name_680_; lean_object* v_defValue_681_; lean_object* v_map_682_; lean_object* v___x_683_; 
v_name_680_ = lean_ctor_get(v_opt_679_, 0);
v_defValue_681_ = lean_ctor_get(v_opt_679_, 1);
v_map_682_ = lean_ctor_get(v_opts_678_, 0);
v___x_683_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_682_, v_name_680_);
if (lean_obj_tag(v___x_683_) == 0)
{
uint8_t v___x_684_; 
v___x_684_ = lean_unbox(v_defValue_681_);
return v___x_684_;
}
else
{
lean_object* v_val_685_; 
v_val_685_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___x_683_, 1);
if (lean_obj_tag(v_val_685_) == 1)
{
uint8_t v_v_686_; 
v_v_686_ = lean_ctor_get_uint8(v_val_685_, 0);
lean_dec_ref_known(v_val_685_, 0);
return v_v_686_;
}
else
{
uint8_t v___x_687_; 
lean_dec(v_val_685_);
v___x_687_ = lean_unbox(v_defValue_681_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_688_, lean_object* v_opt_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_688_, v_opt_689_);
lean_dec_ref(v_opt_689_);
lean_dec_ref(v_opts_688_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_692_, lean_object* v_v_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
if (lean_obj_tag(v_v_693_) == 0)
{
lean_object* v_code_700_; lean_object* v___x_701_; 
v_code_700_ = lean_ctor_get(v_v_693_, 0);
lean_inc_ref(v_code_700_);
lean_dec_ref_known(v_v_693_, 1);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
v___x_701_ = lean_apply_7(v_f_692_, v_code_700_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, lean_box(0));
return v___x_701_;
}
else
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_f_692_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_v_693_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_v_693_, 0);
lean_dec(v_unused_711_);
v___x_703_ = v_v_693_;
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_v_693_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___y_694_);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_712_, lean_object* v_v_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_712_, v_v_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_721_, lean_object* v_f_722_, lean_object* v_v_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_722_, v_v_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_731_, lean_object* v_f_732_, lean_object* v_v_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
uint8_t v_pu_boxed_740_; lean_object* v_res_741_; 
v_pu_boxed_740_ = lean_unbox(v_pu_731_);
v_res_741_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_740_, v_f_732_, v_v_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_741_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_775_, lean_object* v_origDecl_776_, uint8_t v_isMeta_777_, uint8_t v_isPublic_778_, lean_object* v_init_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_k_787_; lean_object* v_l_788_; lean_object* v_r_789_; lean_object* v___x_790_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_k_787_ = lean_ctor_get(v_x_780_, 1);
lean_inc(v_k_787_);
v_l_788_ = lean_ctor_get(v_x_780_, 3);
lean_inc(v_l_788_);
v_r_789_ = lean_ctor_get(v_x_780_, 4);
lean_inc(v_r_789_);
lean_dec_ref_known(v_x_780_, 5);
v___x_790_ = lean_box(0);
v___x_847_ = lean_box(0);
lean_inc_ref(v_origDecl_776_);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_775_, v_origDecl_776_, v_isMeta_777_, v_isPublic_778_, v_init_779_, v_l_788_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_1064_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_snd_850_ = lean_ctor_get(v_a_849_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_849_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_a_849_, 0);
lean_dec(v_unused_1065_);
v___x_852_ = v_a_849_;
v_isShared_853_ = v_isSharedCheck_1064_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_dec(v_a_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_1064_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; uint8_t v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; 
v___x_854_ = l_Lean_NameSet_contains(v_snd_850_, v_k_787_);
if (v___x_854_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_env_885_; uint8_t v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; 
lean_inc(v_k_787_);
v___x_883_ = l_Lean_NameSet_insert(v_snd_850_, v_k_787_);
v___x_884_ = lean_st_ref_get(v___y_785_);
v_env_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_884_);
if (v_isMeta_777_ == 0)
{
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
else
{
if (v_isPublic_778_ == 0)
{
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
else
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_885_, v_k_787_);
if (lean_obj_tag(v___x_994_) == 1)
{
lean_object* v_val_995_; uint8_t v___x_996_; 
v_val_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_994_, 1);
lean_inc(v_k_787_);
lean_inc_ref(v_env_885_);
v___x_996_ = l_Lean_isMarkedMeta(v_env_885_, v_k_787_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v_modules_998_; lean_object* v_moduleNames_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_997_ = l_Lean_Environment_header(v_env_885_);
v_modules_998_ = lean_ctor_get(v___x_997_, 3);
lean_inc_ref(v_modules_998_);
v_moduleNames_999_ = lean_ctor_get(v___x_997_, 4);
lean_inc_ref(v_moduleNames_999_);
lean_dec_ref(v___x_997_);
v___x_1000_ = lean_array_get_size(v_modules_998_);
v___x_1001_ = lean_nat_dec_lt(v_val_995_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_moduleNames_999_);
lean_dec_ref(v_modules_998_);
lean_dec(v_val_995_);
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1002_; lean_object* v_toImport_1003_; uint8_t v_isExported_1004_; 
v___x_1002_ = lean_array_fget(v_modules_998_, v_val_995_);
lean_dec_ref(v_modules_998_);
v_toImport_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc_ref(v_toImport_1003_);
lean_dec(v___x_1002_);
v_isExported_1004_ = lean_ctor_get_uint8(v_toImport_1003_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1003_);
if (v_isExported_1004_ == 0)
{
lean_object* v_toSignature_1005_; lean_object* v_name_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_env_885_);
lean_dec(v___x_883_);
lean_del_object(v___x_852_);
lean_dec(v_r_789_);
v_toSignature_1005_ = lean_ctor_get(v_origDecl_776_, 0);
lean_inc_ref(v_toSignature_1005_);
lean_dec_ref(v_origDecl_776_);
v_name_1006_ = lean_ctor_get(v_toSignature_1005_, 0);
lean_inc(v_name_1006_);
lean_dec_ref(v_toSignature_1005_);
v___x_1007_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1008_ = l_Lean_MessageData_ofConstName(v_name_1006_, v___x_996_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_MessageData_ofConstName(v_k_787_, v___x_996_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_array_get(v___x_847_, v_moduleNames_999_, v_val_995_);
lean_dec(v_val_995_);
lean_dec_ref(v_moduleNames_999_);
v___x_1017_ = l_Lean_MessageData_ofName(v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1015_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1020_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_dec_ref(v_moduleNames_999_);
lean_dec(v_val_995_);
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v_modules_1031_; lean_object* v_moduleNames_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1030_ = l_Lean_Environment_header(v_env_885_);
v_modules_1031_ = lean_ctor_get(v___x_1030_, 3);
lean_inc_ref(v_modules_1031_);
v_moduleNames_1032_ = lean_ctor_get(v___x_1030_, 4);
lean_inc_ref(v_moduleNames_1032_);
lean_dec_ref(v___x_1030_);
v___x_1033_ = lean_array_get_size(v_modules_1031_);
v___x_1034_ = lean_nat_dec_lt(v_val_995_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v_moduleNames_1032_);
lean_dec_ref(v_modules_1031_);
lean_dec(v_val_995_);
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1035_; lean_object* v_toImport_1036_; uint8_t v_isExported_1037_; 
v___x_1035_ = lean_array_fget(v_modules_1031_, v_val_995_);
lean_dec_ref(v_modules_1031_);
v_toImport_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref(v_toImport_1036_);
lean_dec(v___x_1035_);
v_isExported_1037_ = lean_ctor_get_uint8(v_toImport_1036_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1036_);
if (v_isExported_1037_ == 0)
{
lean_object* v_toSignature_1038_; lean_object* v_name_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_env_885_);
lean_dec(v___x_883_);
lean_del_object(v___x_852_);
lean_dec(v_r_789_);
v_toSignature_1038_ = lean_ctor_get(v_origDecl_776_, 0);
lean_inc_ref(v_toSignature_1038_);
lean_dec_ref(v_origDecl_776_);
v_name_1039_ = lean_ctor_get(v_toSignature_1038_, 0);
lean_inc(v_name_1039_);
lean_dec_ref(v_toSignature_1038_);
v___x_1040_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1041_ = l_Lean_MessageData_ofConstName(v_name_1039_, v___x_854_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_MessageData_ofConstName(v_k_787_, v___x_854_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_array_get(v___x_847_, v_moduleNames_1032_, v_val_995_);
lean_dec(v_val_995_);
lean_dec_ref(v_moduleNames_1032_);
v___x_1050_ = l_Lean_MessageData_ofName(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1048_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1053_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_dec_ref(v_moduleNames_1032_);
lean_dec(v_val_995_);
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
}
}
}
else
{
lean_dec(v___x_994_);
v___y_984_ = v___x_883_;
v___y_985_ = v___y_782_;
v___y_986_ = v___y_783_;
v___y_987_ = v___y_784_;
v___y_988_ = v___y_785_;
goto v___jp_983_;
}
}
}
v___jp_886_:
{
uint8_t v___x_893_; uint8_t v___x_894_; 
v___x_893_ = 1;
v___x_894_ = l_Lean_instBEqIRPhases_beq(v___y_887_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_env_885_);
lean_del_object(v___x_852_);
v___y_836_ = v___y_887_;
v___y_837_ = v___y_888_;
v___y_838_ = v___y_889_;
v___y_839_ = v___y_890_;
v___y_840_ = v___y_891_;
v___y_841_ = v___y_892_;
goto v___jp_835_;
}
else
{
if (v_isMeta_777_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v___y_888_);
lean_dec(v_r_789_);
v___x_895_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_885_, v_k_787_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; uint8_t v___x_897_; 
v_val_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_895_, 1);
lean_inc(v_k_787_);
lean_inc_ref(v_env_885_);
v___x_897_ = l_Lean_isMarkedMeta(v_env_885_, v_k_787_);
if (v___x_897_ == 0)
{
lean_object* v_toSignature_898_; lean_object* v_name_899_; lean_object* v___x_900_; lean_object* v_moduleNames_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_del_object(v___x_852_);
v_toSignature_898_ = lean_ctor_get(v_origDecl_776_, 0);
lean_inc_ref(v_toSignature_898_);
lean_dec_ref(v_origDecl_776_);
v_name_899_ = lean_ctor_get(v_toSignature_898_, 0);
lean_inc(v_name_899_);
lean_dec_ref(v_toSignature_898_);
v___x_900_ = l_Lean_Environment_header(v_env_885_);
lean_dec_ref(v_env_885_);
v_moduleNames_901_ = lean_ctor_get(v___x_900_, 4);
lean_inc_ref(v_moduleNames_901_);
lean_dec_ref(v___x_900_);
v___x_902_ = l_Lean_MessageData_ofConstName(v_name_899_, v___x_854_);
v___x_903_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
v___x_905_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_MessageData_ofConstName(v_k_787_, v___x_854_);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_array_get(v___x_847_, v_moduleNames_901_, v_val_896_);
lean_dec(v_val_896_);
lean_dec_ref(v_moduleNames_901_);
v___x_912_ = l_Lean_MessageData_ofName(v___x_911_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_910_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_915_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_dec(v_val_896_);
lean_dec_ref(v_env_885_);
v___y_856_ = v___y_887_;
v___y_857_ = v___y_889_;
v___y_858_ = v___y_890_;
v___y_859_ = v___y_891_;
v___y_860_ = v___y_892_;
goto v___jp_855_;
}
}
else
{
lean_dec(v___x_895_);
lean_dec_ref(v_env_885_);
v___y_856_ = v___y_887_;
v___y_857_ = v___y_889_;
v___y_858_ = v___y_890_;
v___y_859_ = v___y_891_;
v___y_860_ = v___y_892_;
goto v___jp_855_;
}
}
else
{
lean_dec_ref(v_env_885_);
lean_del_object(v___x_852_);
v___y_836_ = v___y_887_;
v___y_837_ = v___y_888_;
v___y_838_ = v___y_889_;
v___y_839_ = v___y_890_;
v___y_840_ = v___y_891_;
v___y_841_ = v___y_892_;
goto v___jp_835_;
}
}
}
v___jp_925_:
{
uint8_t v___x_931_; uint8_t v___x_932_; uint8_t v___x_933_; 
lean_inc(v_k_787_);
lean_inc_ref(v_env_885_);
v___x_931_ = l_Lean_getIRPhases(v_env_885_, v_k_787_);
v___x_932_ = 0;
v___x_933_ = l_Lean_instBEqIRPhases_beq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
v___y_887_ = v___x_931_;
v___y_888_ = v___y_929_;
v___y_889_ = v___y_928_;
v___y_890_ = v___y_927_;
v___y_891_ = v___y_926_;
v___y_892_ = v___y_930_;
goto v___jp_886_;
}
else
{
if (v_isMeta_777_ == 0)
{
v___y_887_ = v___x_931_;
v___y_888_ = v___y_929_;
v___y_889_ = v___y_928_;
v___y_890_ = v___y_927_;
v___y_891_ = v___y_926_;
v___y_892_ = v___y_930_;
goto v___jp_886_;
}
else
{
lean_object* v___x_934_; 
lean_dec(v___y_929_);
lean_del_object(v___x_852_);
lean_dec(v_r_789_);
v___x_934_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_885_, v_k_787_);
if (lean_obj_tag(v___x_934_) == 1)
{
lean_object* v_toSignature_935_; lean_object* v_val_936_; lean_object* v_name_937_; lean_object* v___x_938_; lean_object* v_moduleNames_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_toSignature_935_ = lean_ctor_get(v_origDecl_776_, 0);
lean_inc_ref(v_toSignature_935_);
lean_dec_ref(v_origDecl_776_);
v_val_936_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_934_, 1);
v_name_937_ = lean_ctor_get(v_toSignature_935_, 0);
lean_inc(v_name_937_);
lean_dec_ref(v_toSignature_935_);
v___x_938_ = l_Lean_Environment_header(v_env_885_);
lean_dec_ref(v_env_885_);
v_moduleNames_939_ = lean_ctor_get(v___x_938_, 4);
lean_inc_ref(v_moduleNames_939_);
lean_dec_ref(v___x_938_);
v___x_940_ = l_Lean_MessageData_ofConstName(v_name_937_, v___x_854_);
v___x_941_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
v___x_943_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_MessageData_ofConstName(v_k_787_, v___x_854_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_array_get(v___x_847_, v_moduleNames_939_, v_val_936_);
lean_dec(v_val_936_);
lean_dec_ref(v_moduleNames_939_);
v___x_950_ = l_Lean_MessageData_ofName(v___x_949_);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_953_, v___y_928_, v___y_927_, v___y_926_, v___y_930_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_object* v_toSignature_963_; lean_object* v_name_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v___x_934_);
lean_dec_ref(v_env_885_);
v_toSignature_963_ = lean_ctor_get(v_origDecl_776_, 0);
lean_inc_ref(v_toSignature_963_);
lean_dec_ref(v_origDecl_776_);
v_name_964_ = lean_ctor_get(v_toSignature_963_, 0);
lean_inc(v_name_964_);
lean_dec_ref(v_toSignature_963_);
v___x_965_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_966_ = l_Lean_MessageData_ofConstName(v_name_964_, v___x_854_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_MessageData_ofConstName(v_k_787_, v___x_854_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_973_, v___y_928_, v___y_927_, v___y_926_, v___y_930_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_987_);
v___x_990_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_991_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_989_, v___x_990_);
lean_dec_ref(v___x_989_);
if (v___x_991_ == 0)
{
v___y_926_ = v___y_987_;
v___y_927_ = v___y_986_;
v___y_928_ = v___y_985_;
v___y_929_ = v___y_984_;
v___y_930_ = v___y_988_;
goto v___jp_925_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = l_Lean_Environment_isImportedConst(v_env_885_, v_k_787_);
if (v___x_992_ == 0)
{
uint8_t v___x_993_; 
lean_del_object(v___x_852_);
lean_inc(v_k_787_);
v___x_993_ = l_Lean_getIRPhases(v_env_885_, v_k_787_);
v___y_836_ = v___x_993_;
v___y_837_ = v___y_984_;
v___y_838_ = v___y_985_;
v___y_839_ = v___y_986_;
v___y_840_ = v___y_987_;
v___y_841_ = v___y_988_;
goto v___jp_835_;
}
else
{
v___y_926_ = v___y_987_;
v___y_927_ = v___y_986_;
v___y_928_ = v___y_985_;
v___y_929_ = v___y_984_;
v___y_930_ = v___y_988_;
goto v___jp_925_;
}
}
}
}
else
{
lean_del_object(v___x_852_);
lean_dec(v_k_787_);
v_init_779_ = v___x_790_;
v_x_780_ = v_r_789_;
v___y_781_ = v_snd_850_;
goto _start;
}
v___jp_855_:
{
lean_object* v_toSignature_861_; lean_object* v_name_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v_toSignature_861_ = lean_ctor_get(v_origDecl_776_, 0);
lean_inc_ref(v_toSignature_861_);
lean_dec_ref(v_origDecl_776_);
v_name_862_ = lean_ctor_get(v_toSignature_861_, 0);
lean_inc(v_name_862_);
lean_dec_ref(v_toSignature_861_);
v___x_863_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_864_ = l_Lean_MessageData_ofConstName(v_name_862_, v___x_854_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 7);
lean_ctor_set(v___x_852_, 1, v___x_864_);
lean_ctor_set(v___x_852_, 0, v___x_863_);
v___x_866_ = v___x_852_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_864_);
v___x_866_ = v_reuseFailAlloc_882_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v___x_867_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_ofConstName(v_k_787_, v___x_854_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_872_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
else
{
lean_dec(v_r_789_);
lean_dec(v_k_787_);
lean_dec_ref(v_origDecl_776_);
return v___x_848_;
}
v___jp_791_:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_793_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; uint8_t v___x_799_; lean_object* v___x_800_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = lean_unbox(v_a_798_);
v___x_800_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_787_, v___x_799_, v___y_795_);
lean_dec(v_k_787_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
if (lean_obj_tag(v_a_801_) == 1)
{
lean_object* v_val_802_; uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_val_802_ = lean_ctor_get(v_a_801_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v_a_801_, 1);
v___x_803_ = lean_unbox(v_a_798_);
lean_dec(v_a_798_);
v___x_804_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_803_);
v___x_805_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_804_, v_val_802_, v_pu_775_);
lean_dec(v_val_802_);
lean_inc_ref(v_origDecl_776_);
v___x_806_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_775_, v_origDecl_776_, v_isMeta_777_, v_isPublic_778_, v___x_805_, v___y_794_, v___y_793_, v___y_792_, v___y_796_, v___y_795_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_snd_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v_snd_808_ = lean_ctor_get(v_a_807_, 1);
lean_inc(v_snd_808_);
lean_dec(v_a_807_);
v_init_779_ = v___x_790_;
v_x_780_ = v_r_789_;
v___y_781_ = v_snd_808_;
goto _start;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_r_789_);
lean_dec_ref(v_origDecl_776_);
v_a_810_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_806_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_806_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_dec(v_a_801_);
lean_dec(v_a_798_);
v_init_779_ = v___x_790_;
v_x_780_ = v_r_789_;
v___y_781_ = v___y_794_;
goto _start;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_a_798_);
lean_dec(v___y_794_);
lean_dec(v_r_789_);
lean_dec_ref(v_origDecl_776_);
v_a_819_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_800_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_800_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___y_794_);
lean_dec(v_r_789_);
lean_dec(v_k_787_);
lean_dec_ref(v_origDecl_776_);
v_a_827_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_797_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_797_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
v___jp_835_:
{
uint8_t v___x_842_; uint8_t v___x_843_; 
v___x_842_ = 2;
v___x_843_ = l_Lean_instBEqIRPhases_beq(v___y_836_, v___x_842_);
if (v___x_843_ == 0)
{
if (v_isPublic_778_ == 0)
{
lean_dec(v_k_787_);
v_init_779_ = v___x_790_;
v_x_780_ = v_r_789_;
v___y_781_ = v___y_837_;
goto _start;
}
else
{
uint8_t v___x_845_; 
v___x_845_ = l_Lean_isPrivateName(v_k_787_);
if (v___x_845_ == 0)
{
lean_dec(v_k_787_);
v_init_779_ = v___x_790_;
v_x_780_ = v_r_789_;
v___y_781_ = v___y_837_;
goto _start;
}
else
{
v___y_792_ = v___y_839_;
v___y_793_ = v___y_838_;
v___y_794_ = v___y_837_;
v___y_795_ = v___y_841_;
v___y_796_ = v___y_840_;
goto v___jp_791_;
}
}
}
else
{
v___y_792_ = v___y_839_;
v___y_793_ = v___y_838_;
v___y_794_ = v___y_837_;
v___y_795_ = v___y_841_;
v___y_796_ = v___y_840_;
goto v___jp_791_;
}
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v_origDecl_776_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_init_779_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___y_781_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t v_pu_1069_, lean_object* v_origDecl_1070_, uint8_t v_isMeta_1071_, uint8_t v_isPublic_1072_, lean_object* v_code_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = l_Lean_NameSet_empty;
v___x_1081_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_1069_, v_code_1073_, v___x_1080_);
v___x_1082_ = lean_box(0);
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_1069_, v_origDecl_1070_, v_isMeta_1071_, v_isPublic_1072_, v___x_1082_, v___x_1081_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1100_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1100_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1100_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_snd_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_snd_1088_ = lean_ctor_get(v_a_1084_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_a_1084_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_a_1084_, 0);
lean_dec(v_unused_1099_);
v___x_1090_ = v_a_1084_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_snd_1088_);
lean_dec(v_a_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1082_);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_snd_1088_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1093_);
v___x_1095_ = v___x_1086_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1083_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1083_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object* v_pu_1109_, lean_object* v_origDecl_1110_, lean_object* v_isMeta_1111_, lean_object* v_isPublic_1112_, lean_object* v_code_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_pu_boxed_1120_; uint8_t v_isMeta_boxed_1121_; uint8_t v_isPublic_boxed_1122_; lean_object* v_res_1123_; 
v_pu_boxed_1120_ = lean_unbox(v_pu_1109_);
v_isMeta_boxed_1121_ = lean_unbox(v_isMeta_1111_);
v_isPublic_boxed_1122_ = lean_unbox(v_isPublic_1112_);
v_res_1123_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_boxed_1120_, v_origDecl_1110_, v_isMeta_boxed_1121_, v_isPublic_boxed_1122_, v_code_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t v_pu_1124_, lean_object* v_origDecl_1125_, uint8_t v_isMeta_1126_, uint8_t v_isPublic_1127_, lean_object* v_decl_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_value_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v_value_1135_ = lean_ctor_get(v_decl_1128_, 1);
lean_inc_ref(v_value_1135_);
lean_dec_ref(v_decl_1128_);
v___x_1136_ = lean_box(v_pu_1124_);
v___x_1137_ = lean_box(v_isMeta_1126_);
v___x_1138_ = lean_box(v_isPublic_1127_);
v___f_1139_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1139_, 0, v___x_1136_);
lean_closure_set(v___f_1139_, 1, v_origDecl_1125_);
lean_closure_set(v___f_1139_, 2, v___x_1137_);
lean_closure_set(v___f_1139_, 3, v___x_1138_);
v___x_1140_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_1139_, v_value_1135_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object* v_pu_1141_, lean_object* v_origDecl_1142_, lean_object* v_isMeta_1143_, lean_object* v_isPublic_1144_, lean_object* v_decl_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_pu_boxed_1152_; uint8_t v_isMeta_boxed_1153_; uint8_t v_isPublic_boxed_1154_; lean_object* v_res_1155_; 
v_pu_boxed_1152_ = lean_unbox(v_pu_1141_);
v_isMeta_boxed_1153_ = lean_unbox(v_isMeta_1143_);
v_isPublic_boxed_1154_ = lean_unbox(v_isPublic_1144_);
v_res_1155_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_boxed_1152_, v_origDecl_1142_, v_isMeta_boxed_1153_, v_isPublic_boxed_1154_, v_decl_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object* v_pu_1156_, lean_object* v_origDecl_1157_, lean_object* v_isMeta_1158_, lean_object* v_isPublic_1159_, lean_object* v_init_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v_pu_boxed_1168_; uint8_t v_isMeta_boxed_1169_; uint8_t v_isPublic_boxed_1170_; lean_object* v_res_1171_; 
v_pu_boxed_1168_ = lean_unbox(v_pu_1156_);
v_isMeta_boxed_1169_ = lean_unbox(v_isMeta_1158_);
v_isPublic_boxed_1170_ = lean_unbox(v_isPublic_1159_);
v_res_1171_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_1168_, v_origDecl_1157_, v_isMeta_boxed_1169_, v_isPublic_boxed_1170_, v_init_1160_, v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object* v_opt_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1173_);
v___x_1176_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1175_, v_opt_1172_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = lean_box(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1179_, v___y_1180_);
lean_dec_ref(v___y_1180_);
lean_dec_ref(v_opt_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1183_, lean_object* v_origDecl_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1250_; 
v___x_1190_ = lean_st_ref_get(v_a_1188_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1193_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1192_, v_a_1187_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1250_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1250_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1249_; 
v___x_1198_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1199_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1198_, v_a_1187_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1249_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1249_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1209_; uint8_t v_isModule_1210_; 
v___x_1209_ = l_Lean_Environment_header(v_env_1191_);
lean_dec_ref(v_env_1191_);
v_isModule_1210_ = lean_ctor_get_uint8(v___x_1209_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1209_);
if (v_isModule_1210_ == 0)
{
lean_dec(v_a_1200_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1194_);
lean_dec_ref(v_origDecl_1184_);
goto v___jp_1204_;
}
else
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_unbox(v_a_1194_);
lean_dec(v_a_1194_);
if (v___x_1211_ == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_unbox(v_a_1200_);
if (v___x_1212_ == 0)
{
lean_dec(v_a_1200_);
lean_del_object(v___x_1196_);
lean_dec_ref(v_origDecl_1184_);
goto v___jp_1204_;
}
else
{
lean_object* v___x_1213_; lean_object* v_toSignature_1214_; lean_object* v_env_1215_; lean_object* v_name_1216_; uint8_t v___x_1217_; uint8_t v___y_1219_; uint8_t v___x_1241_; uint8_t v___x_1242_; 
lean_del_object(v___x_1202_);
v___x_1213_ = lean_st_ref_get(v_a_1188_);
v_toSignature_1214_ = lean_ctor_get(v_origDecl_1184_, 0);
v_env_1215_ = lean_ctor_get(v___x_1213_, 0);
lean_inc_ref(v_env_1215_);
lean_dec(v___x_1213_);
v_name_1216_ = lean_ctor_get(v_toSignature_1214_, 0);
lean_inc(v_name_1216_);
v___x_1217_ = l_Lean_getIRPhases(v_env_1215_, v_name_1216_);
v___x_1241_ = 2;
v___x_1242_ = l_Lean_instBEqIRPhases_beq(v___x_1217_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
lean_del_object(v___x_1196_);
v___x_1243_ = l_Lean_isPrivateName(v_name_1216_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_unbox(v_a_1200_);
lean_dec(v_a_1200_);
v___y_1219_ = v___x_1244_;
goto v___jp_1218_;
}
else
{
lean_dec(v_a_1200_);
v___y_1219_ = v___x_1242_;
goto v___jp_1218_;
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
lean_dec(v_a_1200_);
lean_dec_ref(v_origDecl_1184_);
v___x_1245_ = lean_box(0);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1245_);
v___x_1247_ = v___x_1196_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
v___jp_1218_:
{
uint8_t v___x_1220_; uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = 1;
v___x_1221_ = l_Lean_instBEqIRPhases_beq(v___x_1217_, v___x_1220_);
v___x_1222_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1184_);
v___x_1223_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1183_, v_origDecl_1184_, v___x_1221_, v___y_1219_, v_origDecl_1184_, v___x_1222_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1232_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_fst_1228_; lean_object* v___x_1230_; 
v_fst_1228_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_fst_1228_);
lean_dec(v_a_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_fst_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_fst_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1223_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1223_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1200_);
lean_del_object(v___x_1196_);
lean_dec_ref(v_origDecl_1184_);
goto v___jp_1204_;
}
}
v___jp_1204_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1205_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1251_, lean_object* v_origDecl_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
uint8_t v_pu_boxed_1258_; lean_object* v_res_1259_; 
v_pu_boxed_1258_ = lean_unbox(v_pu_1251_);
v_res_1259_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1258_, v_origDecl_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1260_, v___y_1263_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v_opt_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0(uint8_t v_isExporting_1274_, lean_object* v___x_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_env_1284_; lean_object* v_nextMacroScope_1285_; lean_object* v_ngen_1286_; lean_object* v_auxDeclNGen_1287_; lean_object* v_traceState_1288_; lean_object* v_recordedDeps_1289_; lean_object* v_messages_1290_; lean_object* v_infoState_1291_; lean_object* v_snapshotTasks_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1304_; 
v___x_1283_ = lean_st_ref_take(v___y_1281_);
v_env_1284_ = lean_ctor_get(v___x_1283_, 0);
v_nextMacroScope_1285_ = lean_ctor_get(v___x_1283_, 1);
v_ngen_1286_ = lean_ctor_get(v___x_1283_, 2);
v_auxDeclNGen_1287_ = lean_ctor_get(v___x_1283_, 3);
v_traceState_1288_ = lean_ctor_get(v___x_1283_, 4);
v_recordedDeps_1289_ = lean_ctor_get(v___x_1283_, 6);
v_messages_1290_ = lean_ctor_get(v___x_1283_, 7);
v_infoState_1291_ = lean_ctor_get(v___x_1283_, 8);
v_snapshotTasks_1292_ = lean_ctor_get(v___x_1283_, 9);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; 
v_unused_1305_ = lean_ctor_get(v___x_1283_, 5);
lean_dec(v_unused_1305_);
v___x_1294_ = v___x_1283_;
v_isShared_1295_ = v_isSharedCheck_1304_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_snapshotTasks_1292_);
lean_inc(v_infoState_1291_);
lean_inc(v_messages_1290_);
lean_inc(v_recordedDeps_1289_);
lean_inc(v_traceState_1288_);
lean_inc(v_auxDeclNGen_1287_);
lean_inc(v_ngen_1286_);
lean_inc(v_nextMacroScope_1285_);
lean_inc(v_env_1284_);
lean_dec(v___x_1283_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1304_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = l_Lean_Environment_setExporting(v_env_1284_, v_isExporting_1274_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 5, v___x_1275_);
lean_ctor_set(v___x_1294_, 0, v___x_1297_);
v___x_1299_ = v___x_1294_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_nextMacroScope_1285_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_ngen_1286_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_auxDeclNGen_1287_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_traceState_1288_);
lean_ctor_set(v_reuseFailAlloc_1303_, 5, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1303_, 6, v_recordedDeps_1289_);
lean_ctor_set(v_reuseFailAlloc_1303_, 7, v_messages_1290_);
lean_ctor_set(v_reuseFailAlloc_1303_, 8, v_infoState_1291_);
lean_ctor_set(v_reuseFailAlloc_1303_, 9, v_snapshotTasks_1292_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_st_ref_put(v___y_1281_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1296_);
lean_ctor_set(v___x_1301_, 1, v___y_1277_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0___boxed(lean_object* v_isExporting_1306_, lean_object* v___x_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_isExporting_boxed_1315_; lean_object* v_res_1316_; 
v_isExporting_boxed_1315_ = lean_unbox(v_isExporting_1306_);
v_res_1316_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0(v_isExporting_boxed_1315_, v___x_1307_, v_x_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_x_1308_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(lean_object* v___f_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v_a_x3f_1323_){
_start:
{
if (lean_obj_tag(v_a_x3f_1323_) == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_box(0);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1326_ = lean_apply_7(v___f_1317_, v___x_1325_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, lean_box(0));
return v___x_1326_;
}
else
{
lean_object* v_val_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v___y_1318_);
v_val_1327_ = lean_ctor_get(v_a_x3f_1323_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_a_x3f_1323_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1329_ = v_a_x3f_1323_;
v_isShared_1330_ = v_isSharedCheck_1337_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_val_1327_);
lean_dec(v_a_x3f_1323_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1337_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1334_; 
v_fst_1331_ = lean_ctor_get(v_val_1327_, 0);
lean_inc(v_fst_1331_);
v_snd_1332_ = lean_ctor_get(v_val_1327_, 1);
lean_inc(v_snd_1332_);
lean_dec(v_val_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_fst_1331_);
v___x_1334_ = v___x_1329_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_fst_1331_);
v___x_1334_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; 
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1335_ = lean_apply_7(v___f_1317_, v___x_1334_, v_snd_1332_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, lean_box(0));
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1___boxed(lean_object* v___f_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v_a_x3f_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(v___f_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v_a_x3f_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(lean_object* v_x_1347_, uint8_t v_isExporting_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v_env_1356_; lean_object* v___x_1357_; uint8_t v_isModule_1358_; 
v___x_1355_ = lean_st_ref_get(v___y_1353_);
v_env_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_env_1356_);
lean_dec(v___x_1355_);
v___x_1357_ = l_Lean_Environment_header(v_env_1356_);
v_isModule_1358_ = lean_ctor_get_uint8(v___x_1357_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1357_);
if (v_isModule_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v_env_1356_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1359_ = lean_apply_6(v_x_1347_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
return v___x_1359_;
}
else
{
uint8_t v_isExporting_1360_; 
v_isExporting_1360_ = lean_ctor_get_uint8(v_env_1356_, sizeof(void*)*13);
lean_dec_ref(v_env_1356_);
if (v_isExporting_1348_ == 0)
{
if (v_isExporting_1360_ == 0)
{
lean_object* v___x_1440_; 
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1440_ = lean_apply_6(v_x_1347_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
return v___x_1440_;
}
else
{
goto v___jp_1361_;
}
}
else
{
if (v_isExporting_1360_ == 0)
{
goto v___jp_1361_;
}
else
{
lean_object* v___x_1441_; 
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1441_ = lean_apply_6(v_x_1347_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
return v___x_1441_;
}
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v_env_1363_; lean_object* v_nextMacroScope_1364_; lean_object* v_ngen_1365_; lean_object* v_auxDeclNGen_1366_; lean_object* v_traceState_1367_; lean_object* v_recordedDeps_1368_; lean_object* v_messages_1369_; lean_object* v_infoState_1370_; lean_object* v_snapshotTasks_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1438_; 
v___x_1362_ = lean_st_ref_take(v___y_1353_);
v_env_1363_ = lean_ctor_get(v___x_1362_, 0);
v_nextMacroScope_1364_ = lean_ctor_get(v___x_1362_, 1);
v_ngen_1365_ = lean_ctor_get(v___x_1362_, 2);
v_auxDeclNGen_1366_ = lean_ctor_get(v___x_1362_, 3);
v_traceState_1367_ = lean_ctor_get(v___x_1362_, 4);
v_recordedDeps_1368_ = lean_ctor_get(v___x_1362_, 6);
v_messages_1369_ = lean_ctor_get(v___x_1362_, 7);
v_infoState_1370_ = lean_ctor_get(v___x_1362_, 8);
v_snapshotTasks_1371_ = lean_ctor_get(v___x_1362_, 9);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v___x_1362_, 5);
lean_dec(v_unused_1439_);
v___x_1373_ = v___x_1362_;
v_isShared_1374_ = v_isSharedCheck_1438_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snapshotTasks_1371_);
lean_inc(v_infoState_1370_);
lean_inc(v_messages_1369_);
lean_inc(v_recordedDeps_1368_);
lean_inc(v_traceState_1367_);
lean_inc(v_auxDeclNGen_1366_);
lean_inc(v_ngen_1365_);
lean_inc(v_nextMacroScope_1364_);
lean_inc(v_env_1363_);
lean_dec(v___x_1362_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1438_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___f_1378_; lean_object* v___x_1380_; 
v___x_1375_ = l_Lean_Environment_setExporting(v_env_1363_, v_isExporting_1348_);
v___x_1376_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1377_ = lean_box(v_isExporting_1360_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1378_, 0, v___x_1377_);
lean_closure_set(v___f_1378_, 1, v___x_1376_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 5, v___x_1376_);
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1380_ = v___x_1373_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_nextMacroScope_1364_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_ngen_1365_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_auxDeclNGen_1366_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_traceState_1367_);
lean_ctor_set(v_reuseFailAlloc_1437_, 5, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1437_, 6, v_recordedDeps_1368_);
lean_ctor_set(v_reuseFailAlloc_1437_, 7, v_messages_1369_);
lean_ctor_set(v_reuseFailAlloc_1437_, 8, v_infoState_1370_);
lean_ctor_set(v_reuseFailAlloc_1437_, 9, v_snapshotTasks_1371_);
v___x_1380_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v_r_1382_; 
v___x_1381_ = lean_st_ref_put(v___y_1353_, v___x_1380_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
v_r_1382_ = lean_apply_6(v_x_1347_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
if (lean_obj_tag(v_r_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1417_; 
v_a_1383_ = lean_ctor_get(v_r_1382_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_r_1382_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1385_ = v_r_1382_;
v_isShared_1386_ = v_isSharedCheck_1417_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v_r_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1417_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
lean_inc(v_a_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(v___f_1378_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___x_1388_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1407_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1407_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1407_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1405_; 
v_fst_1394_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_fst_1394_);
lean_dec(v_a_1383_);
v_snd_1395_ = lean_ctor_get(v_a_1390_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_a_1390_, 0);
lean_dec(v_unused_1406_);
v___x_1397_ = v_a_1390_;
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_dec(v_a_1390_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_fst_1394_);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_fst_1394_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1395_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_a_1383_);
v_a_1408_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1389_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1389_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1418_ = lean_ctor_get(v_r_1382_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v_r_1382_, 1);
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(v___f_1378_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___x_1419_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1428_);
v___x_1422_ = v___x_1420_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v___x_1420_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 1);
lean_ctor_set(v___x_1422_, 0, v_a_1418_);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1418_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_a_1418_);
v_a_1429_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1420_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1420_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___boxed(lean_object* v_x_1442_, lean_object* v_isExporting_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_isExporting_boxed_1450_; lean_object* v_res_1451_; 
v_isExporting_boxed_1450_ = lean_unbox(v_isExporting_1443_);
v_res_1451_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(v_x_1442_, v_isExporting_boxed_1450_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_00_u03b1_1452_, lean_object* v_x_1453_, uint8_t v_isExporting_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(v_x_1453_, v_isExporting_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_00_u03b1_1462_, lean_object* v_x_1463_, lean_object* v_isExporting_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_isExporting_boxed_1471_; lean_object* v_res_1472_; 
v_isExporting_boxed_1471_ = lean_unbox(v_isExporting_1464_);
v_res_1472_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_00_u03b1_1462_, v_x_1463_, v_isExporting_boxed_1471_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object* v_opt_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1477_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1475_);
v___x_1478_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1477_, v_opt_1473_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = lean_box(v___x_1478_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___y_1474_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_opt_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_opt_1482_, v___y_1483_, v___y_1484_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v_opt_1482_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(lean_object* v_a_1487_, lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1488_) == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
else
{
lean_object* v_key_1490_; lean_object* v_value_1491_; lean_object* v_tail_1492_; uint8_t v___x_1493_; 
v_key_1490_ = lean_ctor_get(v_x_1488_, 0);
v_value_1491_ = lean_ctor_get(v_x_1488_, 1);
v_tail_1492_ = lean_ctor_get(v_x_1488_, 2);
v___x_1493_ = lean_name_eq(v_key_1490_, v_a_1487_);
if (v___x_1493_ == 0)
{
v_x_1488_ = v_tail_1492_;
goto _start;
}
else
{
lean_object* v___x_1495_; 
lean_inc(v_value_1491_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_value_1491_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_a_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(v_a_1496_, v_x_1497_);
lean_dec(v_x_1497_);
lean_dec(v_a_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(lean_object* v_m_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_buckets_1501_; lean_object* v___x_1502_; uint64_t v___y_1504_; 
v_buckets_1501_ = lean_ctor_get(v_m_1499_, 1);
v___x_1502_ = lean_array_get_size(v_buckets_1501_);
if (lean_obj_tag(v_a_1500_) == 0)
{
uint64_t v___x_1518_; 
v___x_1518_ = 1723ULL;
v___y_1504_ = v___x_1518_;
goto v___jp_1503_;
}
else
{
uint64_t v_hash_1519_; 
v_hash_1519_ = lean_ctor_get_uint64(v_a_1500_, sizeof(void*)*2);
v___y_1504_ = v_hash_1519_;
goto v___jp_1503_;
}
v___jp_1503_:
{
uint64_t v___x_1505_; uint64_t v___x_1506_; uint64_t v_fold_1507_; uint64_t v___x_1508_; uint64_t v___x_1509_; uint64_t v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1505_ = 32ULL;
v___x_1506_ = lean_uint64_shift_right(v___y_1504_, v___x_1505_);
v_fold_1507_ = lean_uint64_xor(v___y_1504_, v___x_1506_);
v___x_1508_ = 16ULL;
v___x_1509_ = lean_uint64_shift_right(v_fold_1507_, v___x_1508_);
v___x_1510_ = lean_uint64_xor(v_fold_1507_, v___x_1509_);
v___x_1511_ = lean_uint64_to_usize(v___x_1510_);
v___x_1512_ = lean_usize_of_nat(v___x_1502_);
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_sub(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_usize_land(v___x_1511_, v___x_1514_);
v___x_1516_ = lean_array_uget_borrowed(v_buckets_1501_, v___x_1515_);
v___x_1517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(v_a_1500_, v___x_1516_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___boxed(lean_object* v_m_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(v_m_1520_, v_a_1521_);
lean_dec(v_a_1521_);
lean_dec_ref(v_m_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___lam__0(lean_object* v___x_1523_, lean_object* v_entry_1524_, lean_object* v_s_1525_){
_start:
{
lean_object* v_addEntryFn_1526_; lean_object* v_importedEntries_1527_; lean_object* v_state_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1536_; 
v_addEntryFn_1526_ = lean_ctor_get(v___x_1523_, 3);
lean_inc(v_addEntryFn_1526_);
lean_dec_ref(v___x_1523_);
v_importedEntries_1527_ = lean_ctor_get(v_s_1525_, 0);
v_state_1528_ = lean_ctor_get(v_s_1525_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_s_1525_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1530_ = v_s_1525_;
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_state_1528_);
lean_inc(v_importedEntries_1527_);
lean_dec(v_s_1525_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_state_1532_; lean_object* v___x_1534_; 
v_state_1532_ = lean_apply_2(v_addEntryFn_1526_, v_state_1528_, v_entry_1524_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_state_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_importedEntries_1527_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_state_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(lean_object* v_cls_1537_, lean_object* v_msg_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_ref_1545_; lean_object* v___x_1546_; lean_object* v_env_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_ref_1545_ = lean_ctor_get(v___y_1542_, 2);
v___x_1546_ = lean_st_ref_get(v___y_1543_);
v_env_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc_ref(v_env_1547_);
lean_dec(v___x_1546_);
v___x_1548_ = lean_st_ref_get(v___y_1541_);
v___x_1549_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1540_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1610_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1610_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1610_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_lctx_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1608_; 
v_lctx_1554_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1548_, 1);
lean_dec(v_unused_1609_);
v___x_1556_ = v___x_1548_;
v_isShared_1557_ = v_isSharedCheck_1608_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_lctx_1554_);
lean_dec(v___x_1548_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1608_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1558_ = lean_unbox(v_a_1550_);
lean_dec(v_a_1550_);
v___x_1559_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1554_, v___x_1558_);
lean_dec_ref(v_lctx_1554_);
v___x_1560_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1542_);
v___x_1561_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_1562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1562_, 0, v_env_1547_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
lean_ctor_set(v___x_1562_, 2, v___x_1559_);
lean_ctor_set(v___x_1562_, 3, v___x_1560_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 3);
lean_ctor_set(v___x_1556_, 1, v_msg_1538_);
lean_ctor_set(v___x_1556_, 0, v___x_1562_);
v___x_1564_ = v___x_1556_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_msg_1538_);
v___x_1564_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v_traceState_1566_; lean_object* v_env_1567_; lean_object* v_nextMacroScope_1568_; lean_object* v_ngen_1569_; lean_object* v_auxDeclNGen_1570_; lean_object* v_cache_1571_; lean_object* v_recordedDeps_1572_; lean_object* v_messages_1573_; lean_object* v_infoState_1574_; lean_object* v_snapshotTasks_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1606_; 
v___x_1565_ = lean_st_ref_take(v___y_1543_);
v_traceState_1566_ = lean_ctor_get(v___x_1565_, 4);
v_env_1567_ = lean_ctor_get(v___x_1565_, 0);
v_nextMacroScope_1568_ = lean_ctor_get(v___x_1565_, 1);
v_ngen_1569_ = lean_ctor_get(v___x_1565_, 2);
v_auxDeclNGen_1570_ = lean_ctor_get(v___x_1565_, 3);
v_cache_1571_ = lean_ctor_get(v___x_1565_, 5);
v_recordedDeps_1572_ = lean_ctor_get(v___x_1565_, 6);
v_messages_1573_ = lean_ctor_get(v___x_1565_, 7);
v_infoState_1574_ = lean_ctor_get(v___x_1565_, 8);
v_snapshotTasks_1575_ = lean_ctor_get(v___x_1565_, 9);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1577_ = v___x_1565_;
v_isShared_1578_ = v_isSharedCheck_1606_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_snapshotTasks_1575_);
lean_inc(v_infoState_1574_);
lean_inc(v_messages_1573_);
lean_inc(v_recordedDeps_1572_);
lean_inc(v_cache_1571_);
lean_inc(v_traceState_1566_);
lean_inc(v_auxDeclNGen_1570_);
lean_inc(v_ngen_1569_);
lean_inc(v_nextMacroScope_1568_);
lean_inc(v_env_1567_);
lean_dec(v___x_1565_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1606_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint64_t v_tid_1579_; lean_object* v_traces_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1605_; 
v_tid_1579_ = lean_ctor_get_uint64(v_traceState_1566_, sizeof(void*)*1);
v_traces_1580_ = lean_ctor_get(v_traceState_1566_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_traceState_1566_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1582_ = v_traceState_1566_;
v_isShared_1583_ = v_isSharedCheck_1605_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_traces_1580_);
lean_dec(v_traceState_1566_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1605_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; double v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_1587_ = 0;
v___x_1588_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1589_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1589_, 0, v_cls_1537_);
lean_ctor_set(v___x_1589_, 1, v___x_1585_);
lean_ctor_set(v___x_1589_, 2, v___x_1588_);
lean_ctor_set_float(v___x_1589_, sizeof(void*)*3, v___x_1586_);
lean_ctor_set_float(v___x_1589_, sizeof(void*)*3 + 8, v___x_1586_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*3 + 16, v___x_1587_);
v___x_1590_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_1591_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1564_);
lean_ctor_set(v___x_1591_, 2, v___x_1590_);
lean_inc(v_ref_1545_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_ref_1545_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_PersistentArray_push___redArg(v_traces_1580_, v___x_1592_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1593_);
v___x_1595_ = v___x_1582_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1593_);
lean_ctor_set_uint64(v_reuseFailAlloc_1604_, sizeof(void*)*1, v_tid_1579_);
v___x_1595_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v___x_1595_);
v___x_1597_ = v___x_1577_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_env_1567_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_nextMacroScope_1568_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_ngen_1569_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_auxDeclNGen_1570_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v_cache_1571_);
lean_ctor_set(v_reuseFailAlloc_1603_, 6, v_recordedDeps_1572_);
lean_ctor_set(v_reuseFailAlloc_1603_, 7, v_messages_1573_);
lean_ctor_set(v_reuseFailAlloc_1603_, 8, v_infoState_1574_);
lean_ctor_set(v_reuseFailAlloc_1603_, 9, v_snapshotTasks_1575_);
v___x_1597_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1598_ = lean_st_ref_put(v___y_1543_, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1584_);
lean_ctor_set(v___x_1599_, 1, v___y_1539_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1599_);
v___x_1601_ = v___x_1552_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v___x_1548_);
lean_dec_ref(v_env_1547_);
lean_dec(v___y_1539_);
lean_dec_ref(v_msg_1538_);
lean_dec(v_cls_1537_);
v_a_1611_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1549_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1549_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6___boxed(lean_object* v_cls_1619_, lean_object* v_msg_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(v_cls_1619_, v_msg_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_keys_1628_, lean_object* v_i_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_array_get_size(v_keys_1628_);
v___x_1632_ = lean_nat_dec_lt(v_i_1629_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_dec(v_i_1629_);
return v___x_1632_;
}
else
{
lean_object* v_k_x27_1633_; uint8_t v___x_1634_; 
v_k_x27_1633_ = lean_array_fget_borrowed(v_keys_1628_, v_i_1629_);
v___x_1634_ = l_Lean_instBEqExtraModUse_beq(v_k_1630_, v_k_x27_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_i_1629_, v___x_1635_);
lean_dec(v_i_1629_);
v_i_1629_ = v___x_1636_;
goto _start;
}
else
{
lean_dec(v_i_1629_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1638_, lean_object* v_i_1639_, lean_object* v_k_1640_){
_start:
{
uint8_t v_res_1641_; lean_object* v_r_1642_; 
v_res_1641_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(v_keys_1638_, v_i_1639_, v_k_1640_);
lean_dec_ref(v_k_1640_);
lean_dec_ref(v_keys_1638_);
v_r_1642_ = lean_box(v_res_1641_);
return v_r_1642_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_x_1643_, size_t v_x_1644_, lean_object* v_x_1645_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_es_1646_; lean_object* v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v_j_1650_; lean_object* v___x_1651_; 
v_es_1646_ = lean_ctor_get(v_x_1643_, 0);
v___x_1647_ = lean_box(2);
v___x_1648_ = ((size_t)31ULL);
v___x_1649_ = lean_usize_land(v_x_1644_, v___x_1648_);
v_j_1650_ = lean_usize_to_nat(v___x_1649_);
v___x_1651_ = lean_array_get_borrowed(v___x_1647_, v_es_1646_, v_j_1650_);
lean_dec(v_j_1650_);
switch(lean_obj_tag(v___x_1651_))
{
case 0:
{
lean_object* v_key_1652_; uint8_t v___x_1653_; 
v_key_1652_ = lean_ctor_get(v___x_1651_, 0);
v___x_1653_ = l_Lean_instBEqExtraModUse_beq(v_x_1645_, v_key_1652_);
return v___x_1653_;
}
case 1:
{
lean_object* v_node_1654_; size_t v___x_1655_; size_t v___x_1656_; 
v_node_1654_ = lean_ctor_get(v___x_1651_, 0);
v___x_1655_ = ((size_t)5ULL);
v___x_1656_ = lean_usize_shift_right(v_x_1644_, v___x_1655_);
v_x_1643_ = v_node_1654_;
v_x_1644_ = v___x_1656_;
goto _start;
}
default: 
{
uint8_t v___x_1658_; 
v___x_1658_ = 0;
return v___x_1658_;
}
}
}
else
{
lean_object* v_ks_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_ks_1659_ = lean_ctor_get(v_x_1643_, 0);
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(v_ks_1659_, v___x_1660_, v_x_1645_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
size_t v_x_27181__boxed_1665_; uint8_t v_res_1666_; lean_object* v_r_1667_; 
v_x_27181__boxed_1665_ = lean_unbox_usize(v_x_1663_);
lean_dec(v_x_1663_);
v_res_1666_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(v_x_1662_, v_x_27181__boxed_1665_, v_x_1664_);
lean_dec_ref(v_x_1664_);
lean_dec_ref(v_x_1662_);
v_r_1667_ = lean_box(v_res_1666_);
return v_r_1667_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
uint64_t v___x_1670_; size_t v___x_1671_; uint8_t v___x_1672_; 
v___x_1670_ = l_Lean_instHashableExtraModUse_hash(v_x_1669_);
v___x_1671_ = lean_uint64_to_usize(v___x_1670_);
v___x_1672_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(v_x_1668_, v___x_1671_, v_x_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
uint8_t v_res_1675_; lean_object* v_r_1676_; 
v_res_1675_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(v_x_1673_, v_x_1674_);
lean_dec_ref(v_x_1674_);
lean_dec_ref(v_x_1673_);
v_r_1676_ = lean_box(v_res_1675_);
return v_r_1676_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1688_ = l_Lean_stringToMessageData(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8(void){
_start:
{
lean_object* v_cls_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_cls_1689_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2));
v___x_1690_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1691_ = l_Lean_Name_append(v___x_1690_, v_cls_1689_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(lean_object* v_mod_1702_, uint8_t v_isMeta_1703_, lean_object* v_hint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v_env_1731_; uint8_t v_isExporting_1732_; lean_object* v_entry_1733_; lean_object* v___x_1734_; lean_object* v_env_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1729_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0);
v___x_1730_ = lean_st_ref_get(v___y_1709_);
v_env_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc_ref(v_env_1731_);
lean_dec(v___x_1730_);
v_isExporting_1732_ = lean_ctor_get_uint8(v_env_1731_, sizeof(void*)*13);
lean_dec_ref(v_env_1731_);
lean_inc(v_mod_1702_);
v_entry_1733_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1733_, 0, v_mod_1702_);
lean_ctor_set_uint8(v_entry_1733_, sizeof(void*)*1, v_isExporting_1732_);
lean_ctor_set_uint8(v_entry_1733_, sizeof(void*)*1 + 1, v_isMeta_1703_);
v___x_1734_ = lean_st_ref_get(v___y_1709_);
v_env_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_env_1735_);
lean_dec(v___x_1734_);
v___x_1736_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1737_ = lean_box(1);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1729_, v___x_1736_, v_env_1735_, v___x_1737_, v___x_1738_);
v___x_1740_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(v___x_1739_, v_entry_1733_);
lean_dec(v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v_toCold_1741_; lean_object* v_options_1742_; lean_object* v_inheritedTraceOptions_1743_; uint8_t v_hasTrace_1744_; lean_object* v___f_1745_; uint8_t v___x_1746_; lean_object* v___y_1748_; lean_object* v___y_1749_; 
v_toCold_1741_ = lean_ctor_get(v___y_1708_, 0);
v_options_1742_ = lean_ctor_get(v_toCold_1741_, 2);
v_inheritedTraceOptions_1743_ = lean_ctor_get(v_toCold_1741_, 11);
v_hasTrace_1744_ = lean_ctor_get_uint8(v_options_1742_, sizeof(void*)*1);
v___f_1745_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_1745_, 0, v___x_1736_);
lean_closure_set(v___f_1745_, 1, v_entry_1733_);
v___x_1746_ = 1;
if (v_hasTrace_1744_ == 0)
{
lean_dec(v_hint_1704_);
lean_dec(v_mod_1702_);
v___y_1748_ = v___y_1705_;
v___y_1749_ = v___y_1709_;
goto v___jp_1747_;
}
else
{
lean_object* v_cls_1767_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_cls_1767_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2));
v___x_1789_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8);
v___x_1790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1743_, v_options_1742_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec(v_hint_1704_);
lean_dec(v_mod_1702_);
v___y_1748_ = v___y_1705_;
v___y_1749_ = v___y_1709_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1791_; lean_object* v___y_1793_; 
v___x_1791_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10);
if (v_isExporting_1732_ == 0)
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15));
v___y_1793_ = v___x_1800_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16));
v___y_1793_ = v___x_1801_;
goto v___jp_1792_;
}
v___jp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_inc_ref(v___y_1793_);
v___x_1794_ = l_Lean_stringToMessageData(v___y_1793_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1791_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
if (v_isMeta_1703_ == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13));
v___y_1776_ = v___x_1797_;
v___y_1777_ = v___x_1798_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14));
v___y_1776_ = v___x_1797_;
v___y_1777_ = v___x_1799_;
goto v___jp_1775_;
}
}
}
v___jp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___y_1769_);
lean_ctor_set(v___x_1771_, 1, v___y_1770_);
v___x_1772_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(v_cls_1767_, v___x_1771_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v_snd_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v_snd_1774_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_snd_1774_);
lean_dec(v_a_1773_);
v___y_1748_ = v_snd_1774_;
v___y_1749_ = v___y_1709_;
goto v___jp_1747_;
}
else
{
lean_dec_ref(v___f_1745_);
return v___x_1772_;
}
}
v___jp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
lean_inc_ref(v___y_1777_);
v___x_1778_ = l_Lean_stringToMessageData(v___y_1777_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___y_1776_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_MessageData_ofName(v_mod_1702_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_Name_isAnonymous(v_hint_1704_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6);
v___x_1786_ = l_Lean_MessageData_ofName(v_hint_1704_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___y_1769_ = v___x_1783_;
v___y_1770_ = v___x_1787_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1788_; 
lean_dec(v_hint_1704_);
v___x_1788_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7);
v___y_1769_ = v___x_1783_;
v___y_1770_ = v___x_1788_;
goto v___jp_1768_;
}
}
}
v___jp_1747_:
{
lean_object* v___x_1750_; lean_object* v_toEnvExtension_1751_; lean_object* v_env_1752_; lean_object* v_nextMacroScope_1753_; lean_object* v_ngen_1754_; lean_object* v_auxDeclNGen_1755_; lean_object* v_traceState_1756_; lean_object* v_recordedDeps_1757_; lean_object* v_messages_1758_; lean_object* v_infoState_1759_; lean_object* v_snapshotTasks_1760_; lean_object* v_asyncMode_1761_; uint8_t v_logWrites_1762_; lean_object* v___x_1763_; 
v___x_1750_ = lean_st_ref_take(v___y_1749_);
v_toEnvExtension_1751_ = lean_ctor_get(v___x_1736_, 0);
v_env_1752_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_env_1752_);
v_nextMacroScope_1753_ = lean_ctor_get(v___x_1750_, 1);
lean_inc(v_nextMacroScope_1753_);
v_ngen_1754_ = lean_ctor_get(v___x_1750_, 2);
lean_inc_ref(v_ngen_1754_);
v_auxDeclNGen_1755_ = lean_ctor_get(v___x_1750_, 3);
lean_inc_ref(v_auxDeclNGen_1755_);
v_traceState_1756_ = lean_ctor_get(v___x_1750_, 4);
lean_inc_ref(v_traceState_1756_);
v_recordedDeps_1757_ = lean_ctor_get(v___x_1750_, 6);
lean_inc_ref(v_recordedDeps_1757_);
v_messages_1758_ = lean_ctor_get(v___x_1750_, 7);
lean_inc_ref(v_messages_1758_);
v_infoState_1759_ = lean_ctor_get(v___x_1750_, 8);
lean_inc_ref(v_infoState_1759_);
v_snapshotTasks_1760_ = lean_ctor_get(v___x_1750_, 9);
lean_inc_ref(v_snapshotTasks_1760_);
lean_dec(v___x_1750_);
v_asyncMode_1761_ = lean_ctor_get(v_toEnvExtension_1751_, 2);
v_logWrites_1762_ = lean_ctor_get_uint8(v_toEnvExtension_1751_, sizeof(void*)*6);
v___x_1763_ = lean_box(0);
if (v_logWrites_1762_ == 0)
{
lean_object* v___x_1764_; 
lean_inc_ref(v_toEnvExtension_1751_);
v___x_1764_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1751_, v_env_1752_, v___f_1745_, v_asyncMode_1761_, v___x_1738_, v___x_1746_);
v___y_1712_ = v_recordedDeps_1757_;
v___y_1713_ = v_traceState_1756_;
v___y_1714_ = v___y_1749_;
v___y_1715_ = v___x_1763_;
v___y_1716_ = v_messages_1758_;
v___y_1717_ = v___y_1748_;
v___y_1718_ = v_ngen_1754_;
v___y_1719_ = v_snapshotTasks_1760_;
v___y_1720_ = v_infoState_1759_;
v___y_1721_ = v_auxDeclNGen_1755_;
v___y_1722_ = v_nextMacroScope_1753_;
v___y_1723_ = v___x_1764_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_inc_ref_n(v_toEnvExtension_1751_, 2);
v___x_1765_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1751_, v_env_1752_);
lean_dec_ref(v_env_1752_);
v___x_1766_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1751_, v___x_1765_, v___f_1745_, v_asyncMode_1761_, v___x_1738_, v___x_1746_);
v___y_1712_ = v_recordedDeps_1757_;
v___y_1713_ = v_traceState_1756_;
v___y_1714_ = v___y_1749_;
v___y_1715_ = v___x_1763_;
v___y_1716_ = v_messages_1758_;
v___y_1717_ = v___y_1748_;
v___y_1718_ = v_ngen_1754_;
v___y_1719_ = v_snapshotTasks_1760_;
v___y_1720_ = v_infoState_1759_;
v___y_1721_ = v_auxDeclNGen_1755_;
v___y_1722_ = v_nextMacroScope_1753_;
v___y_1723_ = v___x_1766_;
goto v___jp_1711_;
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec_ref_known(v_entry_1733_, 1);
lean_dec(v_hint_1704_);
lean_dec(v_mod_1702_);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___y_1705_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
v___jp_1711_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1724_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1725_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1725_, 0, v___y_1723_);
lean_ctor_set(v___x_1725_, 1, v___y_1722_);
lean_ctor_set(v___x_1725_, 2, v___y_1718_);
lean_ctor_set(v___x_1725_, 3, v___y_1721_);
lean_ctor_set(v___x_1725_, 4, v___y_1713_);
lean_ctor_set(v___x_1725_, 5, v___x_1724_);
lean_ctor_set(v___x_1725_, 6, v___y_1712_);
lean_ctor_set(v___x_1725_, 7, v___y_1716_);
lean_ctor_set(v___x_1725_, 8, v___y_1720_);
lean_ctor_set(v___x_1725_, 9, v___y_1719_);
v___x_1726_ = lean_st_ref_put(v___y_1714_, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___y_1715_);
lean_ctor_set(v___x_1727_, 1, v___y_1717_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___boxed(lean_object* v_mod_1805_, lean_object* v_isMeta_1806_, lean_object* v_hint_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_isMeta_boxed_1814_; lean_object* v_res_1815_; 
v_isMeta_boxed_1814_ = lean_unbox(v_isMeta_1806_);
v_res_1815_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(v_mod_1805_, v_isMeta_boxed_1814_, v_hint_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(lean_object* v___x_1816_, lean_object* v_declName_1817_, lean_object* v_as_1818_, size_t v_sz_1819_, size_t v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_usize_dec_lt(v_i_1820_, v_sz_1819_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_declName_1817_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_b_1821_);
lean_ctor_set(v___x_1829_, 1, v___y_1822_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v_modules_1832_; lean_object* v___x_1833_; lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v_toImport_1836_; lean_object* v_module_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1831_ = l_Lean_Environment_header(v___x_1816_);
v_modules_1832_ = lean_ctor_get(v___x_1831_, 3);
lean_inc_ref(v_modules_1832_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1834_ = lean_array_uget_borrowed(v_as_1818_, v_i_1820_);
v___x_1835_ = lean_array_get(v___x_1833_, v_modules_1832_, v_a_1834_);
lean_dec_ref(v_modules_1832_);
v_toImport_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_toImport_1836_);
lean_dec(v___x_1835_);
v_module_1837_ = lean_ctor_get(v_toImport_1836_, 0);
lean_inc(v_module_1837_);
lean_dec_ref(v_toImport_1836_);
v___x_1838_ = lean_box(0);
v___x_1839_ = 0;
lean_inc(v_declName_1817_);
v___x_1840_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(v_module_1837_, v___x_1839_, v_declName_1817_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v_snd_1842_; size_t v___x_1843_; size_t v___x_1844_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v_snd_1842_ = lean_ctor_get(v_a_1841_, 1);
lean_inc(v_snd_1842_);
lean_dec(v_a_1841_);
v___x_1843_ = ((size_t)1ULL);
v___x_1844_ = lean_usize_add(v_i_1820_, v___x_1843_);
v_i_1820_ = v___x_1844_;
v_b_1821_ = v___x_1838_;
v___y_1822_ = v_snd_1842_;
goto _start;
}
else
{
lean_dec(v_declName_1817_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3___boxed(lean_object* v___x_1846_, lean_object* v_declName_1847_, lean_object* v_as_1848_, lean_object* v_sz_1849_, lean_object* v_i_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
size_t v_sz_boxed_1858_; size_t v_i_boxed_1859_; lean_object* v_res_1860_; 
v_sz_boxed_1858_ = lean_unbox_usize(v_sz_1849_);
lean_dec(v_sz_1849_);
v_i_boxed_1859_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(v___x_1846_, v_declName_1847_, v_as_1848_, v_sz_boxed_1858_, v_i_boxed_1859_, v_b_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v_as_1848_);
lean_dec_ref(v___x_1846_);
return v_res_1860_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_declName_1864_, uint8_t v_isMeta_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v_env_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___x_1903_; 
v___x_1872_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0);
v___x_1873_ = lean_st_ref_get(v___y_1870_);
v_env_1878_ = lean_ctor_get(v___x_1873_, 0);
lean_inc_ref(v_env_1878_);
lean_dec(v___x_1873_);
v___x_1903_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1878_, v_declName_1864_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_dec_ref(v_env_1878_);
lean_dec(v_declName_1864_);
goto v___jp_1874_;
}
else
{
lean_object* v_val_1904_; lean_object* v___x_1905_; lean_object* v_modules_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_val_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = l_Lean_Environment_header(v_env_1878_);
v_modules_1906_ = lean_ctor_get(v___x_1905_, 3);
lean_inc_ref(v_modules_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = lean_array_get_size(v_modules_1906_);
v___x_1908_ = lean_nat_dec_lt(v_val_1904_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_dec_ref(v_modules_1906_);
lean_dec(v_val_1904_);
lean_dec_ref(v_env_1878_);
lean_dec(v_declName_1864_);
goto v___jp_1874_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___y_1912_; 
v___x_1909_ = lean_array_fget(v_modules_1906_, v_val_1904_);
lean_dec(v_val_1904_);
lean_dec_ref(v_modules_1906_);
v___x_1910_ = lean_st_ref_get(v___y_1870_);
if (v_isMeta_1865_ == 0)
{
lean_dec(v___x_1910_);
v___y_1912_ = v_isMeta_1865_;
goto v___jp_1911_;
}
else
{
lean_object* v_env_1925_; uint8_t v___x_1926_; 
v_env_1925_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_env_1925_);
lean_dec(v___x_1910_);
lean_inc(v_declName_1864_);
v___x_1926_ = l_Lean_isMarkedMeta(v_env_1925_, v_declName_1864_);
if (v___x_1926_ == 0)
{
v___y_1912_ = v_isMeta_1865_;
goto v___jp_1911_;
}
else
{
uint8_t v___x_1927_; 
v___x_1927_ = 0;
v___y_1912_ = v___x_1927_;
goto v___jp_1911_;
}
}
v___jp_1911_:
{
lean_object* v_toImport_1913_; lean_object* v_module_1914_; lean_object* v___x_1915_; 
v_toImport_1913_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_toImport_1913_);
lean_dec(v___x_1909_);
v_module_1914_ = lean_ctor_get(v_toImport_1913_, 0);
lean_inc(v_module_1914_);
lean_dec_ref(v_toImport_1913_);
lean_inc(v_declName_1864_);
v___x_1915_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(v_module_1914_, v___y_1912_, v_declName_1864_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v_snd_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v_snd_1917_ = lean_ctor_get(v_a_1916_, 1);
lean_inc(v_snd_1917_);
lean_dec(v_a_1916_);
v___x_1918_ = l_Lean_indirectModUseExt;
v___x_1919_ = lean_box(1);
v___x_1920_ = lean_box(0);
lean_inc_ref(v_env_1878_);
v___x_1921_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1872_, v___x_1918_, v_env_1878_, v___x_1919_, v___x_1920_);
v___x_1922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(v___x_1921_, v_declName_1864_);
lean_dec(v___x_1921_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1));
v___y_1880_ = v_snd_1917_;
v___y_1881_ = v___x_1923_;
goto v___jp_1879_;
}
else
{
lean_object* v_val_1924_; 
v_val_1924_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v___x_1922_, 1);
v___y_1880_ = v_snd_1917_;
v___y_1881_ = v_val_1924_;
goto v___jp_1879_;
}
}
else
{
lean_dec_ref(v_env_1878_);
lean_dec(v_declName_1864_);
return v___x_1915_;
}
}
}
}
v___jp_1874_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___y_1866_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
v___jp_1879_:
{
lean_object* v___x_1882_; size_t v_sz_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1882_ = lean_box(0);
v_sz_1883_ = lean_array_size(v___y_1881_);
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(v_env_1878_, v_declName_1864_, v___y_1881_, v_sz_1883_, v___x_1884_, v___x_1882_, v___y_1880_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v_env_1878_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1902_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_snd_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1900_; 
v_snd_1890_ = lean_ctor_get(v_a_1886_, 1);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_a_1886_, 0);
lean_dec(v_unused_1901_);
v___x_1892_ = v_a_1886_;
v_isShared_1893_ = v_isSharedCheck_1900_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_snd_1890_);
lean_dec(v_a_1886_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1900_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1882_);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_snd_1890_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1895_);
v___x_1897_ = v___x_1888_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_declName_1928_, lean_object* v_isMeta_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
uint8_t v_isMeta_boxed_1936_; lean_object* v_res_1937_; 
v_isMeta_boxed_1936_ = lean_unbox(v_isMeta_1929_);
v_res_1937_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_declName_1928_, v_isMeta_boxed_1936_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1938_, lean_object* v_vals_1939_, lean_object* v_i_1940_, lean_object* v_k_1941_){
_start:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_array_get_size(v_keys_1938_);
v___x_1943_ = lean_nat_dec_lt(v_i_1940_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v_i_1940_);
v___x_1944_ = lean_box(0);
return v___x_1944_;
}
else
{
lean_object* v_k_x27_1945_; uint8_t v___x_1946_; 
v_k_x27_1945_ = lean_array_fget_borrowed(v_keys_1938_, v_i_1940_);
v___x_1946_ = lean_name_eq(v_k_1941_, v_k_x27_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_i_1940_, v___x_1947_);
lean_dec(v_i_1940_);
v_i_1940_ = v___x_1948_;
goto _start;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_array_fget_borrowed(v_vals_1939_, v_i_1940_);
lean_dec(v_i_1940_);
lean_inc(v___x_1950_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1952_, lean_object* v_vals_1953_, lean_object* v_i_1954_, lean_object* v_k_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_1952_, v_vals_1953_, v_i_1954_, v_k_1955_);
lean_dec(v_k_1955_);
lean_dec_ref(v_vals_1953_);
lean_dec_ref(v_keys_1952_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_1957_, size_t v_x_1958_, lean_object* v_x_1959_){
_start:
{
if (lean_obj_tag(v_x_1957_) == 0)
{
lean_object* v_es_1960_; lean_object* v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; lean_object* v_j_1964_; lean_object* v___x_1965_; 
v_es_1960_ = lean_ctor_get(v_x_1957_, 0);
v___x_1961_ = lean_box(2);
v___x_1962_ = ((size_t)31ULL);
v___x_1963_ = lean_usize_land(v_x_1958_, v___x_1962_);
v_j_1964_ = lean_usize_to_nat(v___x_1963_);
v___x_1965_ = lean_array_get_borrowed(v___x_1961_, v_es_1960_, v_j_1964_);
lean_dec(v_j_1964_);
switch(lean_obj_tag(v___x_1965_))
{
case 0:
{
lean_object* v_key_1966_; lean_object* v_val_1967_; uint8_t v___x_1968_; 
v_key_1966_ = lean_ctor_get(v___x_1965_, 0);
v_val_1967_ = lean_ctor_get(v___x_1965_, 1);
v___x_1968_ = lean_name_eq(v_x_1959_, v_key_1966_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_box(0);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; 
lean_inc(v_val_1967_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_val_1967_);
return v___x_1970_;
}
}
case 1:
{
lean_object* v_node_1971_; size_t v___x_1972_; size_t v___x_1973_; 
v_node_1971_ = lean_ctor_get(v___x_1965_, 0);
v___x_1972_ = ((size_t)5ULL);
v___x_1973_ = lean_usize_shift_right(v_x_1958_, v___x_1972_);
v_x_1957_ = v_node_1971_;
v_x_1958_ = v___x_1973_;
goto _start;
}
default: 
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_box(0);
return v___x_1975_;
}
}
}
else
{
lean_object* v_ks_1976_; lean_object* v_vs_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_ks_1976_ = lean_ctor_get(v_x_1957_, 0);
v_vs_1977_ = lean_ctor_get(v_x_1957_, 1);
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_1976_, v_vs_1977_, v___x_1978_, v_x_1959_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
size_t v_x_27687__boxed_1983_; lean_object* v_res_1984_; 
v_x_27687__boxed_1983_ = lean_unbox_usize(v_x_1981_);
lean_dec(v_x_1981_);
v_res_1984_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_1980_, v_x_27687__boxed_1983_, v_x_1982_);
lean_dec(v_x_1982_);
lean_dec_ref(v_x_1980_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_1985_, lean_object* v_x_1986_){
_start:
{
uint64_t v___y_1988_; 
if (lean_obj_tag(v_x_1986_) == 0)
{
uint64_t v___x_1991_; 
v___x_1991_ = 1723ULL;
v___y_1988_ = v___x_1991_;
goto v___jp_1987_;
}
else
{
uint64_t v_hash_1992_; 
v_hash_1992_ = lean_ctor_get_uint64(v_x_1986_, sizeof(void*)*2);
v___y_1988_ = v_hash_1992_;
goto v___jp_1987_;
}
v___jp_1987_:
{
size_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_uint64_to_usize(v___y_1988_);
v___x_1990_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_1985_, v___x_1989_, v_x_1986_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_1993_, v_x_1994_);
lean_dec(v_x_1994_);
lean_dec_ref(v_x_1993_);
return v_res_1995_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1996_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
return v___x_1999_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2005_ = l_Lean_stringToMessageData(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2009_, lean_object* v_init_2010_, lean_object* v_x_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
if (lean_obj_tag(v_x_2011_) == 0)
{
lean_object* v_k_2018_; lean_object* v_l_2019_; lean_object* v_r_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_k_2018_ = lean_ctor_get(v_x_2011_, 1);
lean_inc(v_k_2018_);
v_l_2019_ = lean_ctor_get(v_x_2011_, 3);
lean_inc(v_l_2019_);
v_r_2020_ = lean_ctor_get(v_x_2011_, 4);
lean_inc(v_r_2020_);
lean_dec_ref_known(v_x_2011_, 5);
v___x_2021_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_box(0);
lean_inc_ref(v_origDecl_2009_);
v___x_2024_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2009_, v_init_2010_, v_l_2019_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2150_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v_snd_2026_ = lean_ctor_get(v_a_2025_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_a_2025_, 0);
lean_dec(v_unused_2151_);
v___x_2028_ = v_a_2025_;
v_isShared_2029_ = v_isSharedCheck_2150_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_dec(v_a_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2150_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_NameSet_contains(v_snd_2026_, v_k_2018_);
if (v___x_2030_ == 0)
{
uint8_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v_env_2034_; lean_object* v___x_2035_; lean_object* v_toEnvExtension_2036_; lean_object* v_asyncMode_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2031_ = 1;
lean_inc(v_k_2018_);
v___x_2032_ = l_Lean_NameSet_insert(v_snd_2026_, v_k_2018_);
v___x_2033_ = lean_st_ref_get(v___y_2016_);
v_env_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_ref(v_env_2034_);
lean_dec(v___x_2033_);
v___x_2035_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2036_ = lean_ctor_get(v___x_2035_, 0);
v_asyncMode_2037_ = lean_ctor_get(v_toEnvExtension_2036_, 2);
v___x_2038_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2021_, v___x_2035_, v_env_2034_, v_asyncMode_2037_, v___x_2023_, v___x_2030_);
v___x_2039_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2038_, v_k_2018_);
lean_dec(v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 1)
{
lean_object* v_val_2040_; lean_object* v___x_2041_; 
lean_del_object(v___x_2028_);
lean_dec(v_k_2018_);
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_n(v_val_2040_, 2);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2040_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_toSignature_2042_; lean_object* v_a_2043_; lean_object* v_name_2044_; uint8_t v___x_2045_; 
v_toSignature_2042_ = lean_ctor_get(v_val_2040_, 0);
v_a_2043_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2041_, 1);
v_name_2044_ = lean_ctor_get(v_toSignature_2042_, 0);
v___x_2045_ = l_Lean_isPrivateName(v_name_2044_);
if (v___x_2045_ == 0)
{
lean_dec(v_a_2043_);
lean_dec(v_val_2040_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v___x_2032_;
goto _start;
}
else
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_unbox(v_a_2043_);
lean_dec(v_a_2043_);
if (v___x_2047_ == 0)
{
lean_dec(v_val_2040_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v___x_2032_;
goto _start;
}
else
{
lean_object* v___x_2049_; 
lean_inc_ref(v_origDecl_2009_);
v___x_2049_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2009_, v_val_2040_, v___x_2032_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v_snd_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v_snd_2051_ = lean_ctor_get(v_a_2050_, 1);
lean_inc(v_snd_2051_);
lean_dec(v_a_2050_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v_snd_2051_;
goto _start;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_r_2020_);
lean_dec_ref(v_origDecl_2009_);
v_a_2053_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2049_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2049_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_val_2040_);
lean_dec(v___x_2032_);
lean_dec(v_r_2020_);
lean_dec_ref(v_origDecl_2009_);
v_a_2061_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2041_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2041_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v___x_2069_; lean_object* v_env_2070_; lean_object* v___x_2071_; 
lean_dec(v___x_2039_);
v___x_2069_ = lean_st_ref_get(v___y_2016_);
v_env_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc_ref(v_env_2070_);
lean_dec(v___x_2069_);
v___x_2071_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2070_, v_k_2018_);
lean_dec_ref(v_env_2070_);
if (lean_obj_tag(v___x_2071_) == 1)
{
lean_object* v_val_2072_; lean_object* v___x_2073_; lean_object* v_env_2094_; lean_object* v___x_2095_; lean_object* v_modules_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_val_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = lean_st_ref_get(v___y_2016_);
v_env_2094_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_ref(v_env_2094_);
lean_dec(v___x_2073_);
v___x_2095_ = l_Lean_Environment_header(v_env_2094_);
lean_dec_ref(v_env_2094_);
v_modules_2096_ = lean_ctor_get(v___x_2095_, 3);
lean_inc_ref(v_modules_2096_);
lean_dec_ref(v___x_2095_);
v___x_2097_ = lean_array_get_size(v_modules_2096_);
v___x_2098_ = lean_nat_dec_lt(v_val_2072_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_dec_ref(v_modules_2096_);
lean_dec(v_val_2072_);
lean_del_object(v___x_2028_);
goto v___jp_2074_;
}
else
{
lean_object* v___x_2099_; lean_object* v_toImport_2100_; uint8_t v_isExported_2101_; 
v___x_2099_ = lean_array_fget(v_modules_2096_, v_val_2072_);
lean_dec_ref(v_modules_2096_);
v_toImport_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_toImport_2100_);
lean_dec(v___x_2099_);
v_isExported_2101_ = lean_ctor_get_uint8(v_toImport_2100_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2100_);
if (v_isExported_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; lean_object* v_fst_2105_; uint8_t v___x_2106_; 
v___x_2102_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2103_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2102_, v___x_2032_, v___y_2015_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v_fst_2105_ = lean_ctor_get(v_a_2104_, 0);
v___x_2106_ = lean_unbox(v_fst_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_r_2020_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_a_2104_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; 
v_unused_2144_ = lean_ctor_get(v_a_2104_, 1);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_a_2104_, 0);
lean_dec(v_unused_2145_);
v___x_2108_ = v_a_2104_;
v_isShared_2109_ = v_isSharedCheck_2143_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v_a_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2143_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v_toSignature_2111_; lean_object* v_env_2112_; lean_object* v_name_2113_; lean_object* v___x_2114_; lean_object* v_moduleNames_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2110_ = lean_st_ref_get(v___y_2016_);
v_toSignature_2111_ = lean_ctor_get(v_origDecl_2009_, 0);
lean_inc_ref(v_toSignature_2111_);
lean_dec_ref(v_origDecl_2009_);
v_env_2112_ = lean_ctor_get(v___x_2110_, 0);
lean_inc_ref(v_env_2112_);
lean_dec(v___x_2110_);
v_name_2113_ = lean_ctor_get(v_toSignature_2111_, 0);
lean_inc(v_name_2113_);
lean_dec_ref(v_toSignature_2111_);
v___x_2114_ = l_Lean_Environment_header(v_env_2112_);
lean_dec_ref(v_env_2112_);
v_moduleNames_2115_ = lean_ctor_get(v___x_2114_, 4);
lean_inc_ref(v_moduleNames_2115_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = l_Lean_MessageData_ofConstName(v_name_2113_, v___x_2030_);
v___x_2117_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 7);
lean_ctor_set(v___x_2108_, 1, v___x_2116_);
lean_ctor_set(v___x_2108_, 0, v___x_2117_);
v___x_2119_ = v___x_2108_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2116_);
v___x_2119_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 7);
lean_ctor_set(v___x_2028_, 1, v___x_2120_);
lean_ctor_set(v___x_2028_, 0, v___x_2119_);
v___x_2122_ = v___x_2028_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v___x_2123_ = l_Lean_MessageData_ofConstName(v_k_2018_, v___x_2030_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_array_get(v___x_2023_, v_moduleNames_2115_, v_val_2072_);
lean_dec(v_val_2072_);
lean_dec_ref(v_moduleNames_2115_);
v___x_2128_ = l_Lean_MessageData_ofName(v___x_2127_);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2126_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2131_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
else
{
lean_object* v_snd_2146_; 
lean_dec(v_val_2072_);
lean_del_object(v___x_2028_);
lean_dec(v_k_2018_);
v_snd_2146_ = lean_ctor_get(v_a_2104_, 1);
lean_inc(v_snd_2146_);
lean_dec(v_a_2104_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v_snd_2146_;
goto _start;
}
}
else
{
lean_dec(v_val_2072_);
lean_del_object(v___x_2028_);
goto v___jp_2074_;
}
}
v___jp_2074_:
{
lean_object* v___x_2075_; lean_object* v_env_2076_; uint8_t v___x_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2075_ = lean_st_ref_get(v___y_2016_);
v_env_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_ref(v_env_2076_);
lean_dec(v___x_2075_);
lean_inc(v_k_2018_);
v___x_2077_ = l_Lean_getIRPhases(v_env_2076_, v_k_2018_);
v___x_2078_ = 1;
v___x_2079_ = l_Lean_instBEqIRPhases_beq(v___x_2077_, v___x_2078_);
v___x_2080_ = lean_box(v___x_2079_);
v___x_2081_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed), 8, 2);
lean_closure_set(v___x_2081_, 0, v_k_2018_);
lean_closure_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(v___x_2081_, v___x_2031_, v___x_2032_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v_snd_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v_snd_2084_ = lean_ctor_get(v_a_2083_, 1);
lean_inc(v_snd_2084_);
lean_dec(v_a_2083_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v_snd_2084_;
goto _start;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_r_2020_);
lean_dec_ref(v_origDecl_2009_);
v_a_2086_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2082_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2082_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
else
{
lean_dec(v___x_2071_);
lean_del_object(v___x_2028_);
lean_dec(v_k_2018_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v___x_2032_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2028_);
lean_dec(v_k_2018_);
v_init_2010_ = v___x_2022_;
v_x_2011_ = v_r_2020_;
v___y_2012_ = v_snd_2026_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2020_);
lean_dec(v_k_2018_);
lean_dec_ref(v_origDecl_2009_);
return v___x_2024_;
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_origDecl_2009_);
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_init_2010_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v___y_2012_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2155_, lean_object* v_origDecl_2156_, lean_object* v_code_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2164_ = l_Lean_NameSet_empty;
v___x_2165_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2155_, v_code_2157_, v___x_2164_);
v___x_2166_ = lean_box(0);
v___x_2167_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2156_, v___x_2166_, v___x_2165_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2184_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2184_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2184_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_snd_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2182_; 
v_snd_2172_ = lean_ctor_get(v_a_2168_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_a_2168_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v_a_2168_, 0);
lean_dec(v_unused_2183_);
v___x_2174_ = v_a_2168_;
v_isShared_2175_ = v_isSharedCheck_2182_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2172_);
lean_dec(v_a_2168_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2182_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2166_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_snd_2172_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2177_);
v___x_2179_ = v___x_2170_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_a_2185_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2167_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2167_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2193_, lean_object* v_origDecl_2194_, lean_object* v_code_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v___x_27767__boxed_2202_; lean_object* v_res_2203_; 
v___x_27767__boxed_2202_ = lean_unbox(v___x_2193_);
v_res_2203_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_27767__boxed_2202_, v_origDecl_2194_, v_code_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2204_, lean_object* v_decl_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_value_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
v_value_2212_ = lean_ctor_get(v_decl_2205_, 1);
lean_inc_ref(v_value_2212_);
lean_dec_ref(v_decl_2205_);
v___x_2213_ = 0;
v___x_2214_ = lean_box(v___x_2213_);
v___f_2215_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2215_, 0, v___x_2214_);
lean_closure_set(v___f_2215_, 1, v_origDecl_2204_);
v___x_2216_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2215_, v_value_2212_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2217_, lean_object* v_decl_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2217_, v_decl_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2226_, lean_object* v_init_2227_, lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2226_, v_init_2227_, v_x_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2237_, v_x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2240_, v_x_2241_, v_x_2242_);
lean_dec(v_x_2242_);
lean_dec_ref(v_x_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_opt_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_opt_2244_, v___y_2245_, v___y_2248_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_opt_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_opt_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_opt_2252_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2260_, lean_object* v_x_2261_, size_t v_x_2262_, lean_object* v_x_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2261_, v_x_2262_, v_x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_){
_start:
{
size_t v_x_28186__boxed_2269_; lean_object* v_res_2270_; 
v_x_28186__boxed_2269_ = lean_unbox_usize(v_x_2267_);
lean_dec(v_x_2267_);
v_res_2270_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2265_, v_x_2266_, v_x_28186__boxed_2269_, v_x_2268_);
lean_dec(v_x_2268_);
lean_dec_ref(v_x_2266_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4(lean_object* v_00_u03b2_2271_, lean_object* v_m_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(v_m_2272_, v_a_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2275_, lean_object* v_m_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4(v_00_u03b2_2275_, v_m_2276_, v_a_2277_);
lean_dec(v_a_2277_);
lean_dec_ref(v_m_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2279_, lean_object* v_keys_2280_, lean_object* v_vals_2281_, lean_object* v_heq_2282_, lean_object* v_i_2283_, lean_object* v_k_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2280_, v_vals_2281_, v_i_2283_, v_k_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2286_, lean_object* v_keys_2287_, lean_object* v_vals_2288_, lean_object* v_heq_2289_, lean_object* v_i_2290_, lean_object* v_k_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2286_, v_keys_2287_, v_vals_2288_, v_heq_2289_, v_i_2290_, v_k_2291_);
lean_dec(v_k_2291_);
lean_dec_ref(v_vals_2288_);
lean_dec_ref(v_keys_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
uint8_t v___x_2296_; 
v___x_2296_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(v_x_2294_, v_x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5(v_00_u03b2_2297_, v_x_2298_, v_x_2299_);
lean_dec_ref(v_x_2299_);
lean_dec_ref(v_x_2298_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_2302_, lean_object* v_a_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(v_a_2303_, v_x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2306_, lean_object* v_a_2307_, lean_object* v_x_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9(v_00_u03b2_2306_, v_a_2307_, v_x_2308_);
lean_dec(v_x_2308_);
lean_dec(v_a_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2310_, lean_object* v_x_2311_, size_t v_x_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(v_x_2311_, v_x_2312_, v_x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
size_t v_x_28214__boxed_2319_; uint8_t v_res_2320_; lean_object* v_r_2321_; 
v_x_28214__boxed_2319_ = lean_unbox_usize(v_x_2317_);
lean_dec(v_x_2317_);
v_res_2320_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_2315_, v_x_2316_, v_x_28214__boxed_2319_, v_x_2318_);
lean_dec_ref(v_x_2318_);
lean_dec_ref(v_x_2316_);
v_r_2321_ = lean_box(v_res_2320_);
return v_r_2321_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2322_, lean_object* v_keys_2323_, lean_object* v_vals_2324_, lean_object* v_heq_2325_, lean_object* v_i_2326_, lean_object* v_k_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(v_keys_2323_, v_i_2326_, v_k_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2329_, lean_object* v_keys_2330_, lean_object* v_vals_2331_, lean_object* v_heq_2332_, lean_object* v_i_2333_, lean_object* v_k_2334_){
_start:
{
uint8_t v_res_2335_; lean_object* v_r_2336_; 
v_res_2335_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12(v_00_u03b2_2329_, v_keys_2330_, v_vals_2331_, v_heq_2332_, v_i_2333_, v_k_2334_);
lean_dec_ref(v_k_2334_);
lean_dec_ref(v_vals_2331_);
lean_dec_ref(v_keys_2330_);
v_r_2336_ = lean_box(v_res_2335_);
return v_r_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2337_, size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_a_2347_; uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_lt(v_i_2339_, v_sz_2338_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_b_2340_);
return v___x_2352_;
}
else
{
lean_object* v___x_2353_; lean_object* v_a_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_box(0);
v_a_2354_ = lean_array_uget_borrowed(v_as_2337_, v_i_2339_);
lean_inc(v_a_2354_);
v___x_2355_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2354_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_toSignature_2356_; lean_object* v_a_2357_; lean_object* v_name_2358_; uint8_t v___x_2359_; 
v_toSignature_2356_ = lean_ctor_get(v_a_2354_, 0);
v_a_2357_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2355_, 1);
v_name_2358_ = lean_ctor_get(v_toSignature_2356_, 0);
v___x_2359_ = l_Lean_isPrivateName(v_name_2358_);
if (v___x_2359_ == 0)
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_unbox(v_a_2357_);
lean_dec(v_a_2357_);
if (v___x_2360_ == 0)
{
v_a_2347_ = v___x_2353_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = lean_st_ref_get(v___y_2344_);
lean_dec(v___x_2361_);
v___x_2362_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2354_, 2);
v___x_2363_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2354_, v_a_2354_, v___x_2362_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref_known(v___x_2363_, 1);
v_a_2347_ = v___x_2353_;
goto v___jp_2346_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
lean_dec(v_a_2357_);
v_a_2347_ = v___x_2353_;
goto v___jp_2346_;
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2355_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2355_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
v___jp_2346_:
{
size_t v___x_2348_; size_t v___x_2349_; 
v___x_2348_ = ((size_t)1ULL);
v___x_2349_ = lean_usize_add(v_i_2339_, v___x_2348_);
v_i_2339_ = v___x_2349_;
v_b_2340_ = v_a_2347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2380_, lean_object* v_sz_2381_, lean_object* v_i_2382_, lean_object* v_b_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
size_t v_sz_boxed_2389_; size_t v_i_boxed_2390_; lean_object* v_res_2391_; 
v_sz_boxed_2389_ = lean_unbox_usize(v_sz_2381_);
lean_dec(v_sz_2381_);
v_i_boxed_2390_ = lean_unbox_usize(v_i_2382_);
lean_dec(v_i_2382_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2380_, v_sz_boxed_2389_, v_i_boxed_2390_, v_b_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec_ref(v_as_2380_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v___x_2400_; uint8_t v_isModule_2401_; 
v___x_2398_ = lean_st_ref_get(v___y_2396_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_env_2399_);
lean_dec(v___x_2398_);
v___x_2400_ = l_Lean_Environment_header(v_env_2399_);
lean_dec_ref(v_env_2399_);
v_isModule_2401_ = lean_ctor_get_uint8(v___x_2400_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2400_);
if (v_isModule_2401_ == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v_decls_2392_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; size_t v_sz_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2403_ = lean_box(0);
v_sz_2404_ = lean_array_size(v_decls_2392_);
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2392_, v_sz_2404_, v___x_2405_, v___x_2403_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v___x_2406_, 0);
lean_dec(v_unused_2414_);
v___x_2408_ = v___x_2406_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_dec(v___x_2406_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v_decls_2392_);
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_decls_2392_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec_ref(v_decls_2392_);
v_a_2415_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2406_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2406_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2429_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2443_ = l_Lean_stringToMessageData(v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2444_, uint8_t v___x_2445_, lean_object* v_as_2446_, size_t v_sz_2447_, size_t v_i_2448_, lean_object* v_b_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_a_2456_; uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_lt(v_i_2448_, v_sz_2447_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_b_2449_);
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; lean_object* v_a_2463_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___x_2471_; lean_object* v_toSignature_2472_; lean_object* v_env_2473_; lean_object* v_name_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2462_ = lean_box(0);
v_a_2463_ = lean_array_uget_borrowed(v_as_2446_, v_i_2448_);
v___x_2471_ = lean_st_ref_get(v___y_2453_);
v_toSignature_2472_ = lean_ctor_get(v_a_2463_, 0);
v_env_2473_ = lean_ctor_get(v___x_2471_, 0);
lean_inc_ref(v_env_2473_);
lean_dec(v___x_2471_);
v_name_2474_ = lean_ctor_get(v_toSignature_2472_, 0);
v___x_2475_ = l_Lean_Environment_setExporting(v_env_2473_, v___x_2445_);
lean_inc(v_name_2474_);
v___x_2476_ = l_Lean_Environment_contains(v___x_2475_, v_name_2474_, v___x_2445_);
if (v___x_2476_ == 0)
{
v_a_2456_ = v___x_2462_;
goto v___jp_2455_;
}
else
{
lean_object* v_toCold_2477_; lean_object* v_options_2478_; uint8_t v_hasTrace_2479_; 
v_toCold_2477_ = lean_ctor_get(v___y_2452_, 0);
v_options_2478_ = lean_ctor_get(v_toCold_2477_, 2);
v_hasTrace_2479_ = lean_ctor_get_uint8(v_options_2478_, sizeof(void*)*1);
if (v_hasTrace_2479_ == 0)
{
v___y_2465_ = v___y_2450_;
v___y_2466_ = v___y_2451_;
v___y_2467_ = v___y_2452_;
v___y_2468_ = v___y_2453_;
goto v___jp_2464_;
}
else
{
lean_object* v_inheritedTraceOptions_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_inheritedTraceOptions_2480_ = lean_ctor_get(v_toCold_2477_, 11);
v___x_2481_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2482_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2483_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2480_, v_options_2478_, v___x_2482_);
if (v___x_2483_ == 0)
{
v___y_2465_ = v___y_2450_;
v___y_2466_ = v___y_2451_;
v___y_2467_ = v___y_2452_;
v___y_2468_ = v___y_2453_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2484_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2474_);
v___x_2485_ = l_Lean_MessageData_ofName(v_name_2474_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2481_, v___x_2488_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_dec_ref_known(v___x_2489_, 1);
v___y_2465_ = v___y_2450_;
v___y_2466_ = v___y_2451_;
v___y_2467_ = v___y_2452_;
v___y_2468_ = v___y_2453_;
goto v___jp_2464_;
}
else
{
return v___x_2489_;
}
}
}
}
v___jp_2464_:
{
uint8_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2444_);
lean_inc(v_a_2463_);
v___x_2470_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2469_, v_phase_2444_, v_a_2463_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_dec_ref_known(v___x_2470_, 1);
v_a_2456_ = v___x_2462_;
goto v___jp_2455_;
}
else
{
return v___x_2470_;
}
}
}
v___jp_2455_:
{
size_t v___x_2457_; size_t v___x_2458_; 
v___x_2457_ = ((size_t)1ULL);
v___x_2458_ = lean_usize_add(v_i_2448_, v___x_2457_);
v_i_2448_ = v___x_2458_;
v_b_2449_ = v_a_2456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2490_, lean_object* v___x_2491_, lean_object* v_as_2492_, lean_object* v_sz_2493_, lean_object* v_i_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v_phase_boxed_2501_; uint8_t v___x_2258__boxed_2502_; size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_phase_boxed_2501_ = lean_unbox(v_phase_2490_);
v___x_2258__boxed_2502_ = lean_unbox(v___x_2491_);
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2493_);
lean_dec(v_sz_2493_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2501_, v___x_2258__boxed_2502_, v_as_2492_, v_sz_boxed_2503_, v_i_boxed_2504_, v_b_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v_as_2492_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2506_, lean_object* v_decls_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v_env_2514_; lean_object* v___x_2515_; uint8_t v_isModule_2516_; 
v___x_2513_ = lean_st_ref_get(v___y_2511_);
v_env_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc_ref(v_env_2514_);
lean_dec(v___x_2513_);
v___x_2515_ = l_Lean_Environment_header(v_env_2514_);
lean_dec_ref(v_env_2514_);
v_isModule_2516_ = lean_ctor_get_uint8(v___x_2515_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2515_);
if (v_isModule_2516_ == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_decls_2507_);
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = lean_box(0);
v_sz_2519_ = lean_array_size(v_decls_2507_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2506_, v_isModule_2516_, v_decls_2507_, v_sz_2519_, v___x_2520_, v___x_2518_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v___x_2521_, 0);
lean_dec(v_unused_2529_);
v___x_2523_ = v___x_2521_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_dec(v___x_2521_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v_decls_2507_);
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_decls_2507_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v_decls_2507_);
v_a_2530_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2521_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2521_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2538_, lean_object* v_decls_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v_phase_boxed_2545_; lean_object* v_res_2546_; 
v_phase_boxed_2545_ = lean_unbox(v_phase_2538_);
v_res_2546_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2545_, v_decls_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2549_){
_start:
{
lean_object* v___x_2550_; lean_object* v___f_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2550_ = lean_box(v_phase_2549_);
v___f_2551_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2551_, 0, v___x_2550_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = 0;
v___x_2554_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2555_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2555_, 0, v___x_2552_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
lean_ctor_set(v___x_2555_, 2, v___f_2551_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*3, v_phase_2549_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*3 + 1, v_phase_2549_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*3 + 2, v___x_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2556_){
_start:
{
uint8_t v_phase_boxed_2557_; lean_object* v_res_2558_; 
v_phase_boxed_2557_ = lean_unbox(v_phase_2556_);
v_res_2558_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2557_);
return v_res_2558_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_unsigned_to_nat(3356661454u);
v___x_2611_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2612_ = l_Lean_Name_num___override(v___x_2611_, v___x_2610_);
return v___x_2612_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2615_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2616_ = l_Lean_Name_str___override(v___x_2615_, v___x_2614_);
return v___x_2616_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2619_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2620_ = l_Lean_Name_str___override(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_unsigned_to_nat(2u);
v___x_2622_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2623_ = l_Lean_Name_num___override(v___x_2622_, v___x_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2625_; uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2625_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2626_ = 0;
v___x_2627_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2628_ = l_Lean_registerTraceClass(v___x_2625_, v___x_2626_, v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2630_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Visibility(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Visibility(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Visibility(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Visibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Visibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Visibility(builtin);
}
#ifdef __cplusplus
}
#endif
