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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21(uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_getIRPhases(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
extern lean_object* l_Lean_Compiler_LCNF_baseExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_41_; 
v___x_41_ = lean_nat_dec_le(v___x_39_, v___x_39_);
if (v___x_41_ == 0)
{
if (v___x_40_ == 0)
{
lean_dec_ref(v_alts_37_);
return v_s_20_;
}
else
{
size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((size_t)0ULL);
v___x_43_ = lean_usize_of_nat(v___x_39_);
v___x_44_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_18_, v_alts_37_, v___x_42_, v___x_43_, v_s_20_);
lean_dec_ref(v_alts_37_);
return v___x_44_;
}
}
else
{
size_t v___x_45_; size_t v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((size_t)0ULL);
v___x_46_ = lean_usize_of_nat(v___x_39_);
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_18_, v_alts_37_, v___x_45_, v___x_46_, v_s_20_);
lean_dec_ref(v_alts_37_);
return v___x_47_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(uint8_t v_pu_48_, lean_object* v_as_49_, size_t v_i_50_, size_t v_stop_51_, lean_object* v_b_52_){
_start:
{
lean_object* v___y_54_; uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_eq(v_i_50_, v_stop_51_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_array_uget_borrowed(v_as_49_, v_i_50_);
switch(lean_obj_tag(v___x_59_))
{
case 0:
{
lean_object* v_code_60_; lean_object* v___x_61_; 
v_code_60_ = lean_ctor_get(v___x_59_, 2);
lean_inc_ref(v_code_60_);
v___x_61_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_48_, v_code_60_, v_b_52_);
v___y_54_ = v___x_61_;
goto v___jp_53_;
}
case 1:
{
lean_object* v_code_62_; lean_object* v___x_63_; 
v_code_62_ = lean_ctor_get(v___x_59_, 1);
lean_inc_ref(v_code_62_);
v___x_63_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_48_, v_code_62_, v_b_52_);
v___y_54_ = v___x_63_;
goto v___jp_53_;
}
default: 
{
lean_object* v_code_64_; lean_object* v___x_65_; 
v_code_64_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_code_64_);
v___x_65_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_48_, v_code_64_, v_b_52_);
v___y_54_ = v___x_65_;
goto v___jp_53_;
}
}
}
else
{
return v_b_52_;
}
v___jp_53_:
{
size_t v___x_55_; size_t v___x_56_; 
v___x_55_ = ((size_t)1ULL);
v___x_56_ = lean_usize_add(v_i_50_, v___x_55_);
v_i_50_ = v___x_56_;
v_b_52_ = v___y_54_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0___boxed(lean_object* v_pu_66_, lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_, lean_object* v_b_70_){
_start:
{
uint8_t v_pu_boxed_71_; size_t v_i_boxed_72_; size_t v_stop_boxed_73_; lean_object* v_res_74_; 
v_pu_boxed_71_ = lean_unbox(v_pu_66_);
v_i_boxed_72_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_73_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_res_74_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_boxed_71_, v_as_67_, v_i_boxed_72_, v_stop_boxed_73_, v_b_70_);
lean_dec_ref(v_as_67_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object* v_pu_75_, lean_object* v_code_76_, lean_object* v_s_77_){
_start:
{
uint8_t v_pu_boxed_78_; lean_object* v_res_79_; 
v_pu_boxed_78_ = lean_unbox(v_pu_75_);
v_res_79_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_boxed_78_, v_code_76_, v_s_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(lean_object* v_opts_80_, lean_object* v_opt_81_){
_start:
{
lean_object* v_name_82_; lean_object* v_defValue_83_; lean_object* v_map_84_; lean_object* v___x_85_; 
v_name_82_ = lean_ctor_get(v_opt_81_, 0);
v_defValue_83_ = lean_ctor_get(v_opt_81_, 1);
v_map_84_ = lean_ctor_get(v_opts_80_, 0);
v___x_85_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_84_, v_name_82_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_inc(v_defValue_83_);
return v_defValue_83_;
}
else
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_85_, 1);
if (lean_obj_tag(v_val_86_) == 3)
{
lean_object* v_v_87_; 
v_v_87_ = lean_ctor_get(v_val_86_, 0);
lean_inc(v_v_87_);
lean_dec_ref_known(v_val_86_, 1);
return v_v_87_;
}
else
{
lean_dec(v_val_86_);
lean_inc(v_defValue_83_);
return v_defValue_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0___boxed(lean_object* v_opts_88_, lean_object* v_opt_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_opts_88_, v_opt_89_);
lean_dec_ref(v_opt_89_);
lean_dec_ref(v_opts_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(lean_object* v_v_91_, lean_object* v_f_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
if (lean_obj_tag(v_v_91_) == 0)
{
lean_object* v_code_98_; lean_object* v___x_99_; 
v_code_98_ = lean_ctor_get(v_v_91_, 0);
lean_inc_ref(v_code_98_);
lean_dec_ref_known(v_v_91_, 1);
lean_inc(v___y_96_);
lean_inc_ref(v___y_95_);
lean_inc(v___y_94_);
lean_inc_ref(v___y_93_);
v___x_99_ = lean_apply_6(v_f_92_, v_code_98_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, lean_box(0));
return v___x_99_;
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_f_92_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_v_91_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_v_91_, 0);
lean_dec(v_unused_109_);
v___x_101_ = v_v_91_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_v_91_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = 0;
v___x_104_ = lean_box(v___x_103_);
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 0);
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg___boxed(lean_object* v_v_110_, lean_object* v_f_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_110_, v_f_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(uint8_t v_pu_118_, lean_object* v_v_119_, lean_object* v_f_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_119_, v_f_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___boxed(lean_object* v_pu_127_, lean_object* v_v_128_, lean_object* v_f_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v_pu_boxed_135_; lean_object* v_res_136_; 
v_pu_boxed_135_ = lean_unbox(v_pu_127_);
v_res_136_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(v_pu_boxed_135_, v_v_128_, v_f_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(lean_object* v_toSignature_137_, uint8_t v_a_138_, uint8_t v_pu_139_, lean_object* v_code_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; lean_object* v_env_147_; lean_object* v_name_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_146_ = lean_st_ref_get(v___y_144_);
v_env_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc_ref(v_env_147_);
lean_dec(v___x_146_);
v_name_148_ = lean_ctor_get(v_toSignature_137_, 0);
lean_inc(v_name_148_);
lean_dec_ref(v_toSignature_137_);
v___x_149_ = 1;
v___x_150_ = l_Lean_Environment_setExporting(v_env_147_, v___x_149_);
v___x_151_ = l_Lean_Environment_findAsync_x3f(v___x_150_, v_name_148_, v_a_138_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box(v_a_138_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_173_; 
v_val_154_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_173_ == 0)
{
v___x_156_ = v___x_151_;
v_isShared_157_ = v_isSharedCheck_173_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_dec(v___x_151_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_173_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint8_t v_kind_158_; uint8_t v___x_159_; uint8_t v___x_160_; 
v_kind_158_ = lean_ctor_get_uint8(v_val_154_, sizeof(void*)*3);
lean_dec(v_val_154_);
v___x_159_ = 0;
v___x_160_ = l_Lean_instBEqConstantKind_beq(v_kind_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_box(v___x_160_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 0);
lean_ctor_set(v___x_156_, 0, v___x_161_);
v___x_163_ = v___x_156_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_165_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_143_);
v___x_166_ = l_Lean_Compiler_LCNF_compiler_small;
v___x_167_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v___x_165_, v___x_166_);
lean_dec_ref(v___x_165_);
v___x_168_ = l_Lean_Compiler_LCNF_Code_sizeLe(v_pu_139_, v_code_140_, v___x_167_);
lean_dec(v___x_167_);
v___x_169_ = lean_box(v___x_168_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 0);
lean_ctor_set(v___x_156_, 0, v___x_169_);
v___x_171_ = v___x_156_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed(lean_object* v_toSignature_174_, lean_object* v_a_175_, lean_object* v_pu_176_, lean_object* v_code_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
uint8_t v_a_965__boxed_183_; uint8_t v_pu_boxed_184_; lean_object* v_res_185_; 
v_a_965__boxed_183_ = lean_unbox(v_a_175_);
v_pu_boxed_184_ = lean_unbox(v_pu_176_);
v_res_185_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_174_, v_a_965__boxed_183_, v_pu_boxed_184_, v_code_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec_ref(v_code_177_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(uint8_t v_pu_186_, lean_object* v_decl_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
lean_inc_ref(v_decl_187_);
v___x_193_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_187_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; uint8_t v___x_195_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v___x_195_ = lean_unbox(v_a_194_);
if (v___x_195_ == 0)
{
lean_object* v_toSignature_196_; lean_object* v_value_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___x_200_; 
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_toSignature_196_ = lean_ctor_get(v_decl_187_, 0);
lean_inc_ref(v_toSignature_196_);
v_value_197_ = lean_ctor_get(v_decl_187_, 1);
lean_inc_ref(v_value_197_);
lean_dec_ref(v_decl_187_);
v___x_198_ = lean_box(v_pu_186_);
v___f_199_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed), 9, 3);
lean_closure_set(v___f_199_, 0, v_toSignature_196_);
lean_closure_set(v___f_199_, 1, v_a_194_);
lean_closure_set(v___f_199_, 2, v___x_198_);
v___x_200_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_value_197_, v___f_199_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_200_;
}
else
{
lean_dec_ref(v_decl_187_);
return v___x_193_;
}
}
else
{
lean_dec_ref(v_decl_187_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(lean_object* v_pu_201_, lean_object* v_decl_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_pu_boxed_208_; lean_object* v_res_209_; 
v_pu_boxed_208_ = lean_unbox(v_pu_201_);
v_res_209_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_boxed_208_, v_decl_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_209_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_214_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
lean_ctor_set(v___x_216_, 2, v___x_215_);
lean_ctor_set(v___x_216_, 3, v___x_215_);
lean_ctor_set(v___x_216_, 4, v___x_214_);
lean_ctor_set(v___x_216_, 5, v___x_214_);
lean_ctor_set(v___x_216_, 6, v___x_214_);
lean_ctor_set(v___x_216_, 7, v___x_214_);
lean_ctor_set(v___x_216_, 8, v___x_214_);
lean_ctor_set(v___x_216_, 9, v___x_214_);
lean_ctor_set(v___x_216_, 10, v___x_214_);
lean_ctor_set(v___x_216_, 11, v___x_213_);
return v___x_216_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_217_; double v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_float_of_nat(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(lean_object* v_cls_222_, lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v_env_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_ref_229_ = lean_ctor_get(v___y_226_, 2);
v___x_230_ = lean_st_ref_get(v___y_227_);
v_env_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_env_231_);
lean_dec(v___x_230_);
v___x_232_ = lean_st_ref_get(v___y_225_);
v___x_233_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_224_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_293_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_293_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_293_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_293_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_lctx_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_291_; 
v_lctx_238_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_232_, 1);
lean_dec(v_unused_292_);
v___x_240_ = v___x_232_;
v_isShared_241_ = v_isSharedCheck_291_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_lctx_238_);
lean_dec(v___x_232_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_291_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_242_ = lean_unbox(v_a_234_);
lean_dec(v_a_234_);
v___x_243_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_238_, v___x_242_);
lean_dec_ref(v_lctx_238_);
v___x_244_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_226_);
v___x_245_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_env_231_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
lean_ctor_set(v___x_246_, 2, v___x_243_);
lean_ctor_set(v___x_246_, 3, v___x_244_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 3);
lean_ctor_set(v___x_240_, 1, v_msg_223_);
lean_ctor_set(v___x_240_, 0, v___x_246_);
v___x_248_ = v___x_240_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_msg_223_);
v___x_248_ = v_reuseFailAlloc_290_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v_traceState_250_; lean_object* v_env_251_; lean_object* v_nextMacroScope_252_; lean_object* v_ngen_253_; lean_object* v_auxDeclNGen_254_; lean_object* v_cache_255_; lean_object* v_recordedDeps_256_; lean_object* v_messages_257_; lean_object* v_infoState_258_; lean_object* v_snapshotTasks_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_289_; 
v___x_249_ = lean_st_ref_take(v___y_227_);
v_traceState_250_ = lean_ctor_get(v___x_249_, 4);
v_env_251_ = lean_ctor_get(v___x_249_, 0);
v_nextMacroScope_252_ = lean_ctor_get(v___x_249_, 1);
v_ngen_253_ = lean_ctor_get(v___x_249_, 2);
v_auxDeclNGen_254_ = lean_ctor_get(v___x_249_, 3);
v_cache_255_ = lean_ctor_get(v___x_249_, 5);
v_recordedDeps_256_ = lean_ctor_get(v___x_249_, 6);
v_messages_257_ = lean_ctor_get(v___x_249_, 7);
v_infoState_258_ = lean_ctor_get(v___x_249_, 8);
v_snapshotTasks_259_ = lean_ctor_get(v___x_249_, 9);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_289_ == 0)
{
v___x_261_ = v___x_249_;
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snapshotTasks_259_);
lean_inc(v_infoState_258_);
lean_inc(v_messages_257_);
lean_inc(v_recordedDeps_256_);
lean_inc(v_cache_255_);
lean_inc(v_traceState_250_);
lean_inc(v_auxDeclNGen_254_);
lean_inc(v_ngen_253_);
lean_inc(v_nextMacroScope_252_);
lean_inc(v_env_251_);
lean_dec(v___x_249_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint64_t v_tid_263_; lean_object* v_traces_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_288_; 
v_tid_263_ = lean_ctor_get_uint64(v_traceState_250_, sizeof(void*)*1);
v_traces_264_ = lean_ctor_get(v_traceState_250_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_traceState_250_);
if (v_isSharedCheck_288_ == 0)
{
v___x_266_ = v_traceState_250_;
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_traces_264_);
lean_dec(v_traceState_250_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; double v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_box(0);
v___x_270_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_271_ = 0;
v___x_272_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_273_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_273_, 0, v_cls_222_);
lean_ctor_set(v___x_273_, 1, v___x_269_);
lean_ctor_set(v___x_273_, 2, v___x_272_);
lean_ctor_set_float(v___x_273_, sizeof(void*)*3, v___x_270_);
lean_ctor_set_float(v___x_273_, sizeof(void*)*3 + 8, v___x_270_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 16, v___x_271_);
v___x_274_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_275_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_248_);
lean_ctor_set(v___x_275_, 2, v___x_274_);
lean_inc(v_ref_229_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_ref_229_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = l_Lean_PersistentArray_push___redArg(v_traces_264_, v___x_276_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_277_);
v___x_279_ = v___x_266_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_277_);
lean_ctor_set_uint64(v_reuseFailAlloc_287_, sizeof(void*)*1, v_tid_263_);
v___x_279_ = v_reuseFailAlloc_287_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 4, v___x_279_);
v___x_281_ = v___x_261_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_env_251_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_nextMacroScope_252_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_ngen_253_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_auxDeclNGen_254_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_286_, 5, v_cache_255_);
lean_ctor_set(v_reuseFailAlloc_286_, 6, v_recordedDeps_256_);
lean_ctor_set(v_reuseFailAlloc_286_, 7, v_messages_257_);
lean_ctor_set(v_reuseFailAlloc_286_, 8, v_infoState_258_);
lean_ctor_set(v_reuseFailAlloc_286_, 9, v_snapshotTasks_259_);
v___x_281_ = v_reuseFailAlloc_286_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_st_ref_put(v___y_227_, v___x_281_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_268_);
v___x_284_ = v___x_236_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_268_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
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
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v___x_232_);
lean_dec_ref(v_env_231_);
lean_dec_ref(v_msg_223_);
lean_dec(v_cls_222_);
v_a_294_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_233_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_233_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___boxed(lean_object* v_cls_302_, lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v_cls_302_, v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(lean_object* v_f_310_, lean_object* v_v_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
if (lean_obj_tag(v_v_311_) == 0)
{
lean_object* v_code_317_; lean_object* v___x_318_; 
v_code_317_ = lean_ctor_get(v_v_311_, 0);
lean_inc_ref(v_code_317_);
lean_dec_ref_known(v_v_311_, 1);
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
v___x_318_ = lean_apply_6(v_f_310_, v_code_317_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, lean_box(0));
return v___x_318_;
}
else
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_f_310_);
v_isSharedCheck_326_ = !lean_is_exclusive(v_v_311_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v_v_311_, 0);
lean_dec(v_unused_327_);
v___x_320_ = v_v_311_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_dec(v_v_311_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 0);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg___boxed(lean_object* v_f_328_, lean_object* v_v_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_328_, v_v_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(uint8_t v_pu_336_, lean_object* v_f_337_, lean_object* v_v_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_337_, v_v_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(lean_object* v_pu_345_, lean_object* v_f_346_, lean_object* v_v_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
uint8_t v_pu_boxed_353_; lean_object* v_res_354_; 
v_pu_boxed_353_ = lean_unbox(v_pu_345_);
v_res_354_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_boxed_353_, v_f_346_, v_v_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object* v_pu_355_, lean_object* v_phase_356_, lean_object* v_decl_357_, lean_object* v_code_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v_pu_boxed_364_; uint8_t v_phase_boxed_365_; lean_object* v_res_366_; 
v_pu_boxed_364_ = lean_unbox(v_pu_355_);
v_phase_boxed_365_ = lean_unbox(v_phase_356_);
v_res_366_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(v_pu_boxed_364_, v_phase_boxed_365_, v_decl_357_, v_code_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_380_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_381_ = l_Lean_Name_append(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2));
v___x_387_ = l_Lean_stringToMessageData(v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec(uint8_t v_pu_388_, uint8_t v_phase_389_, lean_object* v_decl_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___f_398_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___x_406_; lean_object* v_toSignature_407_; lean_object* v_env_408_; lean_object* v_nextMacroScope_409_; lean_object* v_ngen_410_; lean_object* v_auxDeclNGen_411_; lean_object* v_traceState_412_; lean_object* v_recordedDeps_413_; lean_object* v_messages_414_; lean_object* v_infoState_415_; lean_object* v_snapshotTasks_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_487_; 
v___x_396_ = lean_box(v_pu_388_);
v___x_397_ = lean_box(v_phase_389_);
lean_inc_ref(v_decl_390_);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed), 9, 3);
lean_closure_set(v___f_398_, 0, v___x_396_);
lean_closure_set(v___f_398_, 1, v___x_397_);
lean_closure_set(v___f_398_, 2, v_decl_390_);
v___x_406_ = lean_st_ref_take(v_a_394_);
v_toSignature_407_ = lean_ctor_get(v_decl_390_, 0);
v_env_408_ = lean_ctor_get(v___x_406_, 0);
v_nextMacroScope_409_ = lean_ctor_get(v___x_406_, 1);
v_ngen_410_ = lean_ctor_get(v___x_406_, 2);
v_auxDeclNGen_411_ = lean_ctor_get(v___x_406_, 3);
v_traceState_412_ = lean_ctor_get(v___x_406_, 4);
v_recordedDeps_413_ = lean_ctor_get(v___x_406_, 6);
v_messages_414_ = lean_ctor_get(v___x_406_, 7);
v_infoState_415_ = lean_ctor_get(v___x_406_, 8);
v_snapshotTasks_416_ = lean_ctor_get(v___x_406_, 9);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v___x_406_, 5);
lean_dec(v_unused_488_);
v___x_418_ = v___x_406_;
v_isShared_419_ = v_isSharedCheck_487_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_snapshotTasks_416_);
lean_inc(v_infoState_415_);
lean_inc(v_messages_414_);
lean_inc(v_recordedDeps_413_);
lean_inc(v_traceState_412_);
lean_inc(v_auxDeclNGen_411_);
lean_inc(v_ngen_410_);
lean_inc(v_nextMacroScope_409_);
lean_inc(v_env_408_);
lean_dec(v___x_406_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_487_;
goto v_resetjp_417_;
}
v___jp_399_:
{
lean_object* v_value_404_; lean_object* v___x_405_; 
v_value_404_ = lean_ctor_get(v_decl_390_, 1);
lean_inc_ref(v_value_404_);
lean_dec_ref(v_decl_390_);
v___x_405_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_398_, v_value_404_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_405_;
}
v_resetjp_417_:
{
lean_object* v_name_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___x_449_; 
v_name_420_ = lean_ctor_get(v_toSignature_407_, 0);
lean_inc(v_name_420_);
v___x_421_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_408_, v_name_420_);
v___x_422_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 5, v___x_422_);
lean_ctor_set(v___x_418_, 0, v___x_421_);
v___x_449_ = v___x_418_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_nextMacroScope_409_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_ngen_410_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_auxDeclNGen_411_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_traceState_412_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_486_, 6, v_recordedDeps_413_);
lean_ctor_set(v_reuseFailAlloc_486_, 7, v_messages_414_);
lean_ctor_set(v_reuseFailAlloc_486_, 8, v_infoState_415_);
lean_ctor_set(v_reuseFailAlloc_486_, 9, v_snapshotTasks_416_);
v___x_449_ = v_reuseFailAlloc_486_;
goto v_reusejp_448_;
}
v___jp_423_:
{
lean_object* v___x_428_; lean_object* v_env_429_; lean_object* v_nextMacroScope_430_; lean_object* v_ngen_431_; lean_object* v_auxDeclNGen_432_; lean_object* v_traceState_433_; lean_object* v_recordedDeps_434_; lean_object* v_messages_435_; lean_object* v_infoState_436_; lean_object* v_snapshotTasks_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v___x_428_ = lean_st_ref_take(v___y_427_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
v_nextMacroScope_430_ = lean_ctor_get(v___x_428_, 1);
v_ngen_431_ = lean_ctor_get(v___x_428_, 2);
v_auxDeclNGen_432_ = lean_ctor_get(v___x_428_, 3);
v_traceState_433_ = lean_ctor_get(v___x_428_, 4);
v_recordedDeps_434_ = lean_ctor_get(v___x_428_, 6);
v_messages_435_ = lean_ctor_get(v___x_428_, 7);
v_infoState_436_ = lean_ctor_get(v___x_428_, 8);
v_snapshotTasks_437_ = lean_ctor_get(v___x_428_, 9);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v___x_428_, 5);
lean_dec(v_unused_447_);
v___x_439_ = v___x_428_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snapshotTasks_437_);
lean_inc(v_infoState_436_);
lean_inc(v_messages_435_);
lean_inc(v_recordedDeps_434_);
lean_inc(v_traceState_433_);
lean_inc(v_auxDeclNGen_432_);
lean_inc(v_ngen_431_);
lean_inc(v_nextMacroScope_430_);
lean_inc(v_env_429_);
lean_dec(v___x_428_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_inc(v_name_420_);
v___x_441_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_429_, v_phase_389_, v_name_420_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 5, v___x_422_);
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_nextMacroScope_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_ngen_431_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_auxDeclNGen_432_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_traceState_433_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_recordedDeps_434_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_messages_435_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_infoState_436_);
lean_ctor_set(v_reuseFailAlloc_445_, 9, v_snapshotTasks_437_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_st_ref_put(v___y_427_, v___x_443_);
v___y_400_ = v___y_424_;
v___y_401_ = v___y_425_;
v___y_402_ = v___y_426_;
v___y_403_ = v___y_427_;
goto v___jp_399_;
}
}
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_st_ref_put(v_a_394_, v___x_449_);
lean_inc_ref(v_decl_390_);
v___x_451_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_388_, v_decl_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_477_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_477_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_477_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_477_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___x_456_; 
v___x_456_ = lean_unbox(v_a_452_);
lean_dec(v_a_452_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec_ref(v___f_398_);
lean_dec_ref(v_decl_390_);
v___x_457_ = lean_box(0);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
lean_object* v___x_461_; lean_object* v_env_462_; uint8_t v___x_463_; 
lean_del_object(v___x_454_);
v___x_461_ = lean_st_ref_get(v_a_394_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_461_);
v___x_463_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_462_, v_phase_389_, v_name_420_);
if (v___x_463_ == 0)
{
lean_object* v_toCold_464_; lean_object* v_options_465_; uint8_t v_hasTrace_466_; 
v_toCold_464_ = lean_ctor_get(v_a_393_, 0);
v_options_465_ = lean_ctor_get(v_toCold_464_, 2);
v_hasTrace_466_ = lean_ctor_get_uint8(v_options_465_, sizeof(void*)*1);
if (v_hasTrace_466_ == 0)
{
v___y_424_ = v_a_391_;
v___y_425_ = v_a_392_;
v___y_426_ = v_a_393_;
v___y_427_ = v_a_394_;
goto v___jp_423_;
}
else
{
lean_object* v_inheritedTraceOptions_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_inheritedTraceOptions_467_ = lean_ctor_get(v_toCold_464_, 11);
v___x_468_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_469_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_467_, v_options_465_, v___x_469_);
if (v___x_470_ == 0)
{
v___y_424_ = v_a_391_;
v___y_425_ = v_a_392_;
v___y_426_ = v_a_393_;
v___y_427_ = v_a_394_;
goto v___jp_423_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_420_);
v___x_472_ = l_Lean_MessageData_ofName(v_name_420_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_468_, v___x_475_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec_ref_known(v___x_476_, 1);
v___y_424_ = v_a_391_;
v___y_425_ = v_a_392_;
v___y_426_ = v_a_393_;
v___y_427_ = v_a_394_;
goto v___jp_423_;
}
else
{
lean_dec_ref(v___f_398_);
lean_dec_ref(v_decl_390_);
return v___x_476_;
}
}
}
}
else
{
v___y_400_ = v_a_391_;
v___y_401_ = v_a_392_;
v___y_402_ = v_a_393_;
v___y_403_ = v_a_394_;
goto v___jp_399_;
}
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec_ref(v___f_398_);
lean_dec_ref(v_decl_390_);
v_a_478_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_451_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_451_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
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
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(uint8_t v_phase_492_, lean_object* v_decl_493_, lean_object* v_init_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_k_501_; lean_object* v_l_502_; lean_object* v_r_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_k_501_ = lean_ctor_get(v_x_495_, 1);
lean_inc(v_k_501_);
v_l_502_ = lean_ctor_get(v_x_495_, 3);
lean_inc(v_l_502_);
v_r_503_ = lean_ctor_get(v_x_495_, 4);
lean_inc(v_r_503_);
lean_dec_ref_known(v_x_495_, 5);
v___x_504_ = lean_box(0);
lean_inc_ref(v_decl_493_);
v___x_505_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_492_, v_decl_493_, v_init_494_, v_l_502_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_506_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_506_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_501_, v_phase_492_, v___y_499_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
if (lean_obj_tag(v_a_507_) == 1)
{
lean_object* v_val_508_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___x_525_; lean_object* v_env_526_; uint8_t v___x_527_; 
v_val_508_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v_a_507_, 1);
v___x_525_ = lean_st_ref_get(v___y_499_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_525_);
v___x_527_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_526_, v_k_501_);
if (v___x_527_ == 0)
{
lean_object* v_toCold_528_; lean_object* v_options_529_; uint8_t v_hasTrace_530_; 
v_toCold_528_ = lean_ctor_get(v___y_498_, 0);
v_options_529_ = lean_ctor_get(v_toCold_528_, 2);
v_hasTrace_530_ = lean_ctor_get_uint8(v_options_529_, sizeof(void*)*1);
if (v_hasTrace_530_ == 0)
{
lean_dec(v_k_501_);
v___y_510_ = v___y_496_;
v___y_511_ = v___y_497_;
v___y_512_ = v___y_498_;
v___y_513_ = v___y_499_;
goto v___jp_509_;
}
else
{
lean_object* v_inheritedTraceOptions_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_inheritedTraceOptions_531_ = lean_ctor_get(v_toCold_528_, 11);
v___x_532_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_533_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_534_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_531_, v_options_529_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec(v_k_501_);
v___y_510_ = v___y_496_;
v___y_511_ = v___y_497_;
v___y_512_ = v___y_498_;
v___y_513_ = v___y_499_;
goto v___jp_509_;
}
else
{
lean_object* v_toSignature_535_; lean_object* v_name_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_toSignature_535_ = lean_ctor_get(v_decl_493_, 0);
v_name_536_ = lean_ctor_get(v_toSignature_535_, 0);
v___x_537_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
v___x_538_ = l_Lean_MessageData_ofName(v_k_501_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_inc(v_name_536_);
v___x_542_ = l_Lean_MessageData_ofName(v_name_536_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_532_, v___x_543_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_dec_ref_known(v___x_544_, 1);
v___y_510_ = v___y_496_;
v___y_511_ = v___y_497_;
v___y_512_ = v___y_498_;
v___y_513_ = v___y_499_;
goto v___jp_509_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_val_508_);
lean_dec(v_r_503_);
lean_dec_ref(v_decl_493_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
else
{
lean_dec(v_val_508_);
lean_dec(v_k_501_);
v_init_494_ = v___x_504_;
v_x_495_ = v_r_503_;
goto _start;
}
v___jp_509_:
{
uint8_t v___x_514_; lean_object* v___x_515_; 
v___x_514_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_492_);
v___x_515_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_514_, v_phase_492_, v_val_508_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_dec_ref_known(v___x_515_, 1);
v_init_494_ = v___x_504_;
v_x_495_ = v_r_503_;
goto _start;
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_r_503_);
lean_dec_ref(v_decl_493_);
v_a_517_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
else
{
lean_dec(v_a_507_);
lean_dec(v_k_501_);
v_init_494_ = v___x_504_;
v_x_495_ = v_r_503_;
goto _start;
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_r_503_);
lean_dec(v_k_501_);
lean_dec_ref(v_decl_493_);
v_a_555_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_506_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_506_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_dec(v_r_503_);
lean_dec(v_k_501_);
lean_dec_ref(v_decl_493_);
return v___x_505_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_decl_493_);
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v_init_494_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t v_pu_565_, uint8_t v_phase_566_, lean_object* v_decl_567_, lean_object* v_code_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = l_Lean_NameSet_empty;
v___x_575_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_565_, v_code_568_, v___x_574_);
v___x_576_ = lean_box(0);
v___x_577_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_566_, v_decl_567_, v___x_576_, v___x_575_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_577_, 0);
lean_dec(v_unused_585_);
v___x_579_ = v___x_577_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_dec(v___x_577_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_576_);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_576_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_577_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_577_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object* v_phase_594_, lean_object* v_decl_595_, lean_object* v_init_596_, lean_object* v_x_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v_phase_boxed_603_; lean_object* v_res_604_; 
v_phase_boxed_603_ = lean_unbox(v_phase_594_);
v_res_604_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_603_, v_decl_595_, v_init_596_, v_x_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object* v_pu_605_, lean_object* v_phase_606_, lean_object* v_decl_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
uint8_t v_pu_boxed_613_; uint8_t v_phase_boxed_614_; lean_object* v_res_615_; 
v_pu_boxed_613_ = lean_unbox(v_pu_605_);
v_phase_boxed_614_ = lean_unbox(v_phase_606_);
v_res_615_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_boxed_613_, v_phase_boxed_614_, v_decl_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_ref_622_; lean_object* v___x_623_; lean_object* v_env_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_ref_622_ = lean_ctor_get(v___y_619_, 2);
v___x_623_ = lean_st_ref_get(v___y_620_);
v_env_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_env_624_);
lean_dec(v___x_623_);
v___x_625_ = lean_st_ref_get(v___y_618_);
v___x_626_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_617_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_649_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_649_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_649_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_649_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_lctx_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_647_; 
v_lctx_631_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_625_, 1);
lean_dec(v_unused_648_);
v___x_633_ = v___x_625_;
v_isShared_634_ = v_isSharedCheck_647_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_lctx_631_);
lean_dec(v___x_625_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_647_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_635_ = lean_unbox(v_a_627_);
lean_dec(v_a_627_);
v___x_636_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_631_, v___x_635_);
lean_dec_ref(v_lctx_631_);
v___x_637_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_619_);
v___x_638_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_639_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_639_, 0, v_env_624_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
lean_ctor_set(v___x_639_, 2, v___x_636_);
lean_ctor_set(v___x_639_, 3, v___x_637_);
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 3);
lean_ctor_set(v___x_633_, 1, v_msg_616_);
lean_ctor_set(v___x_633_, 0, v___x_639_);
v___x_641_ = v___x_633_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_msg_616_);
v___x_641_ = v_reuseFailAlloc_646_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
lean_inc(v_ref_622_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_ref_622_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 1);
lean_ctor_set(v___x_629_, 0, v___x_642_);
v___x_644_ = v___x_629_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v___x_625_);
lean_dec_ref(v_env_624_);
lean_dec_ref(v_msg_616_);
v_a_650_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_626_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_626_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_666_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_674_, v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
return v_res_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_683_, lean_object* v_opt_684_){
_start:
{
lean_object* v_name_685_; lean_object* v_defValue_686_; lean_object* v_map_687_; lean_object* v___x_688_; 
v_name_685_ = lean_ctor_get(v_opt_684_, 0);
v_defValue_686_ = lean_ctor_get(v_opt_684_, 1);
v_map_687_ = lean_ctor_get(v_opts_683_, 0);
v___x_688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_687_, v_name_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
uint8_t v___x_689_; 
v___x_689_ = lean_unbox(v_defValue_686_);
return v___x_689_;
}
else
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v_val_690_) == 1)
{
uint8_t v_v_691_; 
v_v_691_ = lean_ctor_get_uint8(v_val_690_, 0);
lean_dec_ref_known(v_val_690_, 0);
return v_v_691_;
}
else
{
uint8_t v___x_692_; 
lean_dec(v_val_690_);
v___x_692_ = lean_unbox(v_defValue_686_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_693_, lean_object* v_opt_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_693_, v_opt_694_);
lean_dec_ref(v_opt_694_);
lean_dec_ref(v_opts_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_697_, lean_object* v_v_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
if (lean_obj_tag(v_v_698_) == 0)
{
lean_object* v_code_705_; lean_object* v___x_706_; 
v_code_705_ = lean_ctor_get(v_v_698_, 0);
lean_inc_ref(v_code_705_);
lean_dec_ref_known(v_v_698_, 1);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
v___x_706_ = lean_apply_7(v_f_697_, v_code_705_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, lean_box(0));
return v___x_706_;
}
else
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_f_697_);
v_isSharedCheck_715_ = !lean_is_exclusive(v_v_698_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v_v_698_, 0);
lean_dec(v_unused_716_);
v___x_708_ = v_v_698_;
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_v_698_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_box(0);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___y_699_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 0);
lean_ctor_set(v___x_708_, 0, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_717_, lean_object* v_v_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_717_, v_v_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_726_, lean_object* v_f_727_, lean_object* v_v_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_727_, v_v_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_736_, lean_object* v_f_737_, lean_object* v_v_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
uint8_t v_pu_boxed_745_; lean_object* v_res_746_; 
v_pu_boxed_745_ = lean_unbox(v_pu_736_);
v_res_746_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_745_, v_f_737_, v_v_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_746_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_780_, lean_object* v_origDecl_781_, uint8_t v_isMeta_782_, uint8_t v_isPublic_783_, lean_object* v_init_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v_k_792_; lean_object* v_l_793_; lean_object* v_r_794_; lean_object* v___x_795_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; uint8_t v___y_846_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_k_792_ = lean_ctor_get(v_x_785_, 1);
lean_inc(v_k_792_);
v_l_793_ = lean_ctor_get(v_x_785_, 3);
lean_inc(v_l_793_);
v_r_794_ = lean_ctor_get(v_x_785_, 4);
lean_inc(v_r_794_);
lean_dec_ref_known(v_x_785_, 5);
v___x_795_ = lean_box(0);
v___x_848_ = lean_box(0);
lean_inc_ref(v_origDecl_781_);
v___x_849_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_780_, v_origDecl_781_, v_isMeta_782_, v_isPublic_783_, v_init_784_, v_l_793_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_1156_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v_snd_851_ = lean_ctor_get(v_a_850_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_850_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_a_850_, 0);
lean_dec(v_unused_1157_);
v___x_853_ = v_a_850_;
v_isShared_854_ = v_isSharedCheck_1156_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_dec(v_a_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_1156_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___x_855_; uint8_t v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; uint8_t v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; 
v___x_855_ = l_Lean_NameSet_contains(v_snd_851_, v_k_792_);
if (v___x_855_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_env_897_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; uint8_t v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; uint8_t v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; uint8_t v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; uint8_t v___y_950_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; uint8_t v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; uint8_t v___y_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; uint8_t v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; uint8_t v___y_969_; uint8_t v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_977_; lean_object* v___y_978_; uint8_t v___y_979_; lean_object* v___y_980_; uint8_t v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; uint8_t v___y_984_; lean_object* v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; uint8_t v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; uint8_t v___y_1042_; lean_object* v___y_1044_; lean_object* v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; uint8_t v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1072_; uint8_t v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1102_; uint8_t v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; uint8_t v___y_1137_; 
lean_inc(v_k_792_);
v___x_895_ = l_Lean_NameSet_insert(v_snd_851_, v_k_792_);
v___x_896_ = lean_st_ref_get(v___y_790_);
v_env_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_ref(v_env_897_);
lean_dec(v___x_896_);
if (v_isMeta_782_ == 0)
{
v___y_1137_ = v___x_855_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v_isPublic_783_;
goto v___jp_1136_;
}
v___jp_898_:
{
lean_object* v_toSignature_906_; lean_object* v_name_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v___y_904_);
v_toSignature_906_ = lean_ctor_get(v_origDecl_781_, 0);
lean_inc_ref(v_toSignature_906_);
lean_dec_ref(v_origDecl_781_);
v_name_907_ = lean_ctor_get(v_toSignature_906_, 0);
lean_inc(v_name_907_);
lean_dec_ref(v_toSignature_906_);
v___x_908_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_909_ = l_Lean_MessageData_ofConstName(v_name_907_, v___x_855_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = l_Lean_MessageData_ofConstName(v_k_792_, v___x_855_);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_Environment_header(v_env_897_);
lean_dec_ref(v_env_897_);
v___x_918_ = l_Lean_EnvironmentHeader_moduleNames(v___x_917_);
v___x_919_ = lean_array_get(v___x_848_, v___x_918_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___x_918_);
v___x_920_ = l_Lean_MessageData_ofName(v___x_919_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_916_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_923_, v___y_900_, v___y_899_, v___y_901_, v___y_905_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
v___jp_933_:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_897_, v_k_792_);
if (lean_obj_tag(v___x_940_) == 1)
{
lean_object* v_val_941_; uint8_t v___x_942_; 
v_val_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v___x_940_, 1);
lean_inc(v_k_792_);
lean_inc_ref(v_env_897_);
v___x_942_ = l_Lean_isMarkedMeta(v_env_897_, v_k_792_);
if (v___x_942_ == 0)
{
lean_del_object(v___x_853_);
v___y_899_ = v___y_935_;
v___y_900_ = v___y_934_;
v___y_901_ = v___y_936_;
v___y_902_ = v___y_937_;
v___y_903_ = v_val_941_;
v___y_904_ = v___y_938_;
v___y_905_ = v___y_939_;
goto v___jp_898_;
}
else
{
if (v___x_855_ == 0)
{
lean_dec(v_val_941_);
lean_dec_ref(v_env_897_);
v___y_867_ = v___y_937_;
v___y_868_ = v___y_938_;
v___y_869_ = v___y_934_;
v___y_870_ = v___y_935_;
v___y_871_ = v___y_936_;
v___y_872_ = v___y_939_;
goto v___jp_866_;
}
else
{
lean_del_object(v___x_853_);
v___y_899_ = v___y_935_;
v___y_900_ = v___y_934_;
v___y_901_ = v___y_936_;
v___y_902_ = v___y_937_;
v___y_903_ = v_val_941_;
v___y_904_ = v___y_938_;
v___y_905_ = v___y_939_;
goto v___jp_898_;
}
}
}
else
{
lean_dec(v___x_940_);
lean_dec_ref(v_env_897_);
v___y_867_ = v___y_937_;
v___y_868_ = v___y_938_;
v___y_869_ = v___y_934_;
v___y_870_ = v___y_935_;
v___y_871_ = v___y_936_;
v___y_872_ = v___y_939_;
goto v___jp_866_;
}
}
v___jp_943_:
{
if (v___y_950_ == 0)
{
lean_dec_ref(v_env_897_);
lean_del_object(v___x_853_);
v___y_857_ = v___y_947_;
v___y_858_ = v___y_948_;
v___y_859_ = v___y_945_;
v___y_860_ = v___y_944_;
v___y_861_ = v___y_946_;
v___y_862_ = v___y_949_;
goto v___jp_856_;
}
else
{
lean_dec(v_r_794_);
v___y_934_ = v___y_945_;
v___y_935_ = v___y_944_;
v___y_936_ = v___y_946_;
v___y_937_ = v___y_947_;
v___y_938_ = v___y_948_;
v___y_939_ = v___y_949_;
goto v___jp_933_;
}
}
v___jp_951_:
{
if (v___y_958_ == 0)
{
v___y_944_ = v___y_953_;
v___y_945_ = v___y_952_;
v___y_946_ = v___y_954_;
v___y_947_ = v___y_955_;
v___y_948_ = v___y_956_;
v___y_949_ = v___y_957_;
v___y_950_ = v___x_855_;
goto v___jp_943_;
}
else
{
if (v_isMeta_782_ == 0)
{
lean_dec(v_r_794_);
v___y_934_ = v___y_952_;
v___y_935_ = v___y_953_;
v___y_936_ = v___y_954_;
v___y_937_ = v___y_955_;
v___y_938_ = v___y_956_;
v___y_939_ = v___y_957_;
goto v___jp_933_;
}
else
{
v___y_944_ = v___y_953_;
v___y_945_ = v___y_952_;
v___y_946_ = v___y_954_;
v___y_947_ = v___y_955_;
v___y_948_ = v___y_956_;
v___y_949_ = v___y_957_;
v___y_950_ = v___x_855_;
goto v___jp_943_;
}
}
}
v___jp_959_:
{
uint8_t v___x_966_; uint8_t v___x_967_; 
v___x_966_ = 1;
v___x_967_ = l_Lean_instBEqIRPhases_beq(v___y_963_, v___x_966_);
v___y_952_ = v___y_961_;
v___y_953_ = v___y_960_;
v___y_954_ = v___y_962_;
v___y_955_ = v___y_963_;
v___y_956_ = v___y_964_;
v___y_957_ = v___y_965_;
v___y_958_ = v___x_967_;
goto v___jp_951_;
}
v___jp_968_:
{
if (v___y_969_ == 0)
{
v___y_960_ = v___y_973_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_974_;
v___y_963_ = v___y_970_;
v___y_964_ = v___y_971_;
v___y_965_ = v___y_975_;
goto v___jp_959_;
}
else
{
if (v___x_855_ == 0)
{
v___y_952_ = v___y_972_;
v___y_953_ = v___y_973_;
v___y_954_ = v___y_974_;
v___y_955_ = v___y_970_;
v___y_956_ = v___y_971_;
v___y_957_ = v___y_975_;
v___y_958_ = v___x_855_;
goto v___jp_951_;
}
else
{
v___y_960_ = v___y_973_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_974_;
v___y_963_ = v___y_970_;
v___y_964_ = v___y_971_;
v___y_965_ = v___y_975_;
goto v___jp_959_;
}
}
}
v___jp_976_:
{
if (v___y_984_ == 0)
{
v___y_969_ = v___y_979_;
v___y_970_ = v___y_981_;
v___y_971_ = v___y_980_;
v___y_972_ = v___y_978_;
v___y_973_ = v___y_983_;
v___y_974_ = v___y_977_;
v___y_975_ = v___y_982_;
goto v___jp_968_;
}
else
{
lean_object* v___x_985_; 
lean_dec(v___y_980_);
lean_del_object(v___x_853_);
lean_dec(v_r_794_);
v___x_985_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_897_, v_k_792_);
if (lean_obj_tag(v___x_985_) == 1)
{
lean_object* v_toSignature_986_; lean_object* v_val_987_; lean_object* v_name_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_toSignature_986_ = lean_ctor_get(v_origDecl_781_, 0);
lean_inc_ref(v_toSignature_986_);
lean_dec_ref(v_origDecl_781_);
v_val_987_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_985_, 1);
v_name_988_ = lean_ctor_get(v_toSignature_986_, 0);
lean_inc(v_name_988_);
lean_dec_ref(v_toSignature_986_);
v___x_989_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_990_ = l_Lean_MessageData_ofConstName(v_name_988_, v___x_855_);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_MessageData_ofConstName(v_k_792_, v___x_855_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_Environment_header(v_env_897_);
lean_dec_ref(v_env_897_);
v___x_999_ = l_Lean_EnvironmentHeader_moduleNames(v___x_998_);
v___x_1000_ = lean_array_get(v___x_848_, v___x_999_, v_val_987_);
lean_dec(v_val_987_);
lean_dec_ref(v___x_999_);
v___x_1001_ = l_Lean_MessageData_ofName(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1004_, v___y_978_, v___y_983_, v___y_977_, v___y_982_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_toSignature_1014_; lean_object* v_name_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v___x_985_);
lean_dec_ref(v_env_897_);
v_toSignature_1014_ = lean_ctor_get(v_origDecl_781_, 0);
lean_inc_ref(v_toSignature_1014_);
lean_dec_ref(v_origDecl_781_);
v_name_1015_ = lean_ctor_get(v_toSignature_1014_, 0);
lean_inc(v_name_1015_);
lean_dec_ref(v_toSignature_1014_);
v___x_1016_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_1017_ = l_Lean_MessageData_ofConstName(v_name_1015_, v___x_855_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_MessageData_ofConstName(v_k_792_, v___x_855_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1024_, v___y_978_, v___y_983_, v___y_977_, v___y_982_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
v___jp_1034_:
{
if (v___y_1042_ == 0)
{
v___y_977_ = v___y_1035_;
v___y_978_ = v___y_1036_;
v___y_979_ = v___y_1037_;
v___y_980_ = v___y_1038_;
v___y_981_ = v___y_1039_;
v___y_982_ = v___y_1040_;
v___y_983_ = v___y_1041_;
v___y_984_ = v___x_855_;
goto v___jp_976_;
}
else
{
v___y_977_ = v___y_1035_;
v___y_978_ = v___y_1036_;
v___y_979_ = v___y_1037_;
v___y_980_ = v___y_1038_;
v___y_981_ = v___y_1039_;
v___y_982_ = v___y_1040_;
v___y_983_ = v___y_1041_;
v___y_984_ = v_isMeta_782_;
goto v___jp_976_;
}
}
v___jp_1043_:
{
uint8_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 0;
v___x_1052_ = l_Lean_instBEqIRPhases_beq(v___y_1048_, v___x_1051_);
v___y_1035_ = v___y_1044_;
v___y_1036_ = v___y_1045_;
v___y_1037_ = v___y_1046_;
v___y_1038_ = v___y_1047_;
v___y_1039_ = v___y_1048_;
v___y_1040_ = v___y_1049_;
v___y_1041_ = v___y_1050_;
v___y_1042_ = v___x_1052_;
goto v___jp_1034_;
}
v___jp_1053_:
{
uint8_t v___x_1060_; 
lean_inc(v_k_792_);
lean_inc_ref(v_env_897_);
v___x_1060_ = l_Lean_getIRPhases(v_env_897_, v_k_792_);
if (v___y_1059_ == 0)
{
v___y_1044_ = v___y_1054_;
v___y_1045_ = v___y_1055_;
v___y_1046_ = v___y_1059_;
v___y_1047_ = v___y_1056_;
v___y_1048_ = v___x_1060_;
v___y_1049_ = v___y_1057_;
v___y_1050_ = v___y_1058_;
goto v___jp_1043_;
}
else
{
if (v___x_855_ == 0)
{
v___y_1035_ = v___y_1054_;
v___y_1036_ = v___y_1055_;
v___y_1037_ = v___y_1059_;
v___y_1038_ = v___y_1056_;
v___y_1039_ = v___x_1060_;
v___y_1040_ = v___y_1057_;
v___y_1041_ = v___y_1058_;
v___y_1042_ = v___x_855_;
goto v___jp_1034_;
}
else
{
v___y_1044_ = v___y_1054_;
v___y_1045_ = v___y_1055_;
v___y_1046_ = v___y_1059_;
v___y_1047_ = v___y_1056_;
v___y_1048_ = v___x_1060_;
v___y_1049_ = v___y_1057_;
v___y_1050_ = v___y_1058_;
goto v___jp_1043_;
}
}
}
v___jp_1061_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1065_);
v___x_1068_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_1069_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1067_, v___x_1068_);
lean_dec_ref(v___x_1067_);
if (v___x_1069_ == 0)
{
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___y_1063_;
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1066_;
v___y_1058_ = v___y_1064_;
v___y_1059_ = v___x_855_;
goto v___jp_1053_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = l_Lean_Environment_isImportedConst(v_env_897_, v_k_792_);
if (v___x_1070_ == 0)
{
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___y_1063_;
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1066_;
v___y_1058_ = v___y_1064_;
v___y_1059_ = v___x_1069_;
goto v___jp_1053_;
}
else
{
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___y_1063_;
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1066_;
v___y_1058_ = v___y_1064_;
v___y_1059_ = v___x_855_;
goto v___jp_1053_;
}
}
}
v___jp_1071_:
{
lean_object* v_toSignature_1075_; lean_object* v_name_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_toSignature_1075_ = lean_ctor_get(v_origDecl_781_, 0);
lean_inc_ref(v_toSignature_1075_);
lean_dec_ref(v_origDecl_781_);
v_name_1076_ = lean_ctor_get(v_toSignature_1075_, 0);
lean_inc(v_name_1076_);
lean_dec_ref(v_toSignature_1075_);
v___x_1077_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1078_ = l_Lean_MessageData_ofConstName(v_name_1076_, v___y_1073_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_ofConstName(v_k_792_, v___y_1073_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_EnvironmentHeader_moduleNames(v___y_1074_);
v___x_1087_ = lean_array_get(v___x_848_, v___x_1086_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___x_1086_);
v___x_1088_ = l_Lean_MessageData_ofName(v___x_1087_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1085_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1091_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
v___jp_1101_:
{
if (v___y_1105_ == 0)
{
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1102_);
v___y_1062_ = v___x_895_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
v___y_1066_ = v___y_790_;
goto v___jp_1061_;
}
else
{
lean_dec_ref(v_env_897_);
lean_dec(v___x_895_);
lean_del_object(v___x_853_);
lean_dec(v_r_794_);
v___y_1072_ = v___y_1102_;
v___y_1073_ = v___y_1103_;
v___y_1074_ = v___y_1104_;
goto v___jp_1071_;
}
}
v___jp_1106_:
{
if (v___y_1109_ == 0)
{
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
v___y_1062_ = v___x_895_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
v___y_1066_ = v___y_790_;
goto v___jp_1061_;
}
else
{
lean_object* v_toSignature_1110_; lean_object* v_name_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_env_897_);
lean_dec(v___x_895_);
lean_del_object(v___x_853_);
lean_dec(v_r_794_);
v_toSignature_1110_ = lean_ctor_get(v_origDecl_781_, 0);
lean_inc_ref(v_toSignature_1110_);
lean_dec_ref(v_origDecl_781_);
v_name_1111_ = lean_ctor_get(v_toSignature_1110_, 0);
lean_inc(v_name_1111_);
lean_dec_ref(v_toSignature_1110_);
v___x_1112_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1113_ = l_Lean_MessageData_ofConstName(v_name_1111_, v___x_855_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_ofConstName(v_k_792_, v___x_855_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_EnvironmentHeader_moduleNames(v___y_1108_);
v___x_1122_ = lean_array_get(v___x_848_, v___x_1121_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = l_Lean_MessageData_ofName(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1120_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1126_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
v___jp_1136_:
{
if (v___y_1137_ == 0)
{
v___y_1062_ = v___x_895_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
v___y_1066_ = v___y_790_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_897_, v_k_792_);
if (lean_obj_tag(v___x_1138_) == 1)
{
lean_object* v_val_1139_; uint8_t v___x_1140_; 
v_val_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v___x_1138_, 1);
lean_inc(v_k_792_);
lean_inc_ref(v_env_897_);
v___x_1140_ = l_Lean_isMarkedMeta(v_env_897_, v_k_792_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v_modules_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = l_Lean_Environment_header(v_env_897_);
v_modules_1142_ = lean_ctor_get(v___x_1141_, 3);
v___x_1143_ = lean_array_get_size(v_modules_1142_);
v___x_1144_ = lean_nat_dec_lt(v_val_1139_, v___x_1143_);
if (v___x_1144_ == 0)
{
v___y_1102_ = v_val_1139_;
v___y_1103_ = v___x_1140_;
v___y_1104_ = v___x_1141_;
v___y_1105_ = v___x_1140_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1145_; lean_object* v_toImport_1146_; uint8_t v_isExported_1147_; 
v___x_1145_ = lean_array_fget_borrowed(v_modules_1142_, v_val_1139_);
v_toImport_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isExported_1147_ = lean_ctor_get_uint8(v_toImport_1146_, sizeof(void*)*1 + 1);
if (v_isExported_1147_ == 0)
{
lean_dec_ref(v_env_897_);
lean_dec(v___x_895_);
lean_del_object(v___x_853_);
lean_dec(v_r_794_);
v___y_1072_ = v_val_1139_;
v___y_1073_ = v___x_1140_;
v___y_1074_ = v___x_1141_;
goto v___jp_1071_;
}
else
{
v___y_1102_ = v_val_1139_;
v___y_1103_ = v___x_1140_;
v___y_1104_ = v___x_1141_;
v___y_1105_ = v___x_1140_;
goto v___jp_1101_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v_modules_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1148_ = l_Lean_Environment_header(v_env_897_);
v_modules_1149_ = lean_ctor_get(v___x_1148_, 3);
v___x_1150_ = lean_array_get_size(v_modules_1149_);
v___x_1151_ = lean_nat_dec_lt(v_val_1139_, v___x_1150_);
if (v___x_1151_ == 0)
{
v___y_1107_ = v_val_1139_;
v___y_1108_ = v___x_1148_;
v___y_1109_ = v___x_855_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1152_; lean_object* v_toImport_1153_; uint8_t v_isExported_1154_; 
v___x_1152_ = lean_array_fget_borrowed(v_modules_1149_, v_val_1139_);
v_toImport_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isExported_1154_ = lean_ctor_get_uint8(v_toImport_1153_, sizeof(void*)*1 + 1);
if (v_isExported_1154_ == 0)
{
v___y_1107_ = v_val_1139_;
v___y_1108_ = v___x_1148_;
v___y_1109_ = v___x_1140_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v_val_1139_;
v___y_1108_ = v___x_1148_;
v___y_1109_ = v___x_855_;
goto v___jp_1106_;
}
}
}
}
else
{
lean_dec(v___x_1138_);
v___y_1062_ = v___x_895_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
v___y_1066_ = v___y_790_;
goto v___jp_1061_;
}
}
}
}
else
{
lean_del_object(v___x_853_);
lean_dec(v_k_792_);
v_init_784_ = v___x_795_;
v_x_785_ = v_r_794_;
v___y_786_ = v_snd_851_;
goto _start;
}
v___jp_856_:
{
uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = 2;
v___x_864_ = l_Lean_instBEqIRPhases_beq(v___y_857_, v___x_863_);
if (v___x_864_ == 0)
{
if (v_isPublic_783_ == 0)
{
v___y_841_ = v___y_858_;
v___y_842_ = v___y_862_;
v___y_843_ = v___y_860_;
v___y_844_ = v___y_861_;
v___y_845_ = v___y_859_;
v___y_846_ = v___x_855_;
goto v___jp_840_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = l_Lean_isPrivateName(v_k_792_);
v___y_841_ = v___y_858_;
v___y_842_ = v___y_862_;
v___y_843_ = v___y_860_;
v___y_844_ = v___y_861_;
v___y_845_ = v___y_859_;
v___y_846_ = v___x_865_;
goto v___jp_840_;
}
}
else
{
v___y_797_ = v___y_858_;
v___y_798_ = v___y_862_;
v___y_799_ = v___y_860_;
v___y_800_ = v___y_861_;
v___y_801_ = v___y_859_;
goto v___jp_796_;
}
}
v___jp_866_:
{
lean_object* v_toSignature_873_; lean_object* v_name_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec(v___y_868_);
v_toSignature_873_ = lean_ctor_get(v_origDecl_781_, 0);
lean_inc_ref(v_toSignature_873_);
lean_dec_ref(v_origDecl_781_);
v_name_874_ = lean_ctor_get(v_toSignature_873_, 0);
lean_inc(v_name_874_);
lean_dec_ref(v_toSignature_873_);
v___x_875_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_876_ = l_Lean_MessageData_ofConstName(v_name_874_, v___x_855_);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 7);
lean_ctor_set(v___x_853_, 1, v___x_876_);
lean_ctor_set(v___x_853_, 0, v___x_875_);
v___x_878_ = v___x_853_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_894_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v___x_879_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_MessageData_ofConstName(v_k_792_, v___x_855_);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_884_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
else
{
lean_dec(v_r_794_);
lean_dec(v_k_792_);
lean_dec_ref(v_origDecl_781_);
return v___x_849_;
}
v___jp_796_:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_unbox(v_a_803_);
v___x_805_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_792_, v___x_804_, v___y_798_);
lean_dec(v_k_792_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
if (lean_obj_tag(v_a_806_) == 1)
{
lean_object* v_val_807_; uint8_t v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_val_807_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v_a_806_, 1);
v___x_808_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
v___x_809_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_808_);
v___x_810_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_809_, v_val_807_, v_pu_780_);
lean_dec(v_val_807_);
lean_inc_ref(v_origDecl_781_);
v___x_811_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_780_, v_origDecl_781_, v_isMeta_782_, v_isPublic_783_, v___x_810_, v___y_797_, v___y_801_, v___y_799_, v___y_800_, v___y_798_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v_snd_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v_snd_813_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_snd_813_);
lean_dec(v_a_812_);
v_init_784_ = v___x_795_;
v_x_785_ = v_r_794_;
v___y_786_ = v_snd_813_;
goto _start;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_r_794_);
lean_dec_ref(v_origDecl_781_);
v_a_815_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_811_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_811_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_dec(v_a_806_);
lean_dec(v_a_803_);
v_init_784_ = v___x_795_;
v_x_785_ = v_r_794_;
v___y_786_ = v___y_797_;
goto _start;
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_a_803_);
lean_dec(v___y_797_);
lean_dec(v_r_794_);
lean_dec_ref(v_origDecl_781_);
v_a_824_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_805_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_805_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v___y_797_);
lean_dec(v_r_794_);
lean_dec(v_k_792_);
lean_dec_ref(v_origDecl_781_);
v_a_832_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_802_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_802_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
v___jp_840_:
{
if (v___y_846_ == 0)
{
lean_dec(v_k_792_);
v_init_784_ = v___x_795_;
v_x_785_ = v_r_794_;
v___y_786_ = v___y_841_;
goto _start;
}
else
{
v___y_797_ = v___y_841_;
v___y_798_ = v___y_842_;
v___y_799_ = v___y_843_;
v___y_800_ = v___y_844_;
v___y_801_ = v___y_845_;
goto v___jp_796_;
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v_origDecl_781_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_init_784_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___y_786_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t v_pu_1161_, lean_object* v_origDecl_1162_, uint8_t v_isMeta_1163_, uint8_t v_isPublic_1164_, lean_object* v_code_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = l_Lean_NameSet_empty;
v___x_1173_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_1161_, v_code_1165_, v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_1161_, v_origDecl_1162_, v_isMeta_1163_, v_isPublic_1164_, v___x_1174_, v___x_1173_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1192_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1192_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1192_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1190_; 
v_snd_1180_ = lean_ctor_get(v_a_1176_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_a_1176_, 0);
lean_dec(v_unused_1191_);
v___x_1182_ = v_a_1176_;
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_dec(v_a_1176_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1174_);
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_snd_1180_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1185_);
v___x_1187_ = v___x_1178_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1175_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1175_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object* v_pu_1201_, lean_object* v_origDecl_1202_, lean_object* v_isMeta_1203_, lean_object* v_isPublic_1204_, lean_object* v_code_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v_pu_boxed_1212_; uint8_t v_isMeta_boxed_1213_; uint8_t v_isPublic_boxed_1214_; lean_object* v_res_1215_; 
v_pu_boxed_1212_ = lean_unbox(v_pu_1201_);
v_isMeta_boxed_1213_ = lean_unbox(v_isMeta_1203_);
v_isPublic_boxed_1214_ = lean_unbox(v_isPublic_1204_);
v_res_1215_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_boxed_1212_, v_origDecl_1202_, v_isMeta_boxed_1213_, v_isPublic_boxed_1214_, v_code_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t v_pu_1216_, lean_object* v_origDecl_1217_, uint8_t v_isMeta_1218_, uint8_t v_isPublic_1219_, lean_object* v_decl_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_value_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; 
v_value_1227_ = lean_ctor_get(v_decl_1220_, 1);
lean_inc_ref(v_value_1227_);
lean_dec_ref(v_decl_1220_);
v___x_1228_ = lean_box(v_pu_1216_);
v___x_1229_ = lean_box(v_isMeta_1218_);
v___x_1230_ = lean_box(v_isPublic_1219_);
v___f_1231_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1231_, 0, v___x_1228_);
lean_closure_set(v___f_1231_, 1, v_origDecl_1217_);
lean_closure_set(v___f_1231_, 2, v___x_1229_);
lean_closure_set(v___f_1231_, 3, v___x_1230_);
v___x_1232_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_1231_, v_value_1227_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object* v_pu_1233_, lean_object* v_origDecl_1234_, lean_object* v_isMeta_1235_, lean_object* v_isPublic_1236_, lean_object* v_decl_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_pu_boxed_1244_; uint8_t v_isMeta_boxed_1245_; uint8_t v_isPublic_boxed_1246_; lean_object* v_res_1247_; 
v_pu_boxed_1244_ = lean_unbox(v_pu_1233_);
v_isMeta_boxed_1245_ = lean_unbox(v_isMeta_1235_);
v_isPublic_boxed_1246_ = lean_unbox(v_isPublic_1236_);
v_res_1247_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_boxed_1244_, v_origDecl_1234_, v_isMeta_boxed_1245_, v_isPublic_boxed_1246_, v_decl_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object* v_pu_1248_, lean_object* v_origDecl_1249_, lean_object* v_isMeta_1250_, lean_object* v_isPublic_1251_, lean_object* v_init_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v_pu_boxed_1260_; uint8_t v_isMeta_boxed_1261_; uint8_t v_isPublic_boxed_1262_; lean_object* v_res_1263_; 
v_pu_boxed_1260_ = lean_unbox(v_pu_1248_);
v_isMeta_boxed_1261_ = lean_unbox(v_isMeta_1250_);
v_isPublic_boxed_1262_ = lean_unbox(v_isPublic_1251_);
v_res_1263_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_1260_, v_origDecl_1249_, v_isMeta_boxed_1261_, v_isPublic_boxed_1262_, v_init_1252_, v_x_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object* v_opt_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1265_);
v___x_1268_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1267_, v_opt_1264_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = lean_box(v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1271_, v___y_1272_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_opt_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1275_, lean_object* v_origDecl_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v_env_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1342_; 
v___x_1282_ = lean_st_ref_get(v_a_1280_);
v_env_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1282_);
v___x_1284_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1285_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1284_, v_a_1279_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1342_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1342_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1341_; 
v___x_1290_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1291_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1290_, v_a_1279_);
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1341_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1341_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1301_; uint8_t v_isModule_1302_; 
v___x_1301_ = l_Lean_Environment_header(v_env_1283_);
lean_dec_ref(v_env_1283_);
v_isModule_1302_ = lean_ctor_get_uint8(v___x_1301_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1301_);
if (v_isModule_1302_ == 0)
{
lean_dec(v_a_1292_);
lean_del_object(v___x_1288_);
lean_dec(v_a_1286_);
lean_dec_ref(v_origDecl_1276_);
goto v___jp_1296_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_unbox(v_a_1292_);
if (v___x_1304_ == 0)
{
lean_dec(v_a_1292_);
lean_del_object(v___x_1288_);
lean_dec_ref(v_origDecl_1276_);
goto v___jp_1296_;
}
else
{
lean_object* v___x_1305_; lean_object* v_toSignature_1306_; lean_object* v_env_1307_; lean_object* v_name_1308_; uint8_t v___x_1309_; uint8_t v___y_1311_; uint8_t v___x_1333_; uint8_t v___x_1334_; 
lean_del_object(v___x_1294_);
v___x_1305_ = lean_st_ref_get(v_a_1280_);
v_toSignature_1306_ = lean_ctor_get(v_origDecl_1276_, 0);
v_env_1307_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1307_);
lean_dec(v___x_1305_);
v_name_1308_ = lean_ctor_get(v_toSignature_1306_, 0);
lean_inc(v_name_1308_);
v___x_1309_ = l_Lean_getIRPhases(v_env_1307_, v_name_1308_);
v___x_1333_ = 2;
v___x_1334_ = l_Lean_instBEqIRPhases_beq(v___x_1309_, v___x_1333_);
if (v___x_1334_ == 0)
{
uint8_t v___x_1335_; 
lean_del_object(v___x_1288_);
v___x_1335_ = l_Lean_isPrivateName(v_name_1308_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_unbox(v_a_1292_);
lean_dec(v_a_1292_);
v___y_1311_ = v___x_1336_;
goto v___jp_1310_;
}
else
{
lean_dec(v_a_1292_);
v___y_1311_ = v___x_1334_;
goto v___jp_1310_;
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_dec(v_a_1292_);
lean_dec_ref(v_origDecl_1276_);
v___x_1337_ = lean_box(0);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1337_);
v___x_1339_ = v___x_1288_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
v___jp_1310_:
{
uint8_t v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = 1;
v___x_1313_ = l_Lean_instBEqIRPhases_beq(v___x_1309_, v___x_1312_);
v___x_1314_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1276_);
v___x_1315_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1275_, v_origDecl_1276_, v___x_1313_, v___y_1311_, v_origDecl_1276_, v___x_1314_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_fst_1320_; lean_object* v___x_1322_; 
v_fst_1320_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_fst_1320_);
lean_dec(v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_fst_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_fst_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1315_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1315_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1292_);
lean_del_object(v___x_1288_);
lean_dec_ref(v_origDecl_1276_);
goto v___jp_1296_;
}
}
v___jp_1296_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(0);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1297_);
v___x_1299_ = v___x_1294_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1343_, lean_object* v_origDecl_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
uint8_t v_pu_boxed_1350_; lean_object* v_res_1351_; 
v_pu_boxed_1350_ = lean_unbox(v_pu_1343_);
v_res_1351_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1350_, v_origDecl_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1352_, v___y_1355_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v_opt_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(uint8_t v_isExporting_1366_, lean_object* v___x_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v_env_1376_; lean_object* v_nextMacroScope_1377_; lean_object* v_ngen_1378_; lean_object* v_auxDeclNGen_1379_; lean_object* v_traceState_1380_; lean_object* v_recordedDeps_1381_; lean_object* v_messages_1382_; lean_object* v_infoState_1383_; lean_object* v_snapshotTasks_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1396_; 
v___x_1375_ = lean_st_ref_take(v___y_1373_);
v_env_1376_ = lean_ctor_get(v___x_1375_, 0);
v_nextMacroScope_1377_ = lean_ctor_get(v___x_1375_, 1);
v_ngen_1378_ = lean_ctor_get(v___x_1375_, 2);
v_auxDeclNGen_1379_ = lean_ctor_get(v___x_1375_, 3);
v_traceState_1380_ = lean_ctor_get(v___x_1375_, 4);
v_recordedDeps_1381_ = lean_ctor_get(v___x_1375_, 6);
v_messages_1382_ = lean_ctor_get(v___x_1375_, 7);
v_infoState_1383_ = lean_ctor_get(v___x_1375_, 8);
v_snapshotTasks_1384_ = lean_ctor_get(v___x_1375_, 9);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___x_1375_, 5);
lean_dec(v_unused_1397_);
v___x_1386_ = v___x_1375_;
v_isShared_1387_ = v_isSharedCheck_1396_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snapshotTasks_1384_);
lean_inc(v_infoState_1383_);
lean_inc(v_messages_1382_);
lean_inc(v_recordedDeps_1381_);
lean_inc(v_traceState_1380_);
lean_inc(v_auxDeclNGen_1379_);
lean_inc(v_ngen_1378_);
lean_inc(v_nextMacroScope_1377_);
lean_inc(v_env_1376_);
lean_dec(v___x_1375_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1396_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Lean_Environment_setExporting(v_env_1376_, v_isExporting_1366_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 5, v___x_1367_);
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_nextMacroScope_1377_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_ngen_1378_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_auxDeclNGen_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_traceState_1380_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_recordedDeps_1381_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_messages_1382_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v_infoState_1383_);
lean_ctor_set(v_reuseFailAlloc_1395_, 9, v_snapshotTasks_1384_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_st_ref_put(v___y_1373_, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1388_);
lean_ctor_set(v___x_1393_, 1, v___y_1369_);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(lean_object* v_isExporting_1398_, lean_object* v___x_1399_, lean_object* v_x_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_isExporting_boxed_1407_; lean_object* v_res_1408_; 
v_isExporting_boxed_1407_ = lean_unbox(v_isExporting_1398_);
v_res_1408_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_boxed_1407_, v___x_1399_, v_x_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_x_1400_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(lean_object* v___f_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v_a_x3f_1415_){
_start:
{
if (lean_obj_tag(v_a_x3f_1415_) == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(0);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
v___x_1418_ = lean_apply_7(v___f_1409_, v___x_1417_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, lean_box(0));
return v___x_1418_;
}
else
{
lean_object* v_val_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v___y_1410_);
v_val_1419_ = lean_ctor_get(v_a_x3f_1415_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_a_x3f_1415_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1421_ = v_a_x3f_1415_;
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_val_1419_);
lean_dec(v_a_x3f_1415_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_fst_1423_; lean_object* v_snd_1424_; lean_object* v___x_1426_; 
v_fst_1423_ = lean_ctor_get(v_val_1419_, 0);
lean_inc(v_fst_1423_);
v_snd_1424_ = lean_ctor_get(v_val_1419_, 1);
lean_inc(v_snd_1424_);
lean_dec(v_val_1419_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_fst_1423_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_fst_1423_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
v___x_1427_ = lean_apply_7(v___f_1409_, v___x_1426_, v_snd_1424_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, lean_box(0));
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(lean_object* v___f_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v_a_x3f_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v_a_x3f_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object* v_x_1439_, uint8_t v_isExporting_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_env_1448_; lean_object* v___x_1449_; uint8_t v_isModule_1450_; 
v___x_1447_ = lean_st_ref_get(v___y_1445_);
v_env_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc_ref(v_env_1448_);
lean_dec(v___x_1447_);
v___x_1449_ = l_Lean_Environment_header(v_env_1448_);
v_isModule_1450_ = lean_ctor_get_uint8(v___x_1449_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1449_);
if (v_isModule_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref(v_env_1448_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1451_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1451_;
}
else
{
uint8_t v_isExporting_1452_; 
v_isExporting_1452_ = lean_ctor_get_uint8(v_env_1448_, sizeof(void*)*13);
lean_dec_ref(v_env_1448_);
if (v_isExporting_1440_ == 0)
{
if (v_isExporting_1452_ == 0)
{
lean_object* v___x_1532_; 
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1532_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1532_;
}
else
{
goto v___jp_1453_;
}
}
else
{
if (v_isExporting_1452_ == 0)
{
goto v___jp_1453_;
}
else
{
lean_object* v___x_1533_; 
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1533_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1533_;
}
}
v___jp_1453_:
{
lean_object* v___x_1454_; lean_object* v_env_1455_; lean_object* v_nextMacroScope_1456_; lean_object* v_ngen_1457_; lean_object* v_auxDeclNGen_1458_; lean_object* v_traceState_1459_; lean_object* v_recordedDeps_1460_; lean_object* v_messages_1461_; lean_object* v_infoState_1462_; lean_object* v_snapshotTasks_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1530_; 
v___x_1454_ = lean_st_ref_take(v___y_1445_);
v_env_1455_ = lean_ctor_get(v___x_1454_, 0);
v_nextMacroScope_1456_ = lean_ctor_get(v___x_1454_, 1);
v_ngen_1457_ = lean_ctor_get(v___x_1454_, 2);
v_auxDeclNGen_1458_ = lean_ctor_get(v___x_1454_, 3);
v_traceState_1459_ = lean_ctor_get(v___x_1454_, 4);
v_recordedDeps_1460_ = lean_ctor_get(v___x_1454_, 6);
v_messages_1461_ = lean_ctor_get(v___x_1454_, 7);
v_infoState_1462_ = lean_ctor_get(v___x_1454_, 8);
v_snapshotTasks_1463_ = lean_ctor_get(v___x_1454_, 9);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1454_, 5);
lean_dec(v_unused_1531_);
v___x_1465_ = v___x_1454_;
v_isShared_1466_ = v_isSharedCheck_1530_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_snapshotTasks_1463_);
lean_inc(v_infoState_1462_);
lean_inc(v_messages_1461_);
lean_inc(v_recordedDeps_1460_);
lean_inc(v_traceState_1459_);
lean_inc(v_auxDeclNGen_1458_);
lean_inc(v_ngen_1457_);
lean_inc(v_nextMacroScope_1456_);
lean_inc(v_env_1455_);
lean_dec(v___x_1454_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1530_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___f_1470_; lean_object* v___x_1472_; 
v___x_1467_ = l_Lean_Environment_setExporting(v_env_1455_, v_isExporting_1440_);
v___x_1468_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1469_ = lean_box(v_isExporting_1452_);
v___f_1470_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1470_, 0, v___x_1469_);
lean_closure_set(v___f_1470_, 1, v___x_1468_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 5, v___x_1468_);
lean_ctor_set(v___x_1465_, 0, v___x_1467_);
v___x_1472_ = v___x_1465_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_nextMacroScope_1456_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_ngen_1457_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_auxDeclNGen_1458_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_traceState_1459_);
lean_ctor_set(v_reuseFailAlloc_1529_, 5, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1529_, 6, v_recordedDeps_1460_);
lean_ctor_set(v_reuseFailAlloc_1529_, 7, v_messages_1461_);
lean_ctor_set(v_reuseFailAlloc_1529_, 8, v_infoState_1462_);
lean_ctor_set(v_reuseFailAlloc_1529_, 9, v_snapshotTasks_1463_);
v___x_1472_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v_r_1474_; 
v___x_1473_ = lean_st_ref_put(v___y_1445_, v___x_1472_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
v_r_1474_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
if (lean_obj_tag(v_r_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1509_; 
v_a_1475_ = lean_ctor_get(v_r_1474_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_r_1474_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1477_ = v_r_1474_;
v_isShared_1478_ = v_isSharedCheck_1509_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v_r_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1509_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
lean_inc(v_a_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 1);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1470_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___x_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1499_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1499_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1499_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1497_; 
v_fst_1486_ = lean_ctor_get(v_a_1475_, 0);
lean_inc(v_fst_1486_);
lean_dec(v_a_1475_);
v_snd_1487_ = lean_ctor_get(v_a_1482_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1482_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v_a_1482_, 0);
lean_dec(v_unused_1498_);
v___x_1489_ = v_a_1482_;
v_isShared_1490_ = v_isSharedCheck_1497_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v_a_1482_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1497_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_fst_1486_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_fst_1486_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_snd_1487_);
v___x_1492_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1492_);
v___x_1494_ = v___x_1484_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1475_);
v_a_1500_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1481_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1481_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_a_1510_ = lean_ctor_get(v_r_1474_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v_r_1474_, 1);
v___x_1511_ = lean_box(0);
v___x_1512_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1470_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___x_1511_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1512_, 0);
lean_dec(v_unused_1520_);
v___x_1514_ = v___x_1512_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v___x_1512_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 0, v_a_1510_);
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1510_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_a_1510_);
v_a_1521_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1512_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1512_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_x_1534_, lean_object* v_isExporting_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_isExporting_boxed_1542_; lean_object* v_res_1543_; 
v_isExporting_boxed_1542_ = lean_unbox(v_isExporting_1535_);
v_res_1543_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1534_, v_isExporting_boxed_1542_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_00_u03b1_1544_, lean_object* v_x_1545_, uint8_t v_isExporting_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1545_, v_isExporting_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_x_1555_, lean_object* v_isExporting_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v_isExporting_boxed_1563_; lean_object* v_res_1564_; 
v_isExporting_boxed_1563_ = lean_unbox(v_isExporting_1556_);
v_res_1564_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_1554_, v_x_1555_, v_isExporting_boxed_1563_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(lean_object* v_opt_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1569_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1567_);
v___x_1570_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1569_, v_opt_1565_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = lean_box(v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___y_1566_);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(lean_object* v_opt_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_1574_, v___y_1575_, v___y_1576_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v_opt_1574_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(lean_object* v_cls_1579_, lean_object* v_msg_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_ref_1587_; lean_object* v___x_1588_; lean_object* v_env_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_ref_1587_ = lean_ctor_get(v___y_1584_, 2);
v___x_1588_ = lean_st_ref_get(v___y_1585_);
v_env_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc_ref(v_env_1589_);
lean_dec(v___x_1588_);
v___x_1590_ = lean_st_ref_get(v___y_1583_);
v___x_1591_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1582_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1652_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1652_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1652_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_lctx_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1650_; 
v_lctx_1596_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1590_, 1);
lean_dec(v_unused_1651_);
v___x_1598_ = v___x_1590_;
v_isShared_1599_ = v_isSharedCheck_1650_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_lctx_1596_);
lean_dec(v___x_1590_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1650_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1600_ = lean_unbox(v_a_1592_);
lean_dec(v_a_1592_);
v___x_1601_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1596_, v___x_1600_);
lean_dec_ref(v_lctx_1596_);
v___x_1602_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1584_);
v___x_1603_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_1604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1604_, 0, v_env_1589_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
lean_ctor_set(v___x_1604_, 2, v___x_1601_);
lean_ctor_set(v___x_1604_, 3, v___x_1602_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 3);
lean_ctor_set(v___x_1598_, 1, v_msg_1580_);
lean_ctor_set(v___x_1598_, 0, v___x_1604_);
v___x_1606_ = v___x_1598_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_msg_1580_);
v___x_1606_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v_traceState_1608_; lean_object* v_env_1609_; lean_object* v_nextMacroScope_1610_; lean_object* v_ngen_1611_; lean_object* v_auxDeclNGen_1612_; lean_object* v_cache_1613_; lean_object* v_recordedDeps_1614_; lean_object* v_messages_1615_; lean_object* v_infoState_1616_; lean_object* v_snapshotTasks_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1648_; 
v___x_1607_ = lean_st_ref_take(v___y_1585_);
v_traceState_1608_ = lean_ctor_get(v___x_1607_, 4);
v_env_1609_ = lean_ctor_get(v___x_1607_, 0);
v_nextMacroScope_1610_ = lean_ctor_get(v___x_1607_, 1);
v_ngen_1611_ = lean_ctor_get(v___x_1607_, 2);
v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1607_, 3);
v_cache_1613_ = lean_ctor_get(v___x_1607_, 5);
v_recordedDeps_1614_ = lean_ctor_get(v___x_1607_, 6);
v_messages_1615_ = lean_ctor_get(v___x_1607_, 7);
v_infoState_1616_ = lean_ctor_get(v___x_1607_, 8);
v_snapshotTasks_1617_ = lean_ctor_get(v___x_1607_, 9);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1619_ = v___x_1607_;
v_isShared_1620_ = v_isSharedCheck_1648_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snapshotTasks_1617_);
lean_inc(v_infoState_1616_);
lean_inc(v_messages_1615_);
lean_inc(v_recordedDeps_1614_);
lean_inc(v_cache_1613_);
lean_inc(v_traceState_1608_);
lean_inc(v_auxDeclNGen_1612_);
lean_inc(v_ngen_1611_);
lean_inc(v_nextMacroScope_1610_);
lean_inc(v_env_1609_);
lean_dec(v___x_1607_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1648_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
uint64_t v_tid_1621_; lean_object* v_traces_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1647_; 
v_tid_1621_ = lean_ctor_get_uint64(v_traceState_1608_, sizeof(void*)*1);
v_traces_1622_ = lean_ctor_get(v_traceState_1608_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_traceState_1608_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1624_ = v_traceState_1608_;
v_isShared_1625_ = v_isSharedCheck_1647_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_traces_1622_);
lean_dec(v_traceState_1608_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1647_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; double v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_1629_ = 0;
v___x_1630_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1631_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1631_, 0, v_cls_1579_);
lean_ctor_set(v___x_1631_, 1, v___x_1627_);
lean_ctor_set(v___x_1631_, 2, v___x_1630_);
lean_ctor_set_float(v___x_1631_, sizeof(void*)*3, v___x_1628_);
lean_ctor_set_float(v___x_1631_, sizeof(void*)*3 + 8, v___x_1628_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*3 + 16, v___x_1629_);
v___x_1632_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_1633_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1606_);
lean_ctor_set(v___x_1633_, 2, v___x_1632_);
lean_inc(v_ref_1587_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_ref_1587_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_PersistentArray_push___redArg(v_traces_1622_, v___x_1634_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1635_);
v___x_1637_ = v___x_1624_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1635_);
lean_ctor_set_uint64(v_reuseFailAlloc_1646_, sizeof(void*)*1, v_tid_1621_);
v___x_1637_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v___x_1637_);
v___x_1639_ = v___x_1619_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_env_1609_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_nextMacroScope_1610_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_ngen_1611_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_auxDeclNGen_1612_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1645_, 5, v_cache_1613_);
lean_ctor_set(v_reuseFailAlloc_1645_, 6, v_recordedDeps_1614_);
lean_ctor_set(v_reuseFailAlloc_1645_, 7, v_messages_1615_);
lean_ctor_set(v_reuseFailAlloc_1645_, 8, v_infoState_1616_);
lean_ctor_set(v_reuseFailAlloc_1645_, 9, v_snapshotTasks_1617_);
v___x_1639_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = lean_st_ref_put(v___y_1585_, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1626_);
lean_ctor_set(v___x_1641_, 1, v___y_1581_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1641_);
v___x_1643_ = v___x_1594_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
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
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v___x_1590_);
lean_dec_ref(v_env_1589_);
lean_dec(v___y_1581_);
lean_dec_ref(v_msg_1580_);
lean_dec(v_cls_1579_);
v_a_1653_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1591_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1591_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7___boxed(lean_object* v_cls_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1661_, v_msg_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___lam__0(lean_object* v___x_1670_, lean_object* v_entry_1671_, lean_object* v_s_1672_){
_start:
{
lean_object* v_addEntryFn_1673_; lean_object* v_importedEntries_1674_; lean_object* v_state_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_addEntryFn_1673_ = lean_ctor_get(v___x_1670_, 3);
lean_inc(v_addEntryFn_1673_);
lean_dec_ref(v___x_1670_);
v_importedEntries_1674_ = lean_ctor_get(v_s_1672_, 0);
v_state_1675_ = lean_ctor_get(v_s_1672_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_s_1672_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_s_1672_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_state_1675_);
lean_inc(v_importedEntries_1674_);
lean_dec(v_s_1672_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_state_1679_; lean_object* v___x_1681_; 
v_state_1679_ = lean_apply_2(v_addEntryFn_1673_, v_state_1675_, v_entry_1671_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v_state_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_importedEntries_1674_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_state_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object* v_keys_1684_, lean_object* v_i_1685_, lean_object* v_k_1686_){
_start:
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_array_get_size(v_keys_1684_);
v___x_1688_ = lean_nat_dec_lt(v_i_1685_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec(v_i_1685_);
return v___x_1688_;
}
else
{
lean_object* v_k_x27_1689_; uint8_t v___x_1690_; 
v_k_x27_1689_ = lean_array_fget_borrowed(v_keys_1684_, v_i_1685_);
v___x_1690_ = l_Lean_instBEqExtraModUse_beq(v_k_1686_, v_k_x27_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_add(v_i_1685_, v___x_1691_);
lean_dec(v_i_1685_);
v_i_1685_ = v___x_1692_;
goto _start;
}
else
{
lean_dec(v_i_1685_);
return v___x_1688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1694_, lean_object* v_i_1695_, lean_object* v_k_1696_){
_start:
{
uint8_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_1694_, v_i_1695_, v_k_1696_);
lean_dec_ref(v_k_1696_);
lean_dec_ref(v_keys_1694_);
v_r_1698_ = lean_box(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1699_, size_t v_x_1700_, lean_object* v_x_1701_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v_es_1702_; lean_object* v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v_j_1706_; lean_object* v___x_1707_; 
v_es_1702_ = lean_ctor_get(v_x_1699_, 0);
v___x_1703_ = lean_box(2);
v___x_1704_ = ((size_t)31ULL);
v___x_1705_ = lean_usize_land(v_x_1700_, v___x_1704_);
v_j_1706_ = lean_usize_to_nat(v___x_1705_);
v___x_1707_ = lean_array_get_borrowed(v___x_1703_, v_es_1702_, v_j_1706_);
lean_dec(v_j_1706_);
switch(lean_obj_tag(v___x_1707_))
{
case 0:
{
lean_object* v_key_1708_; uint8_t v___x_1709_; 
v_key_1708_ = lean_ctor_get(v___x_1707_, 0);
v___x_1709_ = l_Lean_instBEqExtraModUse_beq(v_x_1701_, v_key_1708_);
return v___x_1709_;
}
case 1:
{
lean_object* v_node_1710_; size_t v___x_1711_; size_t v___x_1712_; 
v_node_1710_ = lean_ctor_get(v___x_1707_, 0);
v___x_1711_ = ((size_t)5ULL);
v___x_1712_ = lean_usize_shift_right(v_x_1700_, v___x_1711_);
v_x_1699_ = v_node_1710_;
v_x_1700_ = v___x_1712_;
goto _start;
}
default: 
{
uint8_t v___x_1714_; 
v___x_1714_ = 0;
return v___x_1714_;
}
}
}
else
{
lean_object* v_ks_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_ks_1715_ = lean_ctor_get(v_x_1699_, 0);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_1715_, v___x_1716_, v_x_1701_);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
size_t v_x_26923__boxed_1721_; uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_x_26923__boxed_1721_ = lean_unbox_usize(v_x_1719_);
lean_dec(v_x_1719_);
v_res_1722_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1718_, v_x_26923__boxed_1721_, v_x_1720_);
lean_dec_ref(v_x_1720_);
lean_dec_ref(v_x_1718_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
uint64_t v___x_1726_; size_t v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = l_Lean_instHashableExtraModUse_hash(v_x_1725_);
v___x_1727_ = lean_uint64_to_usize(v___x_1726_);
v___x_1728_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1724_, v___x_1727_, v_x_1725_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1729_, lean_object* v_x_1730_){
_start:
{
uint8_t v_res_1731_; lean_object* v_r_1732_; 
v_res_1731_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_1729_, v_x_1730_);
lean_dec_ref(v_x_1730_);
lean_dec_ref(v_x_1729_);
v_r_1732_ = lean_box(v_res_1731_);
return v_r_1732_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3));
v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
return v___x_1739_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5));
v___x_1742_ = l_Lean_stringToMessageData(v___x_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1744_ = l_Lean_stringToMessageData(v___x_1743_);
return v___x_1744_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v_cls_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_cls_1745_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2));
v___x_1746_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1747_ = l_Lean_Name_append(v___x_1746_, v_cls_1745_);
return v___x_1747_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9));
v___x_1750_ = l_Lean_stringToMessageData(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11));
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object* v_mod_1758_, uint8_t v_isMeta_1759_, lean_object* v_hint_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_env_1787_; uint8_t v_isExporting_1788_; lean_object* v_entry_1789_; lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1785_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0);
v___x_1786_ = lean_st_ref_get(v___y_1765_);
v_env_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc_ref(v_env_1787_);
lean_dec(v___x_1786_);
v_isExporting_1788_ = lean_ctor_get_uint8(v_env_1787_, sizeof(void*)*13);
lean_dec_ref(v_env_1787_);
lean_inc(v_mod_1758_);
v_entry_1789_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1789_, 0, v_mod_1758_);
lean_ctor_set_uint8(v_entry_1789_, sizeof(void*)*1, v_isExporting_1788_);
lean_ctor_set_uint8(v_entry_1789_, sizeof(void*)*1 + 1, v_isMeta_1759_);
v___x_1790_ = lean_st_ref_get(v___y_1765_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1792_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1793_ = lean_box(1);
v___x_1794_ = lean_box(0);
v___x_1795_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1785_, v___x_1792_, v_env_1791_, v___x_1793_, v___x_1794_);
v___x_1796_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_1795_, v_entry_1789_);
lean_dec(v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v_toCold_1797_; lean_object* v_options_1798_; lean_object* v_inheritedTraceOptions_1799_; uint8_t v_hasTrace_1800_; lean_object* v___f_1801_; uint8_t v___x_1802_; lean_object* v___y_1804_; lean_object* v___y_1805_; 
v_toCold_1797_ = lean_ctor_get(v___y_1764_, 0);
v_options_1798_ = lean_ctor_get(v_toCold_1797_, 2);
v_inheritedTraceOptions_1799_ = lean_ctor_get(v_toCold_1797_, 11);
v_hasTrace_1800_ = lean_ctor_get_uint8(v_options_1798_, sizeof(void*)*1);
v___f_1801_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_1801_, 0, v___x_1792_);
lean_closure_set(v___f_1801_, 1, v_entry_1789_);
v___x_1802_ = 1;
if (v_hasTrace_1800_ == 0)
{
lean_dec(v_hint_1760_);
lean_dec(v_mod_1758_);
v___y_1804_ = v___y_1761_;
v___y_1805_ = v___y_1765_;
goto v___jp_1803_;
}
else
{
lean_object* v_cls_1823_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_cls_1823_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2));
v___x_1845_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
v___x_1846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1799_, v_options_1798_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_dec(v_hint_1760_);
lean_dec(v_mod_1758_);
v___y_1804_ = v___y_1761_;
v___y_1805_ = v___y_1765_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1847_; lean_object* v___y_1849_; 
v___x_1847_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
if (v_isExporting_1788_ == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15));
v___y_1849_ = v___x_1856_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1857_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16));
v___y_1849_ = v___x_1857_;
goto v___jp_1848_;
}
v___jp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_inc_ref(v___y_1849_);
v___x_1850_ = l_Lean_stringToMessageData(v___y_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1847_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
if (v_isMeta_1759_ == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13));
v___y_1832_ = v___x_1853_;
v___y_1833_ = v___x_1854_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14));
v___y_1832_ = v___x_1853_;
v___y_1833_ = v___x_1855_;
goto v___jp_1831_;
}
}
}
v___jp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___y_1825_);
lean_ctor_set(v___x_1827_, 1, v___y_1826_);
v___x_1828_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1823_, v___x_1827_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v_snd_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v_snd_1830_ = lean_ctor_get(v_a_1829_, 1);
lean_inc(v_snd_1830_);
lean_dec(v_a_1829_);
v___y_1804_ = v_snd_1830_;
v___y_1805_ = v___y_1765_;
goto v___jp_1803_;
}
else
{
lean_dec_ref(v___f_1801_);
return v___x_1828_;
}
}
v___jp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
lean_inc_ref(v___y_1833_);
v___x_1834_ = l_Lean_stringToMessageData(v___y_1833_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___y_1832_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_MessageData_ofName(v_mod_1758_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_Name_isAnonymous(v_hint_1760_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
v___x_1842_ = l_Lean_MessageData_ofName(v_hint_1760_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___y_1825_ = v___x_1839_;
v___y_1826_ = v___x_1843_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1844_; 
lean_dec(v_hint_1760_);
v___x_1844_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7);
v___y_1825_ = v___x_1839_;
v___y_1826_ = v___x_1844_;
goto v___jp_1824_;
}
}
}
v___jp_1803_:
{
lean_object* v___x_1806_; lean_object* v_toEnvExtension_1807_; lean_object* v_env_1808_; lean_object* v_nextMacroScope_1809_; lean_object* v_ngen_1810_; lean_object* v_auxDeclNGen_1811_; lean_object* v_traceState_1812_; lean_object* v_recordedDeps_1813_; lean_object* v_messages_1814_; lean_object* v_infoState_1815_; lean_object* v_snapshotTasks_1816_; lean_object* v_asyncMode_1817_; uint8_t v_logWrites_1818_; lean_object* v___x_1819_; 
v___x_1806_ = lean_st_ref_take(v___y_1805_);
v_toEnvExtension_1807_ = lean_ctor_get(v___x_1792_, 0);
v_env_1808_ = lean_ctor_get(v___x_1806_, 0);
lean_inc_ref(v_env_1808_);
v_nextMacroScope_1809_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_nextMacroScope_1809_);
v_ngen_1810_ = lean_ctor_get(v___x_1806_, 2);
lean_inc_ref(v_ngen_1810_);
v_auxDeclNGen_1811_ = lean_ctor_get(v___x_1806_, 3);
lean_inc_ref(v_auxDeclNGen_1811_);
v_traceState_1812_ = lean_ctor_get(v___x_1806_, 4);
lean_inc_ref(v_traceState_1812_);
v_recordedDeps_1813_ = lean_ctor_get(v___x_1806_, 6);
lean_inc_ref(v_recordedDeps_1813_);
v_messages_1814_ = lean_ctor_get(v___x_1806_, 7);
lean_inc_ref(v_messages_1814_);
v_infoState_1815_ = lean_ctor_get(v___x_1806_, 8);
lean_inc_ref(v_infoState_1815_);
v_snapshotTasks_1816_ = lean_ctor_get(v___x_1806_, 9);
lean_inc_ref(v_snapshotTasks_1816_);
lean_dec(v___x_1806_);
v_asyncMode_1817_ = lean_ctor_get(v_toEnvExtension_1807_, 2);
v_logWrites_1818_ = lean_ctor_get_uint8(v_toEnvExtension_1807_, sizeof(void*)*6);
v___x_1819_ = lean_box(0);
if (v_logWrites_1818_ == 0)
{
lean_object* v___x_1820_; 
lean_inc_ref(v_toEnvExtension_1807_);
v___x_1820_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1807_, v_env_1808_, v___f_1801_, v_asyncMode_1817_, v___x_1794_, v___x_1802_);
v___y_1768_ = v___y_1804_;
v___y_1769_ = v___x_1819_;
v___y_1770_ = v_messages_1814_;
v___y_1771_ = v_ngen_1810_;
v___y_1772_ = v_infoState_1815_;
v___y_1773_ = v_auxDeclNGen_1811_;
v___y_1774_ = v_nextMacroScope_1809_;
v___y_1775_ = v_traceState_1812_;
v___y_1776_ = v___y_1805_;
v___y_1777_ = v_recordedDeps_1813_;
v___y_1778_ = v_snapshotTasks_1816_;
v___y_1779_ = v___x_1820_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_inc_ref_n(v_toEnvExtension_1807_, 2);
v___x_1821_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1807_, v_env_1808_);
lean_dec_ref(v_env_1808_);
v___x_1822_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1807_, v___x_1821_, v___f_1801_, v_asyncMode_1817_, v___x_1794_, v___x_1802_);
v___y_1768_ = v___y_1804_;
v___y_1769_ = v___x_1819_;
v___y_1770_ = v_messages_1814_;
v___y_1771_ = v_ngen_1810_;
v___y_1772_ = v_infoState_1815_;
v___y_1773_ = v_auxDeclNGen_1811_;
v___y_1774_ = v_nextMacroScope_1809_;
v___y_1775_ = v_traceState_1812_;
v___y_1776_ = v___y_1805_;
v___y_1777_ = v_recordedDeps_1813_;
v___y_1778_ = v_snapshotTasks_1816_;
v___y_1779_ = v___x_1822_;
goto v___jp_1767_;
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec_ref_known(v_entry_1789_, 1);
lean_dec(v_hint_1760_);
lean_dec(v_mod_1758_);
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___y_1761_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
v___jp_1767_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1781_, 0, v___y_1779_);
lean_ctor_set(v___x_1781_, 1, v___y_1774_);
lean_ctor_set(v___x_1781_, 2, v___y_1771_);
lean_ctor_set(v___x_1781_, 3, v___y_1773_);
lean_ctor_set(v___x_1781_, 4, v___y_1775_);
lean_ctor_set(v___x_1781_, 5, v___x_1780_);
lean_ctor_set(v___x_1781_, 6, v___y_1777_);
lean_ctor_set(v___x_1781_, 7, v___y_1770_);
lean_ctor_set(v___x_1781_, 8, v___y_1772_);
lean_ctor_set(v___x_1781_, 9, v___y_1778_);
v___x_1782_ = lean_st_ref_put(v___y_1776_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___y_1769_);
lean_ctor_set(v___x_1783_, 1, v___y_1768_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object* v_mod_1861_, lean_object* v_isMeta_1862_, lean_object* v_hint_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v_isMeta_boxed_1870_; lean_object* v_res_1871_; 
v_isMeta_boxed_1870_ = lean_unbox(v_isMeta_1862_);
v_res_1871_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_1861_, v_isMeta_boxed_1870_, v_hint_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object* v_a_1872_, lean_object* v_x_1873_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_box(0);
return v___x_1874_;
}
else
{
lean_object* v_key_1875_; lean_object* v_value_1876_; lean_object* v_tail_1877_; uint8_t v___x_1878_; 
v_key_1875_ = lean_ctor_get(v_x_1873_, 0);
v_value_1876_ = lean_ctor_get(v_x_1873_, 1);
v_tail_1877_ = lean_ctor_get(v_x_1873_, 2);
v___x_1878_ = lean_name_eq(v_key_1875_, v_a_1872_);
if (v___x_1878_ == 0)
{
v_x_1873_ = v_tail_1877_;
goto _start;
}
else
{
lean_object* v___x_1880_; 
lean_inc(v_value_1876_);
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_value_1876_);
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1881_, v_x_1882_);
lean_dec(v_x_1882_);
lean_dec(v_a_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object* v_m_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_buckets_1886_; lean_object* v___x_1887_; uint64_t v___y_1889_; 
v_buckets_1886_ = lean_ctor_get(v_m_1884_, 1);
v___x_1887_ = lean_array_get_size(v_buckets_1886_);
if (lean_obj_tag(v_a_1885_) == 0)
{
uint64_t v___x_1903_; 
v___x_1903_ = 1723ULL;
v___y_1889_ = v___x_1903_;
goto v___jp_1888_;
}
else
{
uint64_t v_hash_1904_; 
v_hash_1904_ = lean_ctor_get_uint64(v_a_1885_, sizeof(void*)*2);
v___y_1889_ = v_hash_1904_;
goto v___jp_1888_;
}
v___jp_1888_:
{
uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v_fold_1892_; uint64_t v___x_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1890_ = 32ULL;
v___x_1891_ = lean_uint64_shift_right(v___y_1889_, v___x_1890_);
v_fold_1892_ = lean_uint64_xor(v___y_1889_, v___x_1891_);
v___x_1893_ = 16ULL;
v___x_1894_ = lean_uint64_shift_right(v_fold_1892_, v___x_1893_);
v___x_1895_ = lean_uint64_xor(v_fold_1892_, v___x_1894_);
v___x_1896_ = lean_uint64_to_usize(v___x_1895_);
v___x_1897_ = lean_usize_of_nat(v___x_1887_);
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_sub(v___x_1897_, v___x_1898_);
v___x_1900_ = lean_usize_land(v___x_1896_, v___x_1899_);
v___x_1901_ = lean_array_uget_borrowed(v_buckets_1886_, v___x_1900_);
v___x_1902_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1885_, v___x_1901_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object* v_m_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_m_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object* v___x_1908_, lean_object* v_declName_1909_, lean_object* v_as_1910_, size_t v_sz_1911_, size_t v_i_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_usize_dec_lt(v_i_1912_, v_sz_1911_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v_declName_1909_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_b_1913_);
lean_ctor_set(v___x_1921_, 1, v___y_1914_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
else
{
lean_object* v___x_1923_; lean_object* v_modules_1924_; lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v_toImport_1928_; lean_object* v_module_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1923_ = l_Lean_Environment_header(v___x_1908_);
v_modules_1924_ = lean_ctor_get(v___x_1923_, 3);
lean_inc_ref(v_modules_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1926_ = lean_array_uget_borrowed(v_as_1910_, v_i_1912_);
v___x_1927_ = lean_array_get(v___x_1925_, v_modules_1924_, v_a_1926_);
lean_dec_ref(v_modules_1924_);
v_toImport_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_ref(v_toImport_1928_);
lean_dec(v___x_1927_);
v_module_1929_ = lean_ctor_get(v_toImport_1928_, 0);
lean_inc(v_module_1929_);
lean_dec_ref(v_toImport_1928_);
v___x_1930_ = lean_box(0);
v___x_1931_ = 0;
lean_inc(v_declName_1909_);
v___x_1932_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1929_, v___x_1931_, v_declName_1909_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_snd_1934_; size_t v___x_1935_; size_t v___x_1936_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_snd_1934_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1934_);
lean_dec(v_a_1933_);
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = lean_usize_add(v_i_1912_, v___x_1935_);
v_i_1912_ = v___x_1936_;
v_b_1913_ = v___x_1930_;
v___y_1914_ = v_snd_1934_;
goto _start;
}
else
{
lean_dec(v_declName_1909_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object* v___x_1938_, lean_object* v_declName_1939_, lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
size_t v_sz_boxed_1950_; size_t v_i_boxed_1951_; lean_object* v_res_1952_; 
v_sz_boxed_1950_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1951_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_1938_, v_declName_1939_, v_as_1940_, v_sz_boxed_1950_, v_i_boxed_1951_, v_b_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v_as_1940_);
lean_dec_ref(v___x_1938_);
return v_res_1952_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_declName_1956_, uint8_t v_isMeta_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_env_1970_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___x_1995_; 
v___x_1964_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0);
v___x_1965_ = lean_st_ref_get(v___y_1962_);
v_env_1970_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_ref(v_env_1970_);
lean_dec(v___x_1965_);
v___x_1995_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1970_, v_declName_1956_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref(v_env_1970_);
lean_dec(v_declName_1956_);
goto v___jp_1966_;
}
else
{
lean_object* v_val_1996_; lean_object* v___x_1997_; lean_object* v_modules_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_val_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = l_Lean_Environment_header(v_env_1970_);
v_modules_1998_ = lean_ctor_get(v___x_1997_, 3);
lean_inc_ref(v_modules_1998_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = lean_array_get_size(v_modules_1998_);
v___x_2000_ = lean_nat_dec_lt(v_val_1996_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v_modules_1998_);
lean_dec(v_val_1996_);
lean_dec_ref(v_env_1970_);
lean_dec(v_declName_1956_);
goto v___jp_1966_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___y_2004_; 
v___x_2001_ = lean_array_fget(v_modules_1998_, v_val_1996_);
lean_dec(v_val_1996_);
lean_dec_ref(v_modules_1998_);
v___x_2002_ = lean_st_ref_get(v___y_1962_);
if (v_isMeta_1957_ == 0)
{
lean_dec(v___x_2002_);
v___y_2004_ = v_isMeta_1957_;
goto v___jp_2003_;
}
else
{
lean_object* v_env_2017_; uint8_t v___x_2018_; 
v_env_2017_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_ref(v_env_2017_);
lean_dec(v___x_2002_);
lean_inc(v_declName_1956_);
v___x_2018_ = l_Lean_isMarkedMeta(v_env_2017_, v_declName_1956_);
if (v___x_2018_ == 0)
{
v___y_2004_ = v_isMeta_1957_;
goto v___jp_2003_;
}
else
{
uint8_t v___x_2019_; 
v___x_2019_ = 0;
v___y_2004_ = v___x_2019_;
goto v___jp_2003_;
}
}
v___jp_2003_:
{
lean_object* v_toImport_2005_; lean_object* v_module_2006_; lean_object* v___x_2007_; 
v_toImport_2005_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_ref(v_toImport_2005_);
lean_dec(v___x_2001_);
v_module_2006_ = lean_ctor_get(v_toImport_2005_, 0);
lean_inc(v_module_2006_);
lean_dec_ref(v_toImport_2005_);
lean_inc(v_declName_1956_);
v___x_2007_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_2006_, v___y_2004_, v_declName_1956_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v_snd_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v_snd_2009_ = lean_ctor_get(v_a_2008_, 1);
lean_inc(v_snd_2009_);
lean_dec(v_a_2008_);
v___x_2010_ = l_Lean_indirectModUseExt;
v___x_2011_ = lean_box(1);
v___x_2012_ = lean_box(0);
lean_inc_ref(v_env_1970_);
v___x_2013_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1964_, v___x_2010_, v_env_1970_, v___x_2011_, v___x_2012_);
v___x_2014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_2013_, v_declName_1956_);
lean_dec(v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___y_1972_ = v_snd_2009_;
v___y_1973_ = v___x_2015_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_2016_; 
v_val_2016_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_1972_ = v_snd_2009_;
v___y_1973_ = v_val_2016_;
goto v___jp_1971_;
}
}
else
{
lean_dec_ref(v_env_1970_);
lean_dec(v_declName_1956_);
return v___x_2007_;
}
}
}
}
v___jp_1966_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___y_1958_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
v___jp_1971_:
{
lean_object* v___x_1974_; size_t v_sz_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = lean_box(0);
v_sz_1975_ = lean_array_size(v___y_1973_);
v___x_1976_ = ((size_t)0ULL);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_1970_, v_declName_1956_, v___y_1973_, v_sz_1975_, v___x_1976_, v___x_1974_, v___y_1972_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_env_1970_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1994_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1994_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1994_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1992_; 
v_snd_1982_ = lean_ctor_get(v_a_1978_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_a_1978_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_a_1978_, 0);
lean_dec(v_unused_1993_);
v___x_1984_ = v_a_1978_;
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_dec(v_a_1978_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1974_);
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_snd_1982_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1987_);
v___x_1989_ = v___x_1980_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
else
{
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_declName_2020_, lean_object* v_isMeta_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v_isMeta_boxed_2028_; lean_object* v_res_2029_; 
v_isMeta_boxed_2028_ = lean_unbox(v_isMeta_2021_);
v_res_2029_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_2020_, v_isMeta_boxed_2028_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2030_, lean_object* v_vals_2031_, lean_object* v_i_2032_, lean_object* v_k_2033_){
_start:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = lean_array_get_size(v_keys_2030_);
v___x_2035_ = lean_nat_dec_lt(v_i_2032_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec(v_i_2032_);
v___x_2036_ = lean_box(0);
return v___x_2036_;
}
else
{
lean_object* v_k_x27_2037_; uint8_t v___x_2038_; 
v_k_x27_2037_ = lean_array_fget_borrowed(v_keys_2030_, v_i_2032_);
v___x_2038_ = lean_name_eq(v_k_2033_, v_k_x27_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_unsigned_to_nat(1u);
v___x_2040_ = lean_nat_add(v_i_2032_, v___x_2039_);
lean_dec(v_i_2032_);
v_i_2032_ = v___x_2040_;
goto _start;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_array_fget_borrowed(v_vals_2031_, v_i_2032_);
lean_dec(v_i_2032_);
lean_inc(v___x_2042_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2044_, lean_object* v_vals_2045_, lean_object* v_i_2046_, lean_object* v_k_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2044_, v_vals_2045_, v_i_2046_, v_k_2047_);
lean_dec(v_k_2047_);
lean_dec_ref(v_vals_2045_);
lean_dec_ref(v_keys_2044_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_2049_, size_t v_x_2050_, lean_object* v_x_2051_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v_es_2052_; lean_object* v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; lean_object* v_j_2056_; lean_object* v___x_2057_; 
v_es_2052_ = lean_ctor_get(v_x_2049_, 0);
v___x_2053_ = lean_box(2);
v___x_2054_ = ((size_t)31ULL);
v___x_2055_ = lean_usize_land(v_x_2050_, v___x_2054_);
v_j_2056_ = lean_usize_to_nat(v___x_2055_);
v___x_2057_ = lean_array_get_borrowed(v___x_2053_, v_es_2052_, v_j_2056_);
lean_dec(v_j_2056_);
switch(lean_obj_tag(v___x_2057_))
{
case 0:
{
lean_object* v_key_2058_; lean_object* v_val_2059_; uint8_t v___x_2060_; 
v_key_2058_ = lean_ctor_get(v___x_2057_, 0);
v_val_2059_ = lean_ctor_get(v___x_2057_, 1);
v___x_2060_ = lean_name_eq(v_x_2051_, v_key_2058_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_box(0);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; 
lean_inc(v_val_2059_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_val_2059_);
return v___x_2062_;
}
}
case 1:
{
lean_object* v_node_2063_; size_t v___x_2064_; size_t v___x_2065_; 
v_node_2063_ = lean_ctor_get(v___x_2057_, 0);
v___x_2064_ = ((size_t)5ULL);
v___x_2065_ = lean_usize_shift_right(v_x_2050_, v___x_2064_);
v_x_2049_ = v_node_2063_;
v_x_2050_ = v___x_2065_;
goto _start;
}
default: 
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_box(0);
return v___x_2067_;
}
}
}
else
{
lean_object* v_ks_2068_; lean_object* v_vs_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_ks_2068_ = lean_ctor_get(v_x_2049_, 0);
v_vs_2069_ = lean_ctor_get(v_x_2049_, 1);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_2068_, v_vs_2069_, v___x_2070_, v_x_2051_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
size_t v_x_27481__boxed_2075_; lean_object* v_res_2076_; 
v_x_27481__boxed_2075_ = lean_unbox_usize(v_x_2073_);
lean_dec(v_x_2073_);
v_res_2076_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2072_, v_x_27481__boxed_2075_, v_x_2074_);
lean_dec(v_x_2074_);
lean_dec_ref(v_x_2072_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
uint64_t v___y_2080_; 
if (lean_obj_tag(v_x_2078_) == 0)
{
uint64_t v___x_2083_; 
v___x_2083_ = 1723ULL;
v___y_2080_ = v___x_2083_;
goto v___jp_2079_;
}
else
{
uint64_t v_hash_2084_; 
v_hash_2084_ = lean_ctor_get_uint64(v_x_2078_, sizeof(void*)*2);
v___y_2080_ = v_hash_2084_;
goto v___jp_2079_;
}
v___jp_2079_:
{
size_t v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_uint64_to_usize(v___y_2080_);
v___x_2082_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2077_, v___x_2081_, v_x_2078_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2085_, v_x_2086_);
lean_dec(v_x_2086_);
lean_dec_ref(v_x_2085_);
return v_res_2087_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2088_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
return v___x_2091_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2097_ = l_Lean_stringToMessageData(v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2100_ = l_Lean_stringToMessageData(v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2101_, lean_object* v_init_2102_, lean_object* v_x_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_object* v_k_2110_; lean_object* v_l_2111_; lean_object* v_r_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_k_2110_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_k_2110_);
v_l_2111_ = lean_ctor_get(v_x_2103_, 3);
lean_inc(v_l_2111_);
v_r_2112_ = lean_ctor_get(v_x_2103_, 4);
lean_inc(v_r_2112_);
lean_dec_ref_known(v_x_2103_, 5);
v___x_2113_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_box(0);
lean_inc_ref(v_origDecl_2101_);
v___x_2116_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2101_, v_init_2102_, v_l_2111_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2238_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_snd_2118_ = lean_ctor_get(v_a_2117_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v_a_2117_, 0);
lean_dec(v_unused_2239_);
v___x_2120_ = v_a_2117_;
v_isShared_2121_ = v_isSharedCheck_2238_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_dec(v_a_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2238_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
uint8_t v___x_2122_; 
v___x_2122_ = l_Lean_NameSet_contains(v_snd_2118_, v_k_2110_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_env_2126_; lean_object* v___x_2127_; lean_object* v_toEnvExtension_2128_; lean_object* v_asyncMode_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2123_ = 1;
lean_inc(v_k_2110_);
v___x_2124_ = l_Lean_NameSet_insert(v_snd_2118_, v_k_2110_);
v___x_2125_ = lean_st_ref_get(v___y_2108_);
v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_ref(v_env_2126_);
lean_dec(v___x_2125_);
v___x_2127_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2128_ = lean_ctor_get(v___x_2127_, 0);
v_asyncMode_2129_ = lean_ctor_get(v_toEnvExtension_2128_, 2);
v___x_2130_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2113_, v___x_2127_, v_env_2126_, v_asyncMode_2129_, v___x_2115_, v___x_2122_);
v___x_2131_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2130_, v_k_2110_);
lean_dec(v___x_2130_);
if (lean_obj_tag(v___x_2131_) == 1)
{
lean_object* v_val_2132_; lean_object* v___x_2133_; 
lean_del_object(v___x_2120_);
lean_dec(v_k_2110_);
v_val_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc_n(v_val_2132_, 2);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2132_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; uint8_t v___y_2136_; lean_object* v_toSignature_2150_; lean_object* v_name_2151_; uint8_t v___x_2152_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v_toSignature_2150_ = lean_ctor_get(v_val_2132_, 0);
v_name_2151_ = lean_ctor_get(v_toSignature_2150_, 0);
v___x_2152_ = l_Lean_isPrivateName(v_name_2151_);
if (v___x_2152_ == 0)
{
lean_dec(v_a_2134_);
v___y_2136_ = v___x_2122_;
goto v___jp_2135_;
}
else
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_unbox(v_a_2134_);
lean_dec(v_a_2134_);
v___y_2136_ = v___x_2153_;
goto v___jp_2135_;
}
v___jp_2135_:
{
if (v___y_2136_ == 0)
{
lean_dec(v_val_2132_);
v_init_2102_ = v___x_2114_;
v_x_2103_ = v_r_2112_;
v___y_2104_ = v___x_2124_;
goto _start;
}
else
{
lean_object* v___x_2138_; 
lean_inc_ref(v_origDecl_2101_);
v___x_2138_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2101_, v_val_2132_, v___x_2124_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_snd_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v_snd_2140_ = lean_ctor_get(v_a_2139_, 1);
lean_inc(v_snd_2140_);
lean_dec(v_a_2139_);
v_init_2102_ = v___x_2114_;
v_x_2103_ = v_r_2112_;
v___y_2104_ = v_snd_2140_;
goto _start;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_r_2112_);
lean_dec_ref(v_origDecl_2101_);
v_a_2142_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2138_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2138_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_val_2132_);
lean_dec(v___x_2124_);
lean_dec(v_r_2112_);
lean_dec_ref(v_origDecl_2101_);
v_a_2154_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2133_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2133_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v_env_2163_; lean_object* v___x_2164_; 
lean_dec(v___x_2131_);
v___x_2162_ = lean_st_ref_get(v___y_2108_);
v_env_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_env_2163_);
lean_dec(v___x_2162_);
v___x_2164_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2163_, v_k_2110_);
lean_dec_ref(v_env_2163_);
if (lean_obj_tag(v___x_2164_) == 1)
{
lean_object* v_val_2165_; lean_object* v___x_2198_; uint8_t v___y_2208_; lean_object* v_env_2228_; lean_object* v___x_2229_; lean_object* v_modules_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_val_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2198_ = lean_st_ref_get(v___y_2108_);
v_env_2228_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_ref(v_env_2228_);
lean_dec(v___x_2198_);
v___x_2229_ = l_Lean_Environment_header(v_env_2228_);
lean_dec_ref(v_env_2228_);
v_modules_2230_ = lean_ctor_get(v___x_2229_, 3);
lean_inc_ref(v_modules_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = lean_array_get_size(v_modules_2230_);
v___x_2232_ = lean_nat_dec_lt(v_val_2165_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_dec_ref(v_modules_2230_);
v___y_2208_ = v___x_2122_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2233_; lean_object* v_toImport_2234_; uint8_t v_isExported_2235_; 
v___x_2233_ = lean_array_fget(v_modules_2230_, v_val_2165_);
lean_dec_ref(v_modules_2230_);
v_toImport_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_toImport_2234_);
lean_dec(v___x_2233_);
v_isExported_2235_ = lean_ctor_get_uint8(v_toImport_2234_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2234_);
if (v_isExported_2235_ == 0)
{
goto v___jp_2199_;
}
else
{
v___y_2208_ = v___x_2122_;
goto v___jp_2207_;
}
}
v___jp_2166_:
{
lean_object* v___x_2167_; lean_object* v_toSignature_2168_; lean_object* v_env_2169_; lean_object* v_name_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2167_ = lean_st_ref_get(v___y_2108_);
v_toSignature_2168_ = lean_ctor_get(v_origDecl_2101_, 0);
lean_inc_ref(v_toSignature_2168_);
lean_dec_ref(v_origDecl_2101_);
v_env_2169_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_env_2169_);
lean_dec(v___x_2167_);
v_name_2170_ = lean_ctor_get(v_toSignature_2168_, 0);
lean_inc(v_name_2170_);
lean_dec_ref(v_toSignature_2168_);
v___x_2171_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
v___x_2172_ = l_Lean_MessageData_ofConstName(v_name_2170_, v___x_2122_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 7);
lean_ctor_set(v___x_2120_, 1, v___x_2172_);
lean_ctor_set(v___x_2120_, 0, v___x_2171_);
v___x_2174_ = v___x_2120_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
v___x_2175_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_MessageData_ofConstName(v_k_2110_, v___x_2122_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = l_Lean_Environment_header(v_env_2169_);
lean_dec_ref(v_env_2169_);
v___x_2182_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2181_);
v___x_2183_ = lean_array_get(v___x_2115_, v___x_2182_, v_val_2165_);
lean_dec(v_val_2165_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = l_Lean_MessageData_ofName(v___x_2183_);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2180_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2187_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v_fst_2203_; uint8_t v___x_2204_; 
v___x_2200_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2201_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v___x_2200_, v___x_2124_, v___y_2107_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v_fst_2203_ = lean_ctor_get(v_a_2202_, 0);
v___x_2204_ = lean_unbox(v_fst_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v_a_2202_);
lean_dec(v_r_2112_);
goto v___jp_2166_;
}
else
{
if (v___x_2122_ == 0)
{
lean_object* v_snd_2205_; 
lean_dec(v_val_2165_);
lean_del_object(v___x_2120_);
lean_dec(v_k_2110_);
v_snd_2205_ = lean_ctor_get(v_a_2202_, 1);
lean_inc(v_snd_2205_);
lean_dec(v_a_2202_);
v_init_2102_ = v___x_2114_;
v_x_2103_ = v_r_2112_;
v___y_2104_ = v_snd_2205_;
goto _start;
}
else
{
lean_dec(v_a_2202_);
lean_dec(v_r_2112_);
goto v___jp_2166_;
}
}
}
v___jp_2207_:
{
if (v___y_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v_env_2210_; uint8_t v___x_2211_; uint8_t v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_val_2165_);
lean_del_object(v___x_2120_);
v___x_2209_ = lean_st_ref_get(v___y_2108_);
v_env_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc_ref(v_env_2210_);
lean_dec(v___x_2209_);
lean_inc(v_k_2110_);
v___x_2211_ = l_Lean_getIRPhases(v_env_2210_, v_k_2110_);
v___x_2212_ = 1;
v___x_2213_ = l_Lean_instBEqIRPhases_beq(v___x_2211_, v___x_2212_);
v___x_2214_ = lean_box(v___x_2213_);
v___x_2215_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed), 8, 2);
lean_closure_set(v___x_2215_, 0, v_k_2110_);
lean_closure_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2215_, v___x_2123_, v___x_2124_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_snd_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v_snd_2218_ = lean_ctor_get(v_a_2217_, 1);
lean_inc(v_snd_2218_);
lean_dec(v_a_2217_);
v_init_2102_ = v___x_2114_;
v_x_2103_ = v_r_2112_;
v___y_2104_ = v_snd_2218_;
goto _start;
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_r_2112_);
lean_dec_ref(v_origDecl_2101_);
v_a_2220_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2216_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2216_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
goto v___jp_2199_;
}
}
}
else
{
lean_dec(v___x_2164_);
lean_del_object(v___x_2120_);
lean_dec(v_k_2110_);
v_init_2102_ = v___x_2114_;
v_x_2103_ = v_r_2112_;
v___y_2104_ = v___x_2124_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2120_);
lean_dec(v_k_2110_);
v_init_2102_ = v___x_2114_;
v_x_2103_ = v_r_2112_;
v___y_2104_ = v_snd_2118_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2112_);
lean_dec(v_k_2110_);
lean_dec_ref(v_origDecl_2101_);
return v___x_2116_;
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v_origDecl_2101_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_init_2102_);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___y_2104_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2243_, lean_object* v_origDecl_2244_, lean_object* v_code_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = l_Lean_NameSet_empty;
v___x_2253_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2243_, v_code_2245_, v___x_2252_);
v___x_2254_ = lean_box(0);
v___x_2255_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2244_, v___x_2254_, v___x_2253_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2272_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2272_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2272_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_snd_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2270_; 
v_snd_2260_ = lean_ctor_get(v_a_2256_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_a_2256_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v_a_2256_, 0);
lean_dec(v_unused_2271_);
v___x_2262_ = v_a_2256_;
v_isShared_2263_ = v_isSharedCheck_2270_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snd_2260_);
lean_dec(v_a_2256_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2270_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2254_);
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_snd_2260_);
v___x_2265_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2267_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2265_);
v___x_2267_ = v___x_2258_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2255_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2255_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2281_, lean_object* v_origDecl_2282_, lean_object* v_code_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
uint8_t v___x_27561__boxed_2290_; lean_object* v_res_2291_; 
v___x_27561__boxed_2290_ = lean_unbox(v___x_2281_);
v_res_2291_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_27561__boxed_2290_, v_origDecl_2282_, v_code_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2292_, lean_object* v_decl_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_value_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___f_2303_; lean_object* v___x_2304_; 
v_value_2300_ = lean_ctor_get(v_decl_2293_, 1);
lean_inc_ref(v_value_2300_);
lean_dec_ref(v_decl_2293_);
v___x_2301_ = 0;
v___x_2302_ = lean_box(v___x_2301_);
v___f_2303_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2303_, 0, v___x_2302_);
lean_closure_set(v___f_2303_, 1, v_origDecl_2292_);
v___x_2304_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2303_, v_value_2300_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2305_, lean_object* v_decl_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2305_, v_decl_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2314_, lean_object* v_init_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2314_, v_init_2315_, v_x_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2325_, v_x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2328_, v_x_2329_, v_x_2330_);
lean_dec(v_x_2330_);
lean_dec_ref(v_x_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_opt_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_2332_, v___y_2333_, v___y_2336_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_opt_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v_opt_2340_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2348_, lean_object* v_x_2349_, size_t v_x_2350_, lean_object* v_x_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2349_, v_x_2350_, v_x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
size_t v_x_27974__boxed_2357_; lean_object* v_res_2358_; 
v_x_27974__boxed_2357_ = lean_unbox_usize(v_x_2355_);
lean_dec(v_x_2355_);
v_res_2358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2353_, v_x_2354_, v_x_27974__boxed_2357_, v_x_2356_);
lean_dec(v_x_2356_);
lean_dec_ref(v_x_2354_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(lean_object* v_00_u03b2_2359_, lean_object* v_m_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_2360_, v_a_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2363_, lean_object* v_m_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_2363_, v_m_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_m_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2367_, lean_object* v_keys_2368_, lean_object* v_vals_2369_, lean_object* v_heq_2370_, lean_object* v_i_2371_, lean_object* v_k_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2368_, v_vals_2369_, v_i_2371_, v_k_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2374_, lean_object* v_keys_2375_, lean_object* v_vals_2376_, lean_object* v_heq_2377_, lean_object* v_i_2378_, lean_object* v_k_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2374_, v_keys_2375_, v_vals_2376_, v_heq_2377_, v_i_2378_, v_k_2379_);
lean_dec(v_k_2379_);
lean_dec_ref(v_vals_2376_);
lean_dec_ref(v_keys_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
uint8_t v___x_2384_; 
v___x_2384_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_2382_, v_x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
uint8_t v_res_2388_; lean_object* v_r_2389_; 
v_res_2388_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_2385_, v_x_2386_, v_x_2387_);
lean_dec_ref(v_x_2387_);
lean_dec_ref(v_x_2386_);
v_r_2389_ = lean_box(v_res_2388_);
return v_r_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_2390_, lean_object* v_a_2391_, lean_object* v_x_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_2391_, v_x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2394_, lean_object* v_a_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_2394_, v_a_2395_, v_x_2396_);
lean_dec(v_x_2396_);
lean_dec(v_a_2395_);
return v_res_2397_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2398_, lean_object* v_x_2399_, size_t v_x_2400_, lean_object* v_x_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_2399_, v_x_2400_, v_x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
size_t v_x_28002__boxed_2407_; uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_x_28002__boxed_2407_ = lean_unbox_usize(v_x_2405_);
lean_dec(v_x_2405_);
v_res_2408_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_2403_, v_x_2404_, v_x_28002__boxed_2407_, v_x_2406_);
lean_dec_ref(v_x_2406_);
lean_dec_ref(v_x_2404_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_2410_, lean_object* v_keys_2411_, lean_object* v_vals_2412_, lean_object* v_heq_2413_, lean_object* v_i_2414_, lean_object* v_k_2415_){
_start:
{
uint8_t v___x_2416_; 
v___x_2416_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_2411_, v_i_2414_, v_k_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2417_, lean_object* v_keys_2418_, lean_object* v_vals_2419_, lean_object* v_heq_2420_, lean_object* v_i_2421_, lean_object* v_k_2422_){
_start:
{
uint8_t v_res_2423_; lean_object* v_r_2424_; 
v_res_2423_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_2417_, v_keys_2418_, v_vals_2419_, v_heq_2420_, v_i_2421_, v_k_2422_);
lean_dec_ref(v_k_2422_);
lean_dec_ref(v_vals_2419_);
lean_dec_ref(v_keys_2418_);
v_r_2424_ = lean_box(v_res_2423_);
return v_r_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2425_, size_t v_sz_2426_, size_t v_i_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_a_2435_; uint8_t v___x_2439_; 
v___x_2439_ = lean_usize_dec_lt(v_i_2427_, v_sz_2426_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_b_2428_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; lean_object* v_a_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_box(0);
v_a_2442_ = lean_array_uget_borrowed(v_as_2425_, v_i_2427_);
lean_inc(v_a_2442_);
v___x_2443_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2442_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_toSignature_2444_; lean_object* v_a_2445_; lean_object* v_name_2446_; uint8_t v___x_2447_; 
v_toSignature_2444_ = lean_ctor_get(v_a_2442_, 0);
v_a_2445_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2443_, 1);
v_name_2446_ = lean_ctor_get(v_toSignature_2444_, 0);
v___x_2447_ = l_Lean_isPrivateName(v_name_2446_);
if (v___x_2447_ == 0)
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_unbox(v_a_2445_);
lean_dec(v_a_2445_);
if (v___x_2448_ == 0)
{
v_a_2435_ = v___x_2441_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_st_ref_get(v___y_2432_);
lean_dec(v___x_2449_);
v___x_2450_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2442_, 2);
v___x_2451_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2442_, v_a_2442_, v___x_2450_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec_ref_known(v___x_2451_, 1);
v_a_2435_ = v___x_2441_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
else
{
lean_dec(v_a_2445_);
v_a_2435_ = v___x_2441_;
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v_a_2460_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2443_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2443_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
v___jp_2434_:
{
size_t v___x_2436_; size_t v___x_2437_; 
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_add(v_i_2427_, v___x_2436_);
v_i_2427_ = v___x_2437_;
v_b_2428_ = v_a_2435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2468_, lean_object* v_sz_2469_, lean_object* v_i_2470_, lean_object* v_b_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
size_t v_sz_boxed_2477_; size_t v_i_boxed_2478_; lean_object* v_res_2479_; 
v_sz_boxed_2477_ = lean_unbox_usize(v_sz_2469_);
lean_dec(v_sz_2469_);
v_i_boxed_2478_ = lean_unbox_usize(v_i_2470_);
lean_dec(v_i_2470_);
v_res_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2468_, v_sz_boxed_2477_, v_i_boxed_2478_, v_b_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v_as_2468_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; lean_object* v_env_2487_; lean_object* v___x_2488_; uint8_t v_isModule_2489_; 
v___x_2486_ = lean_st_ref_get(v___y_2484_);
v_env_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc_ref(v_env_2487_);
lean_dec(v___x_2486_);
v___x_2488_ = l_Lean_Environment_header(v_env_2487_);
lean_dec_ref(v_env_2487_);
v_isModule_2489_ = lean_ctor_get_uint8(v___x_2488_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2488_);
if (v_isModule_2489_ == 0)
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_decls_2480_);
return v___x_2490_;
}
else
{
lean_object* v___x_2491_; size_t v_sz_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2491_ = lean_box(0);
v_sz_2492_ = lean_array_size(v_decls_2480_);
v___x_2493_ = ((size_t)0ULL);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2480_, v_sz_2492_, v___x_2493_, v___x_2491_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2494_, 0);
lean_dec(v_unused_2502_);
v___x_2496_ = v___x_2494_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_dec(v___x_2494_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v_decls_2480_);
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_decls_2480_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v_decls_2480_);
v_a_2503_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2494_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2494_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2517_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2532_, uint8_t v___x_2533_, lean_object* v_as_2534_, size_t v_sz_2535_, size_t v_i_2536_, lean_object* v_b_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_a_2544_; uint8_t v___x_2548_; 
v___x_2548_ = lean_usize_dec_lt(v_i_2536_, v_sz_2535_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_b_2537_);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; lean_object* v_a_2551_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___x_2559_; lean_object* v_toSignature_2560_; lean_object* v_env_2561_; lean_object* v_name_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2550_ = lean_box(0);
v_a_2551_ = lean_array_uget_borrowed(v_as_2534_, v_i_2536_);
v___x_2559_ = lean_st_ref_get(v___y_2541_);
v_toSignature_2560_ = lean_ctor_get(v_a_2551_, 0);
v_env_2561_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_ref(v_env_2561_);
lean_dec(v___x_2559_);
v_name_2562_ = lean_ctor_get(v_toSignature_2560_, 0);
v___x_2563_ = l_Lean_Environment_setExporting(v_env_2561_, v___x_2533_);
lean_inc(v_name_2562_);
v___x_2564_ = l_Lean_Environment_contains(v___x_2563_, v_name_2562_, v___x_2533_);
if (v___x_2564_ == 0)
{
v_a_2544_ = v___x_2550_;
goto v___jp_2543_;
}
else
{
lean_object* v_toCold_2565_; lean_object* v_options_2566_; uint8_t v_hasTrace_2567_; 
v_toCold_2565_ = lean_ctor_get(v___y_2540_, 0);
v_options_2566_ = lean_ctor_get(v_toCold_2565_, 2);
v_hasTrace_2567_ = lean_ctor_get_uint8(v_options_2566_, sizeof(void*)*1);
if (v_hasTrace_2567_ == 0)
{
v___y_2553_ = v___y_2538_;
v___y_2554_ = v___y_2539_;
v___y_2555_ = v___y_2540_;
v___y_2556_ = v___y_2541_;
goto v___jp_2552_;
}
else
{
lean_object* v_inheritedTraceOptions_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_inheritedTraceOptions_2568_ = lean_ctor_get(v_toCold_2565_, 11);
v___x_2569_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2570_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2568_, v_options_2566_, v___x_2570_);
if (v___x_2571_ == 0)
{
v___y_2553_ = v___y_2538_;
v___y_2554_ = v___y_2539_;
v___y_2555_ = v___y_2540_;
v___y_2556_ = v___y_2541_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2572_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2562_);
v___x_2573_ = l_Lean_MessageData_ofName(v_name_2562_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2569_, v___x_2576_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_dec_ref_known(v___x_2577_, 1);
v___y_2553_ = v___y_2538_;
v___y_2554_ = v___y_2539_;
v___y_2555_ = v___y_2540_;
v___y_2556_ = v___y_2541_;
goto v___jp_2552_;
}
else
{
return v___x_2577_;
}
}
}
}
v___jp_2552_:
{
uint8_t v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2532_);
lean_inc(v_a_2551_);
v___x_2558_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2557_, v_phase_2532_, v_a_2551_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
v_a_2544_ = v___x_2550_;
goto v___jp_2543_;
}
else
{
return v___x_2558_;
}
}
}
v___jp_2543_:
{
size_t v___x_2545_; size_t v___x_2546_; 
v___x_2545_ = ((size_t)1ULL);
v___x_2546_ = lean_usize_add(v_i_2536_, v___x_2545_);
v_i_2536_ = v___x_2546_;
v_b_2537_ = v_a_2544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2578_, lean_object* v___x_2579_, lean_object* v_as_2580_, lean_object* v_sz_2581_, lean_object* v_i_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
uint8_t v_phase_boxed_2589_; uint8_t v___x_2258__boxed_2590_; size_t v_sz_boxed_2591_; size_t v_i_boxed_2592_; lean_object* v_res_2593_; 
v_phase_boxed_2589_ = lean_unbox(v_phase_2578_);
v___x_2258__boxed_2590_ = lean_unbox(v___x_2579_);
v_sz_boxed_2591_ = lean_unbox_usize(v_sz_2581_);
lean_dec(v_sz_2581_);
v_i_boxed_2592_ = lean_unbox_usize(v_i_2582_);
lean_dec(v_i_2582_);
v_res_2593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2589_, v___x_2258__boxed_2590_, v_as_2580_, v_sz_boxed_2591_, v_i_boxed_2592_, v_b_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_as_2580_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2594_, lean_object* v_decls_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; lean_object* v_env_2602_; lean_object* v___x_2603_; uint8_t v_isModule_2604_; 
v___x_2601_ = lean_st_ref_get(v___y_2599_);
v_env_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc_ref(v_env_2602_);
lean_dec(v___x_2601_);
v___x_2603_ = l_Lean_Environment_header(v_env_2602_);
lean_dec_ref(v_env_2602_);
v_isModule_2604_ = lean_ctor_get_uint8(v___x_2603_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2603_);
if (v_isModule_2604_ == 0)
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_decls_2595_);
return v___x_2605_;
}
else
{
lean_object* v___x_2606_; size_t v_sz_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2606_ = lean_box(0);
v_sz_2607_ = lean_array_size(v_decls_2595_);
v___x_2608_ = ((size_t)0ULL);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2594_, v_isModule_2604_, v_decls_2595_, v_sz_2607_, v___x_2608_, v___x_2606_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v___x_2609_, 0);
lean_dec(v_unused_2617_);
v___x_2611_ = v___x_2609_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_dec(v___x_2609_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_decls_2595_);
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_decls_2595_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v_decls_2595_);
v_a_2618_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2609_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2609_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2626_, lean_object* v_decls_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v_phase_boxed_2633_; lean_object* v_res_2634_; 
v_phase_boxed_2633_ = lean_unbox(v_phase_2626_);
v_res_2634_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2633_, v_decls_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2638_ = lean_box(v_phase_2637_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2639_, 0, v___x_2638_);
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = 0;
v___x_2642_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2643_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2643_, 0, v___x_2640_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
lean_ctor_set(v___x_2643_, 2, v___f_2639_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*3, v_phase_2637_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*3 + 1, v_phase_2637_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*3 + 2, v___x_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2644_){
_start:
{
uint8_t v_phase_boxed_2645_; lean_object* v_res_2646_; 
v_phase_boxed_2645_ = lean_unbox(v_phase_2644_);
v_res_2646_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2645_);
return v_res_2646_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_unsigned_to_nat(3356661454u);
v___x_2699_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2700_ = l_Lean_Name_num___override(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2703_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2704_ = l_Lean_Name_str___override(v___x_2703_, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2707_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2708_ = l_Lean_Name_str___override(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_unsigned_to_nat(2u);
v___x_2710_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2711_ = l_Lean_Name_num___override(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2713_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2714_ = 0;
v___x_2715_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2716_ = l_Lean_registerTraceClass(v___x_2713_, v___x_2714_, v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2718_;
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
