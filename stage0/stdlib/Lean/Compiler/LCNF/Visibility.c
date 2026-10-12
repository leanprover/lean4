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
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(uint8_t v_pu_9_, lean_object* v_e_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_e_10_, v_s_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_9_ = stack[0].m_num;
lean_object* v_e_10_ = stack[1].m_obj;
lean_object* v_s_11_ = stack[2].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(v_pu_9_, v_e_10_, v_s_11_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___boxed(lean_object* v_pu_14_, lean_object* v_e_15_, lean_object* v_s_16_){
_start:
{
uint8_t v_pu_boxed_17_; lean_object* v_res_18_; 
v_pu_boxed_17_ = lean_unbox(v_pu_14_);
v_res_18_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(v_pu_boxed_17_, v_e_15_, v_s_16_);
return v_res_18_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(uint8_t v_pu_19_, lean_object* v_code_20_, lean_object* v_s_21_){
_start:
{
switch(lean_obj_tag(v_code_20_))
{
case 0:
{
lean_object* v_decl_22_; lean_object* v_k_23_; lean_object* v_value_24_; lean_object* v___x_25_; 
v_decl_22_ = lean_ctor_get(v_code_20_, 0);
lean_inc_ref(v_decl_22_);
v_k_23_ = lean_ctor_get(v_code_20_, 1);
lean_inc_ref(v_k_23_);
lean_dec_ref_known(v_code_20_, 2);
v_value_24_ = lean_ctor_get(v_decl_22_, 3);
lean_inc(v_value_24_);
lean_dec_ref(v_decl_22_);
v___x_25_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_value_24_, v_s_21_);
v_code_20_ = v_k_23_;
v_s_21_ = v___x_25_;
goto _start;
}
case 2:
{
lean_object* v_decl_27_; lean_object* v_k_28_; lean_object* v_value_29_; lean_object* v___x_30_; 
v_decl_27_ = lean_ctor_get(v_code_20_, 0);
lean_inc_ref(v_decl_27_);
v_k_28_ = lean_ctor_get(v_code_20_, 1);
lean_inc_ref(v_k_28_);
lean_dec_ref_known(v_code_20_, 2);
v_value_29_ = lean_ctor_get(v_decl_27_, 4);
lean_inc_ref(v_value_29_);
lean_dec_ref(v_decl_27_);
v___x_30_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_19_, v_k_28_, v_s_21_);
v_code_20_ = v_value_29_;
v_s_21_ = v___x_30_;
goto _start;
}
case 1:
{
lean_object* v_decl_32_; lean_object* v_k_33_; lean_object* v_value_34_; lean_object* v___x_35_; 
v_decl_32_ = lean_ctor_get(v_code_20_, 0);
lean_inc_ref(v_decl_32_);
v_k_33_ = lean_ctor_get(v_code_20_, 1);
lean_inc_ref(v_k_33_);
lean_dec_ref_known(v_code_20_, 2);
v_value_34_ = lean_ctor_get(v_decl_32_, 4);
lean_inc_ref(v_value_34_);
lean_dec_ref(v_decl_32_);
v___x_35_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_19_, v_k_33_, v_s_21_);
v_code_20_ = v_value_34_;
v_s_21_ = v___x_35_;
goto _start;
}
case 4:
{
lean_object* v_cases_37_; lean_object* v_alts_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_cases_37_ = lean_ctor_get(v_code_20_, 0);
lean_inc_ref(v_cases_37_);
lean_dec_ref_known(v_code_20_, 1);
v_alts_38_ = lean_ctor_get(v_cases_37_, 3);
lean_inc_ref(v_alts_38_);
lean_dec_ref(v_cases_37_);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_array_get_size(v_alts_38_);
v___x_41_ = lean_nat_dec_lt(v___x_39_, v___x_40_);
if (v___x_41_ == 0)
{
lean_dec_ref(v_alts_38_);
return v_s_21_;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = lean_nat_dec_le(v___x_40_, v___x_40_);
if (v___x_42_ == 0)
{
if (v___x_41_ == 0)
{
lean_dec_ref(v_alts_38_);
return v_s_21_;
}
else
{
size_t v___x_43_; size_t v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((size_t)0ULL);
v___x_44_ = lean_usize_of_nat(v___x_40_);
v___x_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_19_, v_alts_38_, v___x_43_, v___x_44_, v_s_21_);
lean_dec_ref(v_alts_38_);
return v___x_45_;
}
}
else
{
size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((size_t)0ULL);
v___x_47_ = lean_usize_of_nat(v___x_40_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_19_, v_alts_38_, v___x_46_, v___x_47_, v_s_21_);
lean_dec_ref(v_alts_38_);
return v___x_48_;
}
}
}
default: 
{
lean_dec_ref(v_code_20_);
return v_s_21_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_19_ = stack[0].m_num;
lean_object* v_code_20_ = stack[1].m_obj;
lean_object* v_s_21_ = stack[2].m_obj;
lean_object* v_res_49_;
v_res_49_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_19_, v_code_20_, v_s_21_);
stack->m_obj
 = v_res_49_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(uint8_t v_pu_50_, lean_object* v_as_51_, size_t v_i_52_, size_t v_stop_53_, lean_object* v_b_54_){
_start:
{
lean_object* v___y_56_; uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_eq(v_i_52_, v_stop_53_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_array_uget_borrowed(v_as_51_, v_i_52_);
switch(lean_obj_tag(v___x_61_))
{
case 0:
{
lean_object* v_code_62_; lean_object* v___x_63_; 
v_code_62_ = lean_ctor_get(v___x_61_, 2);
lean_inc_ref(v_code_62_);
v___x_63_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_50_, v_code_62_, v_b_54_);
v___y_56_ = v___x_63_;
goto v___jp_55_;
}
case 1:
{
lean_object* v_code_64_; lean_object* v___x_65_; 
v_code_64_ = lean_ctor_get(v___x_61_, 1);
lean_inc_ref(v_code_64_);
v___x_65_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_50_, v_code_64_, v_b_54_);
v___y_56_ = v___x_65_;
goto v___jp_55_;
}
default: 
{
lean_object* v_code_66_; lean_object* v___x_67_; 
v_code_66_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_code_66_);
v___x_67_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_50_, v_code_66_, v_b_54_);
v___y_56_ = v___x_67_;
goto v___jp_55_;
}
}
}
else
{
return v_b_54_;
}
v___jp_55_:
{
size_t v___x_57_; size_t v___x_58_; 
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_add(v_i_52_, v___x_57_);
v_i_52_ = v___x_58_;
v_b_54_ = v___y_56_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_50_ = stack[0].m_num;
lean_object* v_as_51_ = stack[1].m_obj;
size_t v_i_52_ = stack[2].m_num;
size_t v_stop_53_ = stack[3].m_num;
lean_object* v_b_54_ = stack[4].m_obj;
lean_object* v_res_68_;
v_res_68_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_50_, v_as_51_, v_i_52_, v_stop_53_, v_b_54_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0___boxed(lean_object* v_pu_69_, lean_object* v_as_70_, lean_object* v_i_71_, lean_object* v_stop_72_, lean_object* v_b_73_){
_start:
{
uint8_t v_pu_boxed_74_; size_t v_i_boxed_75_; size_t v_stop_boxed_76_; lean_object* v_res_77_; 
v_pu_boxed_74_ = lean_unbox(v_pu_69_);
v_i_boxed_75_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_stop_boxed_76_ = lean_unbox_usize(v_stop_72_);
lean_dec(v_stop_72_);
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_boxed_74_, v_as_70_, v_i_boxed_75_, v_stop_boxed_76_, v_b_73_);
lean_dec_ref(v_as_70_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object* v_pu_78_, lean_object* v_code_79_, lean_object* v_s_80_){
_start:
{
uint8_t v_pu_boxed_81_; lean_object* v_res_82_; 
v_pu_boxed_81_ = lean_unbox(v_pu_78_);
v_res_82_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_boxed_81_, v_code_79_, v_s_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(lean_object* v_opts_83_, lean_object* v_opt_84_){
_start:
{
lean_object* v_name_85_; lean_object* v_defValue_86_; lean_object* v_map_87_; lean_object* v___x_88_; 
v_name_85_ = lean_ctor_get(v_opt_84_, 0);
v_defValue_86_ = lean_ctor_get(v_opt_84_, 1);
v_map_87_ = lean_ctor_get(v_opts_83_, 0);
v___x_88_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_87_, v_name_85_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_inc(v_defValue_86_);
return v_defValue_86_;
}
else
{
lean_object* v_val_89_; 
v_val_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v___x_88_, 1);
if (lean_obj_tag(v_val_89_) == 3)
{
lean_object* v_v_90_; 
v_v_90_ = lean_ctor_get(v_val_89_, 0);
lean_inc(v_v_90_);
lean_dec_ref_known(v_val_89_, 1);
return v_v_90_;
}
else
{
lean_dec(v_val_89_);
lean_inc(v_defValue_86_);
return v_defValue_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0___boxed(lean_object* v_opts_91_, lean_object* v_opt_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_opts_91_, v_opt_92_);
lean_dec_ref(v_opt_92_);
lean_dec_ref(v_opts_91_);
return v_res_93_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(lean_object* v_v_94_, lean_object* v_f_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
if (lean_obj_tag(v_v_94_) == 0)
{
lean_object* v_code_101_; lean_object* v___x_102_; 
v_code_101_ = lean_ctor_get(v_v_94_, 0);
lean_inc_ref(v_code_101_);
lean_dec_ref_known(v_v_94_, 1);
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
lean_inc(v___y_97_);
lean_inc_ref(v___y_96_);
v___x_102_ = lean_apply_6(v_f_95_, v_code_101_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, lean_box(0));
return v___x_102_;
}
else
{
lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_111_; 
lean_dec_ref(v_f_95_);
v_isSharedCheck_111_ = !lean_is_exclusive(v_v_94_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_v_94_, 0);
lean_dec(v_unused_112_);
v___x_104_ = v_v_94_;
v_isShared_105_ = v_isSharedCheck_111_;
goto v_resetjp_103_;
}
else
{
lean_dec(v_v_94_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_111_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = 0;
v___x_107_ = lean_box(v___x_106_);
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 0);
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_94_ = stack[0].m_obj;
lean_object* v_f_95_ = stack[1].m_obj;
lean_object* v___y_96_ = stack[2].m_obj;
lean_object* v___y_97_ = stack[3].m_obj;
lean_object* v___y_98_ = stack[4].m_obj;
lean_object* v___y_99_ = stack[5].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_94_, v_f_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg___boxed(lean_object* v_v_114_, lean_object* v_f_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_114_, v_f_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(uint8_t v_pu_122_, lean_object* v_v_123_, lean_object* v_f_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_123_, v_f_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_122_ = stack[0].m_num;
lean_object* v_v_123_ = stack[1].m_obj;
lean_object* v_f_124_ = stack[2].m_obj;
lean_object* v___y_125_ = stack[3].m_obj;
lean_object* v___y_126_ = stack[4].m_obj;
lean_object* v___y_127_ = stack[5].m_obj;
lean_object* v___y_128_ = stack[6].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(v_pu_122_, v_v_123_, v_f_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___boxed(lean_object* v_pu_132_, lean_object* v_v_133_, lean_object* v_f_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
uint8_t v_pu_boxed_140_; lean_object* v_res_141_; 
v_pu_boxed_140_ = lean_unbox(v_pu_132_);
v_res_141_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(v_pu_boxed_140_, v_v_133_, v_f_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_141_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(lean_object* v_toSignature_142_, uint8_t v_a_143_, uint8_t v_pu_144_, lean_object* v_code_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; lean_object* v_env_152_; lean_object* v_name_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_151_ = lean_st_ref_get(v___y_149_);
v_env_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_env_152_);
lean_dec(v___x_151_);
v_name_153_ = lean_ctor_get(v_toSignature_142_, 0);
lean_inc(v_name_153_);
lean_dec_ref(v_toSignature_142_);
v___x_154_ = 1;
v___x_155_ = l_Lean_Environment_setExporting(v_env_152_, v___x_154_);
v___x_156_ = l_Lean_Environment_findAsync_x3f(v___x_155_, v_name_153_, v_a_143_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_box(v_a_143_);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_178_; 
v_val_159_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_178_ == 0)
{
v___x_161_ = v___x_156_;
v_isShared_162_ = v_isSharedCheck_178_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_val_159_);
lean_dec(v___x_156_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_178_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
uint8_t v_kind_163_; uint8_t v___x_164_; uint8_t v___x_165_; 
v_kind_163_ = lean_ctor_get_uint8(v_val_159_, sizeof(void*)*3);
lean_dec(v_val_159_);
v___x_164_ = 0;
v___x_165_ = l_Lean_instBEqConstantKind_beq(v_kind_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_box(v___x_165_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 0);
lean_ctor_set(v___x_161_, 0, v___x_166_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_170_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_148_);
v___x_171_ = l_Lean_Compiler_LCNF_compiler_small;
v___x_172_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v___x_170_, v___x_171_);
lean_dec_ref(v___x_170_);
v___x_173_ = l_Lean_Compiler_LCNF_Code_sizeLe(v_pu_144_, v_code_145_, v___x_172_);
lean_dec(v___x_172_);
v___x_174_ = lean_box(v___x_173_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 0);
lean_ctor_set(v___x_161_, 0, v___x_174_);
v___x_176_ = v___x_161_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toSignature_142_ = stack[0].m_obj;
uint8_t v_a_143_ = stack[1].m_num;
uint8_t v_pu_144_ = stack[2].m_num;
lean_object* v_code_145_ = stack[3].m_obj;
lean_object* v___y_146_ = stack[4].m_obj;
lean_object* v___y_147_ = stack[5].m_obj;
lean_object* v___y_148_ = stack[6].m_obj;
lean_object* v___y_149_ = stack[7].m_obj;
lean_object* v_res_179_;
v_res_179_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_142_, v_a_143_, v_pu_144_, v_code_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed(lean_object* v_toSignature_180_, lean_object* v_a_181_, lean_object* v_pu_182_, lean_object* v_code_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
uint8_t v_a_1001__boxed_189_; uint8_t v_pu_boxed_190_; lean_object* v_res_191_; 
v_a_1001__boxed_189_ = lean_unbox(v_a_181_);
v_pu_boxed_190_ = lean_unbox(v_pu_182_);
v_res_191_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_180_, v_a_1001__boxed_189_, v_pu_boxed_190_, v_code_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v_code_183_);
return v_res_191_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(uint8_t v_pu_192_, lean_object* v_decl_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_199_; 
lean_inc_ref(v_decl_193_);
v___x_199_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_193_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; uint8_t v___x_201_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v___x_201_ = lean_unbox(v_a_200_);
if (v___x_201_ == 0)
{
lean_object* v_toSignature_202_; lean_object* v_value_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; 
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
v_toSignature_202_ = lean_ctor_get(v_decl_193_, 0);
lean_inc_ref(v_toSignature_202_);
v_value_203_ = lean_ctor_get(v_decl_193_, 1);
lean_inc_ref(v_value_203_);
lean_dec_ref(v_decl_193_);
v___x_204_ = lean_box(v_pu_192_);
v___f_205_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed), 9, 3);
lean_closure_set(v___f_205_, 0, v_toSignature_202_);
lean_closure_set(v___f_205_, 1, v_a_200_);
lean_closure_set(v___f_205_, 2, v___x_204_);
v___x_206_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_value_203_, v___f_205_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
return v___x_206_;
}
else
{
lean_dec_ref(v_decl_193_);
return v___x_199_;
}
}
else
{
lean_dec_ref(v_decl_193_);
return v___x_199_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_192_ = stack[0].m_num;
lean_object* v_decl_193_ = stack[1].m_obj;
lean_object* v_a_194_ = stack[2].m_obj;
lean_object* v_a_195_ = stack[3].m_obj;
lean_object* v_a_196_ = stack[4].m_obj;
lean_object* v_a_197_ = stack[5].m_obj;
lean_object* v_res_207_;
v_res_207_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_192_, v_decl_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(lean_object* v_pu_208_, lean_object* v_decl_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
uint8_t v_pu_boxed_215_; lean_object* v_res_216_; 
v_pu_boxed_215_ = lean_unbox(v_pu_208_);
v_res_216_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_boxed_215_, v_decl_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_216_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_217_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_221_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_ctor_set(v___x_223_, 3, v___x_222_);
lean_ctor_set(v___x_223_, 4, v___x_221_);
lean_ctor_set(v___x_223_, 5, v___x_221_);
lean_ctor_set(v___x_223_, 6, v___x_221_);
lean_ctor_set(v___x_223_, 7, v___x_221_);
lean_ctor_set(v___x_223_, 8, v___x_221_);
lean_ctor_set(v___x_223_, 9, v___x_221_);
lean_ctor_set(v___x_223_, 10, v___x_221_);
lean_ctor_set(v___x_223_, 11, v___x_220_);
return v___x_223_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_224_; double v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_float_of_nat(v___x_224_);
return v___x_225_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(lean_object* v_cls_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_ref_236_; lean_object* v___x_237_; lean_object* v_env_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_ref_236_ = lean_ctor_get(v___y_233_, 2);
v___x_237_ = lean_st_ref_get(v___y_234_);
v_env_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_env_238_);
lean_dec(v___x_237_);
v___x_239_ = lean_st_ref_get(v___y_232_);
v___x_240_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_231_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_300_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_300_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_300_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_300_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_lctx_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_298_; 
v_lctx_245_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_239_, 1);
lean_dec(v_unused_299_);
v___x_247_ = v___x_239_;
v_isShared_248_ = v_isSharedCheck_298_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_lctx_245_);
lean_dec(v___x_239_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_298_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_249_ = lean_unbox(v_a_241_);
lean_dec(v_a_241_);
v___x_250_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_245_, v___x_249_);
lean_dec_ref(v_lctx_245_);
v___x_251_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_233_);
v___x_252_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_253_, 0, v_env_238_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
lean_ctor_set(v___x_253_, 2, v___x_250_);
lean_ctor_set(v___x_253_, 3, v___x_251_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 3);
lean_ctor_set(v___x_247_, 1, v_msg_230_);
lean_ctor_set(v___x_247_, 0, v___x_253_);
v___x_255_ = v___x_247_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_msg_230_);
v___x_255_ = v_reuseFailAlloc_297_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v_traceState_257_; lean_object* v_env_258_; lean_object* v_nextMacroScope_259_; lean_object* v_ngen_260_; lean_object* v_auxDeclNGen_261_; lean_object* v_cache_262_; lean_object* v_recordedDeps_263_; lean_object* v_messages_264_; lean_object* v_infoState_265_; lean_object* v_snapshotTasks_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_296_; 
v___x_256_ = lean_st_ref_take(v___y_234_);
v_traceState_257_ = lean_ctor_get(v___x_256_, 4);
v_env_258_ = lean_ctor_get(v___x_256_, 0);
v_nextMacroScope_259_ = lean_ctor_get(v___x_256_, 1);
v_ngen_260_ = lean_ctor_get(v___x_256_, 2);
v_auxDeclNGen_261_ = lean_ctor_get(v___x_256_, 3);
v_cache_262_ = lean_ctor_get(v___x_256_, 5);
v_recordedDeps_263_ = lean_ctor_get(v___x_256_, 6);
v_messages_264_ = lean_ctor_get(v___x_256_, 7);
v_infoState_265_ = lean_ctor_get(v___x_256_, 8);
v_snapshotTasks_266_ = lean_ctor_get(v___x_256_, 9);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_296_ == 0)
{
v___x_268_ = v___x_256_;
v_isShared_269_ = v_isSharedCheck_296_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_snapshotTasks_266_);
lean_inc(v_infoState_265_);
lean_inc(v_messages_264_);
lean_inc(v_recordedDeps_263_);
lean_inc(v_cache_262_);
lean_inc(v_traceState_257_);
lean_inc(v_auxDeclNGen_261_);
lean_inc(v_ngen_260_);
lean_inc(v_nextMacroScope_259_);
lean_inc(v_env_258_);
lean_dec(v___x_256_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_296_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
uint64_t v_tid_270_; lean_object* v_traces_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_295_; 
v_tid_270_ = lean_ctor_get_uint64(v_traceState_257_, sizeof(void*)*1);
v_traces_271_ = lean_ctor_get(v_traceState_257_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_traceState_257_);
if (v_isSharedCheck_295_ == 0)
{
v___x_273_ = v_traceState_257_;
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_traces_271_);
lean_dec(v_traceState_257_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; double v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_275_ = lean_box(0);
v___x_276_ = lean_box(0);
v___x_277_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_278_ = 0;
v___x_279_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_280_, 0, v_cls_229_);
lean_ctor_set(v___x_280_, 1, v___x_276_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
lean_ctor_set_float(v___x_280_, sizeof(void*)*3, v___x_277_);
lean_ctor_set_float(v___x_280_, sizeof(void*)*3 + 8, v___x_277_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*3 + 16, v___x_278_);
v___x_281_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_255_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_inc(v_ref_236_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_ref_236_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l_Lean_PersistentArray_push___redArg(v_traces_271_, v___x_283_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_284_);
v___x_286_ = v___x_273_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_284_);
lean_ctor_set_uint64(v_reuseFailAlloc_294_, sizeof(void*)*1, v_tid_270_);
v___x_286_ = v_reuseFailAlloc_294_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v___x_286_);
v___x_288_ = v___x_268_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_env_258_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_nextMacroScope_259_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_ngen_260_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_auxDeclNGen_261_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v_cache_262_);
lean_ctor_set(v_reuseFailAlloc_293_, 6, v_recordedDeps_263_);
lean_ctor_set(v_reuseFailAlloc_293_, 7, v_messages_264_);
lean_ctor_set(v_reuseFailAlloc_293_, 8, v_infoState_265_);
lean_ctor_set(v_reuseFailAlloc_293_, 9, v_snapshotTasks_266_);
v___x_288_ = v_reuseFailAlloc_293_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_st_ref_put(v___y_234_, v___x_288_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_275_);
v___x_291_ = v___x_243_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_275_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
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
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v___x_239_);
lean_dec_ref(v_env_238_);
lean_dec_ref(v_msg_230_);
lean_dec(v_cls_229_);
v_a_301_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_240_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_240_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_229_ = stack[0].m_obj;
lean_object* v_msg_230_ = stack[1].m_obj;
lean_object* v___y_231_ = stack[2].m_obj;
lean_object* v___y_232_ = stack[3].m_obj;
lean_object* v___y_233_ = stack[4].m_obj;
lean_object* v___y_234_ = stack[5].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v_cls_229_, v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___boxed(lean_object* v_cls_310_, lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v_cls_310_, v_msg_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(lean_object* v_f_318_, lean_object* v_v_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
if (lean_obj_tag(v_v_319_) == 0)
{
lean_object* v_code_325_; lean_object* v___x_326_; 
v_code_325_ = lean_ctor_get(v_v_319_, 0);
lean_inc_ref(v_code_325_);
lean_dec_ref_known(v_v_319_, 1);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v___y_321_);
lean_inc_ref(v___y_320_);
v___x_326_ = lean_apply_6(v_f_318_, v_code_325_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, lean_box(0));
return v___x_326_;
}
else
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_f_318_);
v_isSharedCheck_334_ = !lean_is_exclusive(v_v_319_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_v_319_, 0);
lean_dec(v_unused_335_);
v___x_328_ = v_v_319_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_v_319_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_box(0);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 0);
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_318_ = stack[0].m_obj;
lean_object* v_v_319_ = stack[1].m_obj;
lean_object* v___y_320_ = stack[2].m_obj;
lean_object* v___y_321_ = stack[3].m_obj;
lean_object* v___y_322_ = stack[4].m_obj;
lean_object* v___y_323_ = stack[5].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_318_, v_v_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg___boxed(lean_object* v_f_337_, lean_object* v_v_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_337_, v_v_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(uint8_t v_pu_345_, lean_object* v_f_346_, lean_object* v_v_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_346_, v_v_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_353_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_345_ = stack[0].m_num;
lean_object* v_f_346_ = stack[1].m_obj;
lean_object* v_v_347_ = stack[2].m_obj;
lean_object* v___y_348_ = stack[3].m_obj;
lean_object* v___y_349_ = stack[4].m_obj;
lean_object* v___y_350_ = stack[5].m_obj;
lean_object* v___y_351_ = stack[6].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_345_, v_f_346_, v_v_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(lean_object* v_pu_355_, lean_object* v_f_356_, lean_object* v_v_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
uint8_t v_pu_boxed_363_; lean_object* v_res_364_; 
v_pu_boxed_363_ = lean_unbox(v_pu_355_);
v_res_364_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_boxed_363_, v_f_356_, v_v_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object* v_pu_365_, lean_object* v_phase_366_, lean_object* v_decl_367_, lean_object* v_code_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v_pu_boxed_374_; uint8_t v_phase_boxed_375_; lean_object* v_res_376_; 
v_pu_boxed_374_ = lean_unbox(v_pu_365_);
v_phase_boxed_375_ = lean_unbox(v_phase_366_);
v_res_376_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(v_pu_boxed_374_, v_phase_boxed_375_, v_decl_367_, v_code_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_390_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_391_ = l_Lean_Name_append(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec(uint8_t v_pu_398_, uint8_t v_phase_399_, lean_object* v_decl_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___f_408_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___x_416_; lean_object* v_toSignature_417_; lean_object* v_env_418_; lean_object* v_nextMacroScope_419_; lean_object* v_ngen_420_; lean_object* v_auxDeclNGen_421_; lean_object* v_traceState_422_; lean_object* v_recordedDeps_423_; lean_object* v_messages_424_; lean_object* v_infoState_425_; lean_object* v_snapshotTasks_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_497_; 
v___x_406_ = lean_box(v_pu_398_);
v___x_407_ = lean_box(v_phase_399_);
lean_inc_ref(v_decl_400_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed), 9, 3);
lean_closure_set(v___f_408_, 0, v___x_406_);
lean_closure_set(v___f_408_, 1, v___x_407_);
lean_closure_set(v___f_408_, 2, v_decl_400_);
v___x_416_ = lean_st_ref_take(v_a_404_);
v_toSignature_417_ = lean_ctor_get(v_decl_400_, 0);
v_env_418_ = lean_ctor_get(v___x_416_, 0);
v_nextMacroScope_419_ = lean_ctor_get(v___x_416_, 1);
v_ngen_420_ = lean_ctor_get(v___x_416_, 2);
v_auxDeclNGen_421_ = lean_ctor_get(v___x_416_, 3);
v_traceState_422_ = lean_ctor_get(v___x_416_, 4);
v_recordedDeps_423_ = lean_ctor_get(v___x_416_, 6);
v_messages_424_ = lean_ctor_get(v___x_416_, 7);
v_infoState_425_ = lean_ctor_get(v___x_416_, 8);
v_snapshotTasks_426_ = lean_ctor_get(v___x_416_, 9);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_416_, 5);
lean_dec(v_unused_498_);
v___x_428_ = v___x_416_;
v_isShared_429_ = v_isSharedCheck_497_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snapshotTasks_426_);
lean_inc(v_infoState_425_);
lean_inc(v_messages_424_);
lean_inc(v_recordedDeps_423_);
lean_inc(v_traceState_422_);
lean_inc(v_auxDeclNGen_421_);
lean_inc(v_ngen_420_);
lean_inc(v_nextMacroScope_419_);
lean_inc(v_env_418_);
lean_dec(v___x_416_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_497_;
goto v_resetjp_427_;
}
v___jp_409_:
{
lean_object* v_value_414_; lean_object* v___x_415_; 
v_value_414_ = lean_ctor_get(v_decl_400_, 1);
lean_inc_ref(v_value_414_);
lean_dec_ref(v_decl_400_);
v___x_415_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_408_, v_value_414_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
return v___x_415_;
}
v_resetjp_427_:
{
lean_object* v_name_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___x_459_; 
v_name_430_ = lean_ctor_get(v_toSignature_417_, 0);
lean_inc(v_name_430_);
v___x_431_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_418_, v_name_430_);
v___x_432_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 5, v___x_432_);
lean_ctor_set(v___x_428_, 0, v___x_431_);
v___x_459_ = v___x_428_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_nextMacroScope_419_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_ngen_420_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_auxDeclNGen_421_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_traceState_422_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_recordedDeps_423_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_messages_424_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_infoState_425_);
lean_ctor_set(v_reuseFailAlloc_496_, 9, v_snapshotTasks_426_);
v___x_459_ = v_reuseFailAlloc_496_;
goto v_reusejp_458_;
}
v___jp_433_:
{
lean_object* v___x_438_; lean_object* v_env_439_; lean_object* v_nextMacroScope_440_; lean_object* v_ngen_441_; lean_object* v_auxDeclNGen_442_; lean_object* v_traceState_443_; lean_object* v_recordedDeps_444_; lean_object* v_messages_445_; lean_object* v_infoState_446_; lean_object* v_snapshotTasks_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v___x_438_ = lean_st_ref_take(v___y_437_);
v_env_439_ = lean_ctor_get(v___x_438_, 0);
v_nextMacroScope_440_ = lean_ctor_get(v___x_438_, 1);
v_ngen_441_ = lean_ctor_get(v___x_438_, 2);
v_auxDeclNGen_442_ = lean_ctor_get(v___x_438_, 3);
v_traceState_443_ = lean_ctor_get(v___x_438_, 4);
v_recordedDeps_444_ = lean_ctor_get(v___x_438_, 6);
v_messages_445_ = lean_ctor_get(v___x_438_, 7);
v_infoState_446_ = lean_ctor_get(v___x_438_, 8);
v_snapshotTasks_447_ = lean_ctor_get(v___x_438_, 9);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_438_, 5);
lean_dec(v_unused_457_);
v___x_449_ = v___x_438_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_snapshotTasks_447_);
lean_inc(v_infoState_446_);
lean_inc(v_messages_445_);
lean_inc(v_recordedDeps_444_);
lean_inc(v_traceState_443_);
lean_inc(v_auxDeclNGen_442_);
lean_inc(v_ngen_441_);
lean_inc(v_nextMacroScope_440_);
lean_inc(v_env_439_);
lean_dec(v___x_438_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_inc(v_name_430_);
v___x_451_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_439_, v_phase_399_, v_name_430_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 5, v___x_432_);
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_nextMacroScope_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_ngen_441_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_auxDeclNGen_442_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_traceState_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_recordedDeps_444_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_messages_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_infoState_446_);
lean_ctor_set(v_reuseFailAlloc_455_, 9, v_snapshotTasks_447_);
v___x_453_ = v_reuseFailAlloc_455_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; 
v___x_454_ = lean_st_ref_put(v___y_437_, v___x_453_);
v___y_410_ = v___y_434_;
v___y_411_ = v___y_435_;
v___y_412_ = v___y_436_;
v___y_413_ = v___y_437_;
goto v___jp_409_;
}
}
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_st_ref_put(v_a_404_, v___x_459_);
lean_inc_ref(v_decl_400_);
v___x_461_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_398_, v_decl_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_487_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_487_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_487_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_487_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = lean_unbox(v_a_462_);
lean_dec(v_a_462_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec_ref(v___f_408_);
lean_dec_ref(v_decl_400_);
v___x_467_ = lean_box(0);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v___x_471_; lean_object* v_env_472_; uint8_t v___x_473_; 
lean_del_object(v___x_464_);
v___x_471_ = lean_st_ref_get(v_a_404_);
v_env_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc_ref(v_env_472_);
lean_dec(v___x_471_);
v___x_473_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_472_, v_phase_399_, v_name_430_);
if (v___x_473_ == 0)
{
lean_object* v_toCold_474_; lean_object* v_options_475_; uint8_t v_hasTrace_476_; 
v_toCold_474_ = lean_ctor_get(v_a_403_, 0);
v_options_475_ = lean_ctor_get(v_toCold_474_, 2);
v_hasTrace_476_ = lean_ctor_get_uint8(v_options_475_, sizeof(void*)*1);
if (v_hasTrace_476_ == 0)
{
v___y_434_ = v_a_401_;
v___y_435_ = v_a_402_;
v___y_436_ = v_a_403_;
v___y_437_ = v_a_404_;
goto v___jp_433_;
}
else
{
lean_object* v_inheritedTraceOptions_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_inheritedTraceOptions_477_ = lean_ctor_get(v_toCold_474_, 11);
v___x_478_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_479_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_477_, v_options_475_, v___x_479_);
if (v___x_480_ == 0)
{
v___y_434_ = v_a_401_;
v___y_435_ = v_a_402_;
v___y_436_ = v_a_403_;
v___y_437_ = v_a_404_;
goto v___jp_433_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_481_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_430_);
v___x_482_ = l_Lean_MessageData_ofName(v_name_430_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_478_, v___x_485_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_dec_ref_known(v___x_486_, 1);
v___y_434_ = v_a_401_;
v___y_435_ = v_a_402_;
v___y_436_ = v_a_403_;
v___y_437_ = v_a_404_;
goto v___jp_433_;
}
else
{
lean_dec_ref(v___f_408_);
lean_dec_ref(v_decl_400_);
return v___x_486_;
}
}
}
}
else
{
v___y_410_ = v_a_401_;
v___y_411_ = v_a_402_;
v___y_412_ = v_a_403_;
v___y_413_ = v_a_404_;
goto v___jp_409_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v___f_408_);
lean_dec_ref(v_decl_400_);
v_a_488_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_461_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_461_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_markDeclPublicRec_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_398_ = stack[0].m_num;
uint8_t v_phase_399_ = stack[1].m_num;
lean_object* v_decl_400_ = stack[2].m_obj;
lean_object* v_a_401_ = stack[3].m_obj;
lean_object* v_a_402_ = stack[4].m_obj;
lean_object* v_a_403_ = stack[5].m_obj;
lean_object* v_a_404_ = stack[6].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_398_, v_phase_399_, v_decl_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
stack->m_obj
 = v_res_499_;
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(uint8_t v_phase_503_, lean_object* v_decl_504_, lean_object* v_init_505_, lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_k_512_; lean_object* v_l_513_; lean_object* v_r_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_k_512_ = lean_ctor_get(v_x_506_, 1);
lean_inc(v_k_512_);
v_l_513_ = lean_ctor_get(v_x_506_, 3);
lean_inc(v_l_513_);
v_r_514_ = lean_ctor_get(v_x_506_, 4);
lean_inc(v_r_514_);
lean_dec_ref_known(v_x_506_, 5);
v___x_515_ = lean_box(0);
lean_inc_ref(v_decl_504_);
v___x_516_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_503_, v_decl_504_, v_init_505_, v_l_513_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; 
lean_dec_ref_known(v___x_516_, 1);
v___x_517_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_512_, v_phase_503_, v___y_510_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
if (lean_obj_tag(v_a_518_) == 1)
{
lean_object* v_val_519_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___x_536_; lean_object* v_env_537_; uint8_t v___x_538_; 
v_val_519_ = lean_ctor_get(v_a_518_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_a_518_, 1);
v___x_536_ = lean_st_ref_get(v___y_510_);
v_env_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_env_537_);
lean_dec(v___x_536_);
v___x_538_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_537_, v_k_512_);
if (v___x_538_ == 0)
{
lean_object* v_toCold_539_; lean_object* v_options_540_; uint8_t v_hasTrace_541_; 
v_toCold_539_ = lean_ctor_get(v___y_509_, 0);
v_options_540_ = lean_ctor_get(v_toCold_539_, 2);
v_hasTrace_541_ = lean_ctor_get_uint8(v_options_540_, sizeof(void*)*1);
if (v_hasTrace_541_ == 0)
{
lean_dec(v_k_512_);
v___y_521_ = v___y_507_;
v___y_522_ = v___y_508_;
v___y_523_ = v___y_509_;
v___y_524_ = v___y_510_;
goto v___jp_520_;
}
else
{
lean_object* v_inheritedTraceOptions_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_inheritedTraceOptions_542_ = lean_ctor_get(v_toCold_539_, 11);
v___x_543_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_544_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_542_, v_options_540_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v_k_512_);
v___y_521_ = v___y_507_;
v___y_522_ = v___y_508_;
v___y_523_ = v___y_509_;
v___y_524_ = v___y_510_;
goto v___jp_520_;
}
else
{
lean_object* v_toSignature_546_; lean_object* v_name_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_toSignature_546_ = lean_ctor_get(v_decl_504_, 0);
v_name_547_ = lean_ctor_get(v_toSignature_546_, 0);
v___x_548_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
v___x_549_ = l_Lean_MessageData_ofName(v_k_512_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
lean_inc(v_name_547_);
v___x_553_ = l_Lean_MessageData_ofName(v_name_547_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_543_, v___x_554_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_dec_ref_known(v___x_555_, 1);
v___y_521_ = v___y_507_;
v___y_522_ = v___y_508_;
v___y_523_ = v___y_509_;
v___y_524_ = v___y_510_;
goto v___jp_520_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_val_519_);
lean_dec(v_r_514_);
lean_dec_ref(v_decl_504_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
else
{
lean_dec(v_val_519_);
lean_dec(v_k_512_);
v_init_505_ = v___x_515_;
v_x_506_ = v_r_514_;
goto _start;
}
v___jp_520_:
{
uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_525_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_503_);
v___x_526_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_525_, v_phase_503_, v_val_519_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_dec_ref_known(v___x_526_, 1);
v_init_505_ = v___x_515_;
v_x_506_ = v_r_514_;
goto _start;
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_r_514_);
lean_dec_ref(v_decl_504_);
v_a_528_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_526_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
else
{
lean_dec(v_a_518_);
lean_dec(v_k_512_);
v_init_505_ = v___x_515_;
v_x_506_ = v_r_514_;
goto _start;
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_r_514_);
lean_dec(v_k_512_);
lean_dec_ref(v_decl_504_);
v_a_566_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_517_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_517_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_dec(v_r_514_);
lean_dec(v_k_512_);
lean_dec_ref(v_decl_504_);
return v___x_516_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_decl_504_);
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_init_505_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_503_ = stack[0].m_num;
lean_object* v_decl_504_ = stack[1].m_obj;
lean_object* v_init_505_ = stack[2].m_obj;
lean_object* v_x_506_ = stack[3].m_obj;
lean_object* v___y_507_ = stack[4].m_obj;
lean_object* v___y_508_ = stack[5].m_obj;
lean_object* v___y_509_ = stack[6].m_obj;
lean_object* v___y_510_ = stack[7].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_503_, v_decl_504_, v_init_505_, v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_576_;
}
lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t v_pu_577_, uint8_t v_phase_578_, lean_object* v_decl_579_, lean_object* v_code_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_586_ = l_Lean_NameSet_empty;
v___x_587_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_577_, v_code_580_, v___x_586_);
v___x_588_ = lean_box(0);
v___x_589_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_578_, v_decl_579_, v___x_588_, v___x_587_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_597_);
v___x_591_ = v___x_589_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_dec(v___x_589_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_588_);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_588_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_589_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_589_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_577_ = stack[0].m_num;
uint8_t v_phase_578_ = stack[1].m_num;
lean_object* v_decl_579_ = stack[2].m_obj;
lean_object* v_code_580_ = stack[3].m_obj;
lean_object* v___y_581_ = stack[4].m_obj;
lean_object* v___y_582_ = stack[5].m_obj;
lean_object* v___y_583_ = stack[6].m_obj;
lean_object* v___y_584_ = stack[7].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(v_pu_577_, v_phase_578_, v_decl_579_, v_code_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object* v_phase_607_, lean_object* v_decl_608_, lean_object* v_init_609_, lean_object* v_x_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
uint8_t v_phase_boxed_616_; lean_object* v_res_617_; 
v_phase_boxed_616_ = lean_unbox(v_phase_607_);
v_res_617_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_616_, v_decl_608_, v_init_609_, v_x_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object* v_pu_618_, lean_object* v_phase_619_, lean_object* v_decl_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
uint8_t v_pu_boxed_626_; uint8_t v_phase_boxed_627_; lean_object* v_res_628_; 
v_pu_boxed_626_ = lean_unbox(v_pu_618_);
v_phase_boxed_627_ = lean_unbox(v_phase_619_);
v_res_628_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_boxed_626_, v_phase_boxed_627_, v_decl_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_628_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_ref_635_; lean_object* v___x_636_; lean_object* v_env_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_ref_635_ = lean_ctor_get(v___y_632_, 2);
v___x_636_ = lean_st_ref_get(v___y_633_);
v_env_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_636_);
v___x_638_ = lean_st_ref_get(v___y_631_);
v___x_639_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_630_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_662_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_662_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_662_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_662_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_lctx_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_660_; 
v_lctx_644_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_638_, 1);
lean_dec(v_unused_661_);
v___x_646_ = v___x_638_;
v_isShared_647_ = v_isSharedCheck_660_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_lctx_644_);
lean_dec(v___x_638_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_660_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_648_ = lean_unbox(v_a_640_);
lean_dec(v_a_640_);
v___x_649_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_644_, v___x_648_);
lean_dec_ref(v_lctx_644_);
v___x_650_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_632_);
v___x_651_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_652_, 0, v_env_637_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_ctor_set(v___x_652_, 2, v___x_649_);
lean_ctor_set(v___x_652_, 3, v___x_650_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 3);
lean_ctor_set(v___x_646_, 1, v_msg_629_);
lean_ctor_set(v___x_646_, 0, v___x_652_);
v___x_654_ = v___x_646_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_msg_629_);
v___x_654_ = v_reuseFailAlloc_659_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
lean_inc(v_ref_635_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_ref_635_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 0, v___x_655_);
v___x_657_ = v___x_642_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___x_638_);
lean_dec_ref(v_env_637_);
lean_dec_ref(v_msg_629_);
v_a_663_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_639_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_639_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_629_ = stack[0].m_obj;
lean_object* v___y_630_ = stack[1].m_obj;
lean_object* v___y_631_ = stack[2].m_obj;
lean_object* v___y_632_ = stack[3].m_obj;
lean_object* v___y_633_ = stack[4].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_680_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_680_ = stack[1].m_obj;
lean_object* v___y_681_ = stack[2].m_obj;
lean_object* v___y_682_ = stack[3].m_obj;
lean_object* v___y_683_ = stack[4].m_obj;
lean_object* v___y_684_ = stack[5].m_obj;
lean_object* v___y_685_ = stack[6].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_box(0), v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_689_, v_msg_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
return v_res_697_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_698_, lean_object* v_opt_699_){
_start:
{
lean_object* v_name_700_; lean_object* v_defValue_701_; lean_object* v_map_702_; lean_object* v___x_703_; 
v_name_700_ = lean_ctor_get(v_opt_699_, 0);
v_defValue_701_ = lean_ctor_get(v_opt_699_, 1);
v_map_702_ = lean_ctor_get(v_opts_698_, 0);
v___x_703_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_702_, v_name_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
uint8_t v___x_704_; 
v___x_704_ = lean_unbox(v_defValue_701_);
return v___x_704_;
}
else
{
lean_object* v_val_705_; 
v_val_705_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_703_, 1);
if (lean_obj_tag(v_val_705_) == 1)
{
uint8_t v_v_706_; 
v_v_706_ = lean_ctor_get_uint8(v_val_705_, 0);
lean_dec_ref_known(v_val_705_, 0);
return v_v_706_;
}
else
{
uint8_t v___x_707_; 
lean_dec(v_val_705_);
v___x_707_ = lean_unbox(v_defValue_701_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_698_ = stack[0].m_obj;
lean_object* v_opt_699_ = stack[1].m_obj;
uint8_t v_res_708_;
v_res_708_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_698_, v_opt_699_);
stack->m_num = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_709_, lean_object* v_opt_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_709_, v_opt_710_);
lean_dec_ref(v_opt_710_);
lean_dec_ref(v_opts_709_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_713_, lean_object* v_v_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
if (lean_obj_tag(v_v_714_) == 0)
{
lean_object* v_code_721_; lean_object* v___x_722_; 
v_code_721_ = lean_ctor_get(v_v_714_, 0);
lean_inc_ref(v_code_721_);
lean_dec_ref_known(v_v_714_, 1);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
v___x_722_ = lean_apply_7(v_f_713_, v_code_721_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
return v___x_722_;
}
else
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_f_713_);
v_isSharedCheck_731_ = !lean_is_exclusive(v_v_714_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_v_714_, 0);
lean_dec(v_unused_732_);
v___x_724_ = v_v_714_;
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_v_714_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___y_715_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 0);
lean_ctor_set(v___x_724_, 0, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_713_ = stack[0].m_obj;
lean_object* v_v_714_ = stack[1].m_obj;
lean_object* v___y_715_ = stack[2].m_obj;
lean_object* v___y_716_ = stack[3].m_obj;
lean_object* v___y_717_ = stack[4].m_obj;
lean_object* v___y_718_ = stack[5].m_obj;
lean_object* v___y_719_ = stack[6].m_obj;
lean_object* v_res_733_;
v_res_733_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_713_, v_v_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_734_, lean_object* v_v_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_734_, v_v_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_743_, lean_object* v_f_744_, lean_object* v_v_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_744_, v_v_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_752_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_743_ = stack[0].m_num;
lean_object* v_f_744_ = stack[1].m_obj;
lean_object* v_v_745_ = stack[2].m_obj;
lean_object* v___y_746_ = stack[3].m_obj;
lean_object* v___y_747_ = stack[4].m_obj;
lean_object* v___y_748_ = stack[5].m_obj;
lean_object* v___y_749_ = stack[6].m_obj;
lean_object* v___y_750_ = stack[7].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_743_, v_f_744_, v_v_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_754_, lean_object* v_f_755_, lean_object* v_v_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
uint8_t v_pu_boxed_763_; lean_object* v_res_764_; 
v_pu_boxed_763_ = lean_unbox(v_pu_754_);
v_res_764_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_763_, v_f_755_, v_v_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_764_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_798_, lean_object* v_origDecl_799_, uint8_t v_isMeta_800_, uint8_t v_isPublic_801_, lean_object* v_init_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v_k_810_; lean_object* v_l_811_; lean_object* v_r_812_; lean_object* v___x_813_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; uint8_t v___y_864_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_k_810_ = lean_ctor_get(v_x_803_, 1);
lean_inc(v_k_810_);
v_l_811_ = lean_ctor_get(v_x_803_, 3);
lean_inc(v_l_811_);
v_r_812_ = lean_ctor_get(v_x_803_, 4);
lean_inc(v_r_812_);
lean_dec_ref_known(v_x_803_, 5);
v___x_813_ = lean_box(0);
v___x_866_ = lean_box(0);
lean_inc_ref(v_origDecl_799_);
v___x_867_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_798_, v_origDecl_799_, v_isMeta_800_, v_isPublic_801_, v_init_802_, v_l_811_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_snd_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_1174_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_snd_869_ = lean_ctor_get(v_a_868_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_a_868_, 0);
lean_dec(v_unused_1175_);
v___x_871_ = v_a_868_;
v_isShared_872_ = v_isSharedCheck_1174_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_snd_869_);
lean_dec(v_a_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_1174_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; uint8_t v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; uint8_t v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; 
v___x_873_ = l_Lean_NameSet_contains(v_snd_869_, v_k_810_);
if (v___x_873_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_env_915_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_952_; uint8_t v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; uint8_t v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; uint8_t v___y_968_; lean_object* v___y_970_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; lean_object* v___y_978_; uint8_t v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; uint8_t v___y_987_; uint8_t v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; uint8_t v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1059_; uint8_t v___y_1060_; uint8_t v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; uint8_t v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; uint8_t v___y_1077_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1127_; uint8_t v___y_1155_; 
lean_inc(v_k_810_);
v___x_913_ = l_Lean_NameSet_insert(v_snd_869_, v_k_810_);
v___x_914_ = lean_st_ref_get(v___y_808_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_env_915_);
lean_dec(v___x_914_);
if (v_isMeta_800_ == 0)
{
v___y_1155_ = v___x_873_;
goto v___jp_1154_;
}
else
{
v___y_1155_ = v_isPublic_801_;
goto v___jp_1154_;
}
v___jp_916_:
{
lean_object* v_toSignature_924_; lean_object* v_name_925_; lean_object* v___x_926_; lean_object* v_moduleNames_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v___y_919_);
v_toSignature_924_ = lean_ctor_get(v_origDecl_799_, 0);
lean_inc_ref(v_toSignature_924_);
lean_dec_ref(v_origDecl_799_);
v_name_925_ = lean_ctor_get(v_toSignature_924_, 0);
lean_inc(v_name_925_);
lean_dec_ref(v_toSignature_924_);
v___x_926_ = l_Lean_Environment_header(v_env_915_);
lean_dec_ref(v_env_915_);
v_moduleNames_927_ = lean_ctor_get(v___x_926_, 4);
lean_inc_ref(v_moduleNames_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_Lean_MessageData_ofConstName(v_name_925_, v___x_873_);
v___x_929_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
v___x_931_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_MessageData_ofConstName(v_k_810_, v___x_873_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_array_get(v___x_866_, v_moduleNames_927_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v_moduleNames_927_);
v___x_938_ = l_Lean_MessageData_ofName(v___x_937_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_936_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_941_, v___y_921_, v___y_922_, v___y_920_, v___y_923_);
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
v___jp_951_:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_915_, v_k_810_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v_val_959_; uint8_t v___x_960_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v___x_958_, 1);
lean_inc(v_k_810_);
lean_inc_ref(v_env_915_);
v___x_960_ = l_Lean_isMarkedMeta(v_env_915_, v_k_810_);
if (v___x_960_ == 0)
{
lean_del_object(v___x_871_);
v___y_917_ = v_val_959_;
v___y_918_ = v___y_953_;
v___y_919_ = v___y_952_;
v___y_920_ = v___y_954_;
v___y_921_ = v___y_955_;
v___y_922_ = v___y_956_;
v___y_923_ = v___y_957_;
goto v___jp_916_;
}
else
{
if (v___x_873_ == 0)
{
lean_dec(v_val_959_);
lean_dec_ref(v_env_915_);
v___y_885_ = v___y_953_;
v___y_886_ = v___y_952_;
v___y_887_ = v___y_955_;
v___y_888_ = v___y_956_;
v___y_889_ = v___y_954_;
v___y_890_ = v___y_957_;
goto v___jp_884_;
}
else
{
lean_del_object(v___x_871_);
v___y_917_ = v_val_959_;
v___y_918_ = v___y_953_;
v___y_919_ = v___y_952_;
v___y_920_ = v___y_954_;
v___y_921_ = v___y_955_;
v___y_922_ = v___y_956_;
v___y_923_ = v___y_957_;
goto v___jp_916_;
}
}
}
else
{
lean_dec(v___x_958_);
lean_dec_ref(v_env_915_);
v___y_885_ = v___y_953_;
v___y_886_ = v___y_952_;
v___y_887_ = v___y_955_;
v___y_888_ = v___y_956_;
v___y_889_ = v___y_954_;
v___y_890_ = v___y_957_;
goto v___jp_884_;
}
}
v___jp_961_:
{
if (v___y_968_ == 0)
{
lean_dec_ref(v_env_915_);
lean_del_object(v___x_871_);
v___y_875_ = v___y_962_;
v___y_876_ = v___y_963_;
v___y_877_ = v___y_965_;
v___y_878_ = v___y_966_;
v___y_879_ = v___y_964_;
v___y_880_ = v___y_967_;
goto v___jp_874_;
}
else
{
lean_dec(v_r_812_);
v___y_952_ = v___y_963_;
v___y_953_ = v___y_962_;
v___y_954_ = v___y_964_;
v___y_955_ = v___y_965_;
v___y_956_ = v___y_966_;
v___y_957_ = v___y_967_;
goto v___jp_951_;
}
}
v___jp_969_:
{
if (v___y_976_ == 0)
{
v___y_962_ = v___y_971_;
v___y_963_ = v___y_970_;
v___y_964_ = v___y_972_;
v___y_965_ = v___y_973_;
v___y_966_ = v___y_974_;
v___y_967_ = v___y_975_;
v___y_968_ = v___x_873_;
goto v___jp_961_;
}
else
{
if (v_isMeta_800_ == 0)
{
lean_dec(v_r_812_);
v___y_952_ = v___y_970_;
v___y_953_ = v___y_971_;
v___y_954_ = v___y_972_;
v___y_955_ = v___y_973_;
v___y_956_ = v___y_974_;
v___y_957_ = v___y_975_;
goto v___jp_951_;
}
else
{
v___y_962_ = v___y_971_;
v___y_963_ = v___y_970_;
v___y_964_ = v___y_972_;
v___y_965_ = v___y_973_;
v___y_966_ = v___y_974_;
v___y_967_ = v___y_975_;
v___y_968_ = v___x_873_;
goto v___jp_961_;
}
}
}
v___jp_977_:
{
uint8_t v___x_984_; uint8_t v___x_985_; 
v___x_984_ = 1;
v___x_985_ = l_Lean_instBEqIRPhases_beq(v___y_979_, v___x_984_);
v___y_970_ = v___y_978_;
v___y_971_ = v___y_979_;
v___y_972_ = v___y_980_;
v___y_973_ = v___y_981_;
v___y_974_ = v___y_982_;
v___y_975_ = v___y_983_;
v___y_976_ = v___x_985_;
goto v___jp_969_;
}
v___jp_986_:
{
if (v___y_988_ == 0)
{
v___y_978_ = v___y_989_;
v___y_979_ = v___y_987_;
v___y_980_ = v___y_992_;
v___y_981_ = v___y_990_;
v___y_982_ = v___y_991_;
v___y_983_ = v___y_993_;
goto v___jp_977_;
}
else
{
if (v___x_873_ == 0)
{
v___y_970_ = v___y_989_;
v___y_971_ = v___y_987_;
v___y_972_ = v___y_992_;
v___y_973_ = v___y_990_;
v___y_974_ = v___y_991_;
v___y_975_ = v___y_993_;
v___y_976_ = v___x_873_;
goto v___jp_969_;
}
else
{
v___y_978_ = v___y_989_;
v___y_979_ = v___y_987_;
v___y_980_ = v___y_992_;
v___y_981_ = v___y_990_;
v___y_982_ = v___y_991_;
v___y_983_ = v___y_993_;
goto v___jp_977_;
}
}
}
v___jp_994_:
{
if (v___y_1002_ == 0)
{
v___y_987_ = v___y_995_;
v___y_988_ = v___y_1000_;
v___y_989_ = v___y_1001_;
v___y_990_ = v___y_998_;
v___y_991_ = v___y_999_;
v___y_992_ = v___y_996_;
v___y_993_ = v___y_997_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1003_; 
lean_dec(v___y_1001_);
lean_del_object(v___x_871_);
lean_dec(v_r_812_);
v___x_1003_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_915_, v_k_810_);
if (lean_obj_tag(v___x_1003_) == 1)
{
lean_object* v_toSignature_1004_; lean_object* v_val_1005_; lean_object* v_name_1006_; lean_object* v___x_1007_; lean_object* v_moduleNames_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_toSignature_1004_ = lean_ctor_get(v_origDecl_799_, 0);
lean_inc_ref(v_toSignature_1004_);
lean_dec_ref(v_origDecl_799_);
v_val_1005_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___x_1003_, 1);
v_name_1006_ = lean_ctor_get(v_toSignature_1004_, 0);
lean_inc(v_name_1006_);
lean_dec_ref(v_toSignature_1004_);
v___x_1007_ = l_Lean_Environment_header(v_env_915_);
lean_dec_ref(v_env_915_);
v_moduleNames_1008_ = lean_ctor_get(v___x_1007_, 4);
lean_inc_ref(v_moduleNames_1008_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = l_Lean_MessageData_ofConstName(v_name_1006_, v___x_873_);
v___x_1010_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
v___x_1012_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_MessageData_ofConstName(v_k_810_, v___x_873_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_array_get(v___x_866_, v_moduleNames_1008_, v_val_1005_);
lean_dec(v_val_1005_);
lean_dec_ref(v_moduleNames_1008_);
v___x_1019_ = l_Lean_MessageData_ofName(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1017_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1022_, v___y_998_, v___y_999_, v___y_996_, v___y_997_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_toSignature_1032_; lean_object* v_name_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v___x_1003_);
lean_dec_ref(v_env_915_);
v_toSignature_1032_ = lean_ctor_get(v_origDecl_799_, 0);
lean_inc_ref(v_toSignature_1032_);
lean_dec_ref(v_origDecl_799_);
v_name_1033_ = lean_ctor_get(v_toSignature_1032_, 0);
lean_inc(v_name_1033_);
lean_dec_ref(v_toSignature_1032_);
v___x_1034_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_1035_ = l_Lean_MessageData_ofConstName(v_name_1033_, v___x_873_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_MessageData_ofConstName(v_k_810_, v___x_873_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1042_, v___y_998_, v___y_999_, v___y_996_, v___y_997_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
v___jp_1052_:
{
if (v___y_1060_ == 0)
{
v___y_995_ = v___y_1053_;
v___y_996_ = v___y_1054_;
v___y_997_ = v___y_1056_;
v___y_998_ = v___y_1055_;
v___y_999_ = v___y_1057_;
v___y_1000_ = v___y_1058_;
v___y_1001_ = v___y_1059_;
v___y_1002_ = v___x_873_;
goto v___jp_994_;
}
else
{
v___y_995_ = v___y_1053_;
v___y_996_ = v___y_1054_;
v___y_997_ = v___y_1056_;
v___y_998_ = v___y_1055_;
v___y_999_ = v___y_1057_;
v___y_1000_ = v___y_1058_;
v___y_1001_ = v___y_1059_;
v___y_1002_ = v_isMeta_800_;
goto v___jp_994_;
}
}
v___jp_1061_:
{
uint8_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 0;
v___x_1070_ = l_Lean_instBEqIRPhases_beq(v___y_1062_, v___x_1069_);
v___y_1053_ = v___y_1062_;
v___y_1054_ = v___y_1063_;
v___y_1055_ = v___y_1065_;
v___y_1056_ = v___y_1064_;
v___y_1057_ = v___y_1066_;
v___y_1058_ = v___y_1067_;
v___y_1059_ = v___y_1068_;
v___y_1060_ = v___x_1070_;
goto v___jp_1052_;
}
v___jp_1071_:
{
uint8_t v___x_1078_; 
lean_inc(v_k_810_);
lean_inc_ref(v_env_915_);
v___x_1078_ = l_Lean_getIRPhases(v_env_915_, v_k_810_);
if (v___y_1077_ == 0)
{
v___y_1062_ = v___x_1078_;
v___y_1063_ = v___y_1072_;
v___y_1064_ = v___y_1074_;
v___y_1065_ = v___y_1073_;
v___y_1066_ = v___y_1075_;
v___y_1067_ = v___y_1077_;
v___y_1068_ = v___y_1076_;
goto v___jp_1061_;
}
else
{
if (v___x_873_ == 0)
{
v___y_1053_ = v___x_1078_;
v___y_1054_ = v___y_1072_;
v___y_1055_ = v___y_1073_;
v___y_1056_ = v___y_1074_;
v___y_1057_ = v___y_1075_;
v___y_1058_ = v___y_1077_;
v___y_1059_ = v___y_1076_;
v___y_1060_ = v___x_873_;
goto v___jp_1052_;
}
else
{
v___y_1062_ = v___x_1078_;
v___y_1063_ = v___y_1072_;
v___y_1064_ = v___y_1074_;
v___y_1065_ = v___y_1073_;
v___y_1066_ = v___y_1075_;
v___y_1067_ = v___y_1077_;
v___y_1068_ = v___y_1076_;
goto v___jp_1061_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1083_);
v___x_1086_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_1087_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1085_, v___x_1086_);
lean_dec_ref(v___x_1085_);
if (v___x_1087_ == 0)
{
v___y_1072_ = v___y_1083_;
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___y_1084_;
v___y_1075_ = v___y_1082_;
v___y_1076_ = v___y_1080_;
v___y_1077_ = v___x_873_;
goto v___jp_1071_;
}
else
{
uint8_t v___x_1088_; 
v___x_1088_ = l_Lean_Environment_isImportedConst(v_env_915_, v_k_810_);
if (v___x_1088_ == 0)
{
v___y_1072_ = v___y_1083_;
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___y_1084_;
v___y_1075_ = v___y_1082_;
v___y_1076_ = v___y_1080_;
v___y_1077_ = v___x_1087_;
goto v___jp_1071_;
}
else
{
v___y_1072_ = v___y_1083_;
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___y_1084_;
v___y_1075_ = v___y_1082_;
v___y_1076_ = v___y_1080_;
v___y_1077_ = v___x_873_;
goto v___jp_1071_;
}
}
}
v___jp_1089_:
{
lean_object* v_toSignature_1093_; lean_object* v_name_1094_; lean_object* v_moduleNames_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_toSignature_1093_ = lean_ctor_get(v_origDecl_799_, 0);
lean_inc_ref(v_toSignature_1093_);
lean_dec_ref(v_origDecl_799_);
v_name_1094_ = lean_ctor_get(v_toSignature_1093_, 0);
lean_inc(v_name_1094_);
lean_dec_ref(v_toSignature_1093_);
v_moduleNames_1095_ = lean_ctor_get(v___y_1092_, 4);
lean_inc_ref(v_moduleNames_1095_);
lean_dec_ref(v___y_1092_);
v___x_1096_ = l_Lean_MessageData_ofConstName(v_name_1094_, v___y_1090_);
v___x_1097_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1096_);
v___x_1099_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_MessageData_ofConstName(v_k_810_, v___y_1090_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_array_get(v___x_866_, v_moduleNames_1095_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v_moduleNames_1095_);
v___x_1106_ = l_Lean_MessageData_ofName(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1109_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
v___jp_1119_:
{
if (v___y_1123_ == 0)
{
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
v___y_1080_ = v___x_913_;
v___y_1081_ = v___y_805_;
v___y_1082_ = v___y_806_;
v___y_1083_ = v___y_807_;
v___y_1084_ = v___y_808_;
goto v___jp_1079_;
}
else
{
lean_dec_ref(v_env_915_);
lean_dec(v___x_913_);
lean_del_object(v___x_871_);
lean_dec(v_r_812_);
v___y_1090_ = v___y_1120_;
v___y_1091_ = v___y_1121_;
v___y_1092_ = v___y_1122_;
goto v___jp_1089_;
}
}
v___jp_1124_:
{
if (v___y_1127_ == 0)
{
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
v___y_1080_ = v___x_913_;
v___y_1081_ = v___y_805_;
v___y_1082_ = v___y_806_;
v___y_1083_ = v___y_807_;
v___y_1084_ = v___y_808_;
goto v___jp_1079_;
}
else
{
lean_object* v_toSignature_1128_; lean_object* v_name_1129_; lean_object* v_moduleNames_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_env_915_);
lean_dec(v___x_913_);
lean_del_object(v___x_871_);
lean_dec(v_r_812_);
v_toSignature_1128_ = lean_ctor_get(v_origDecl_799_, 0);
lean_inc_ref(v_toSignature_1128_);
lean_dec_ref(v_origDecl_799_);
v_name_1129_ = lean_ctor_get(v_toSignature_1128_, 0);
lean_inc(v_name_1129_);
lean_dec_ref(v_toSignature_1128_);
v_moduleNames_1130_ = lean_ctor_get(v___y_1125_, 4);
lean_inc_ref(v_moduleNames_1130_);
lean_dec_ref(v___y_1125_);
v___x_1131_ = l_Lean_MessageData_ofConstName(v_name_1129_, v___x_873_);
v___x_1132_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1131_);
v___x_1134_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_MessageData_ofConstName(v_k_810_, v___x_873_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_array_get(v___x_866_, v_moduleNames_1130_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v_moduleNames_1130_);
v___x_1141_ = l_Lean_MessageData_ofName(v___x_1140_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1144_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
v___jp_1154_:
{
if (v___y_1155_ == 0)
{
v___y_1080_ = v___x_913_;
v___y_1081_ = v___y_805_;
v___y_1082_ = v___y_806_;
v___y_1083_ = v___y_807_;
v___y_1084_ = v___y_808_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_915_, v_k_810_);
if (lean_obj_tag(v___x_1156_) == 1)
{
lean_object* v_val_1157_; uint8_t v___x_1158_; 
v_val_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v___x_1156_, 1);
lean_inc(v_k_810_);
lean_inc_ref(v_env_915_);
v___x_1158_ = l_Lean_isMarkedMeta(v_env_915_, v_k_810_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v_modules_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1159_ = l_Lean_Environment_header(v_env_915_);
v_modules_1160_ = lean_ctor_get(v___x_1159_, 3);
v___x_1161_ = lean_array_get_size(v_modules_1160_);
v___x_1162_ = lean_nat_dec_lt(v_val_1157_, v___x_1161_);
if (v___x_1162_ == 0)
{
v___y_1120_ = v___x_1158_;
v___y_1121_ = v_val_1157_;
v___y_1122_ = v___x_1159_;
v___y_1123_ = v___x_1158_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1163_; lean_object* v_toImport_1164_; uint8_t v_isExported_1165_; 
v___x_1163_ = lean_array_fget_borrowed(v_modules_1160_, v_val_1157_);
v_toImport_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isExported_1165_ = lean_ctor_get_uint8(v_toImport_1164_, sizeof(void*)*1 + 1);
if (v_isExported_1165_ == 0)
{
lean_dec_ref(v_env_915_);
lean_dec(v___x_913_);
lean_del_object(v___x_871_);
lean_dec(v_r_812_);
v___y_1090_ = v___x_1158_;
v___y_1091_ = v_val_1157_;
v___y_1092_ = v___x_1159_;
goto v___jp_1089_;
}
else
{
v___y_1120_ = v___x_1158_;
v___y_1121_ = v_val_1157_;
v___y_1122_ = v___x_1159_;
v___y_1123_ = v___x_1158_;
goto v___jp_1119_;
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v_modules_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = l_Lean_Environment_header(v_env_915_);
v_modules_1167_ = lean_ctor_get(v___x_1166_, 3);
v___x_1168_ = lean_array_get_size(v_modules_1167_);
v___x_1169_ = lean_nat_dec_lt(v_val_1157_, v___x_1168_);
if (v___x_1169_ == 0)
{
v___y_1125_ = v___x_1166_;
v___y_1126_ = v_val_1157_;
v___y_1127_ = v___x_873_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1170_; lean_object* v_toImport_1171_; uint8_t v_isExported_1172_; 
v___x_1170_ = lean_array_fget_borrowed(v_modules_1167_, v_val_1157_);
v_toImport_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isExported_1172_ = lean_ctor_get_uint8(v_toImport_1171_, sizeof(void*)*1 + 1);
if (v_isExported_1172_ == 0)
{
v___y_1125_ = v___x_1166_;
v___y_1126_ = v_val_1157_;
v___y_1127_ = v___x_1158_;
goto v___jp_1124_;
}
else
{
v___y_1125_ = v___x_1166_;
v___y_1126_ = v_val_1157_;
v___y_1127_ = v___x_873_;
goto v___jp_1124_;
}
}
}
}
else
{
lean_dec(v___x_1156_);
v___y_1080_ = v___x_913_;
v___y_1081_ = v___y_805_;
v___y_1082_ = v___y_806_;
v___y_1083_ = v___y_807_;
v___y_1084_ = v___y_808_;
goto v___jp_1079_;
}
}
}
}
else
{
lean_del_object(v___x_871_);
lean_dec(v_k_810_);
v_init_802_ = v___x_813_;
v_x_803_ = v_r_812_;
v___y_804_ = v_snd_869_;
goto _start;
}
v___jp_874_:
{
uint8_t v___x_881_; uint8_t v___x_882_; 
v___x_881_ = 2;
v___x_882_ = l_Lean_instBEqIRPhases_beq(v___y_875_, v___x_881_);
if (v___x_882_ == 0)
{
if (v_isPublic_801_ == 0)
{
v___y_859_ = v___y_880_;
v___y_860_ = v___y_876_;
v___y_861_ = v___y_877_;
v___y_862_ = v___y_879_;
v___y_863_ = v___y_878_;
v___y_864_ = v___x_873_;
goto v___jp_858_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = l_Lean_isPrivateName(v_k_810_);
v___y_859_ = v___y_880_;
v___y_860_ = v___y_876_;
v___y_861_ = v___y_877_;
v___y_862_ = v___y_879_;
v___y_863_ = v___y_878_;
v___y_864_ = v___x_883_;
goto v___jp_858_;
}
}
else
{
v___y_815_ = v___y_880_;
v___y_816_ = v___y_876_;
v___y_817_ = v___y_877_;
v___y_818_ = v___y_879_;
v___y_819_ = v___y_878_;
goto v___jp_814_;
}
}
v___jp_884_:
{
lean_object* v_toSignature_891_; lean_object* v_name_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
lean_dec(v___y_886_);
v_toSignature_891_ = lean_ctor_get(v_origDecl_799_, 0);
lean_inc_ref(v_toSignature_891_);
lean_dec_ref(v_origDecl_799_);
v_name_892_ = lean_ctor_get(v_toSignature_891_, 0);
lean_inc(v_name_892_);
lean_dec_ref(v_toSignature_891_);
v___x_893_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_894_ = l_Lean_MessageData_ofConstName(v_name_892_, v___x_873_);
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 7);
lean_ctor_set(v___x_871_, 1, v___x_894_);
lean_ctor_set(v___x_871_, 0, v___x_893_);
v___x_896_ = v___x_871_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_912_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v___x_897_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_MessageData_ofConstName(v_k_810_, v___x_873_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_902_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
else
{
lean_dec(v_r_812_);
lean_dec(v_k_810_);
lean_dec_ref(v_origDecl_799_);
return v___x_867_;
}
v___jp_814_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = lean_unbox(v_a_821_);
v___x_823_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_810_, v___x_822_, v___y_815_);
lean_dec(v_k_810_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
if (lean_obj_tag(v_a_824_) == 1)
{
lean_object* v_val_825_; uint8_t v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_val_825_ = lean_ctor_get(v_a_824_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v_a_824_, 1);
v___x_826_ = lean_unbox(v_a_821_);
lean_dec(v_a_821_);
v___x_827_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_826_);
v___x_828_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_827_, v_val_825_, v_pu_798_);
lean_dec(v_val_825_);
lean_inc_ref(v_origDecl_799_);
v___x_829_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_798_, v_origDecl_799_, v_isMeta_800_, v_isPublic_801_, v___x_828_, v___y_816_, v___y_817_, v___y_819_, v___y_818_, v___y_815_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v_snd_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v_snd_831_ = lean_ctor_get(v_a_830_, 1);
lean_inc(v_snd_831_);
lean_dec(v_a_830_);
v_init_802_ = v___x_813_;
v_x_803_ = v_r_812_;
v___y_804_ = v_snd_831_;
goto _start;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_r_812_);
lean_dec_ref(v_origDecl_799_);
v_a_833_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_829_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_dec(v_a_824_);
lean_dec(v_a_821_);
v_init_802_ = v___x_813_;
v_x_803_ = v_r_812_;
v___y_804_ = v___y_816_;
goto _start;
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_821_);
lean_dec(v___y_816_);
lean_dec(v_r_812_);
lean_dec_ref(v_origDecl_799_);
v_a_842_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_823_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_823_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v___y_816_);
lean_dec(v_r_812_);
lean_dec(v_k_810_);
lean_dec_ref(v_origDecl_799_);
v_a_850_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_820_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_820_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
v___jp_858_:
{
if (v___y_864_ == 0)
{
lean_dec(v_k_810_);
v_init_802_ = v___x_813_;
v_x_803_ = v_r_812_;
v___y_804_ = v___y_860_;
goto _start;
}
else
{
v___y_815_ = v___y_859_;
v___y_816_ = v___y_860_;
v___y_817_ = v___y_861_;
v___y_818_ = v___y_862_;
v___y_819_ = v___y_863_;
goto v___jp_814_;
}
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_origDecl_799_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_init_802_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___y_804_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_798_ = stack[0].m_num;
lean_object* v_origDecl_799_ = stack[1].m_obj;
uint8_t v_isMeta_800_ = stack[2].m_num;
uint8_t v_isPublic_801_ = stack[3].m_num;
lean_object* v_init_802_ = stack[4].m_obj;
lean_object* v_x_803_ = stack[5].m_obj;
lean_object* v___y_804_ = stack[6].m_obj;
lean_object* v___y_805_ = stack[7].m_obj;
lean_object* v___y_806_ = stack[8].m_obj;
lean_object* v___y_807_ = stack[9].m_obj;
lean_object* v___y_808_ = stack[10].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_798_, v_origDecl_799_, v_isMeta_800_, v_isPublic_801_, v_init_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
stack->m_obj
 = v_res_1179_;
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t v_pu_1180_, lean_object* v_origDecl_1181_, uint8_t v_isMeta_1182_, uint8_t v_isPublic_1183_, lean_object* v_code_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1191_ = l_Lean_NameSet_empty;
v___x_1192_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_1180_, v_code_1184_, v___x_1191_);
v___x_1193_ = lean_box(0);
v___x_1194_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_1180_, v_origDecl_1181_, v_isMeta_1182_, v_isPublic_1183_, v___x_1193_, v___x_1192_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1211_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1211_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1211_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_snd_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1209_; 
v_snd_1199_ = lean_ctor_get(v_a_1195_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_a_1195_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_a_1195_, 0);
lean_dec(v_unused_1210_);
v___x_1201_ = v_a_1195_;
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snd_1199_);
lean_dec(v_a_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1193_);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_snd_1199_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1204_);
v___x_1206_ = v___x_1197_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1194_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1194_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1180_ = stack[0].m_num;
lean_object* v_origDecl_1181_ = stack[1].m_obj;
uint8_t v_isMeta_1182_ = stack[2].m_num;
uint8_t v_isPublic_1183_ = stack[3].m_num;
lean_object* v_code_1184_ = stack[4].m_obj;
lean_object* v___y_1185_ = stack[5].m_obj;
lean_object* v___y_1186_ = stack[6].m_obj;
lean_object* v___y_1187_ = stack[7].m_obj;
lean_object* v___y_1188_ = stack[8].m_obj;
lean_object* v___y_1189_ = stack[9].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_1180_, v_origDecl_1181_, v_isMeta_1182_, v_isPublic_1183_, v_code_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object* v_pu_1221_, lean_object* v_origDecl_1222_, lean_object* v_isMeta_1223_, lean_object* v_isPublic_1224_, lean_object* v_code_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v_pu_boxed_1232_; uint8_t v_isMeta_boxed_1233_; uint8_t v_isPublic_boxed_1234_; lean_object* v_res_1235_; 
v_pu_boxed_1232_ = lean_unbox(v_pu_1221_);
v_isMeta_boxed_1233_ = lean_unbox(v_isMeta_1223_);
v_isPublic_boxed_1234_ = lean_unbox(v_isPublic_1224_);
v_res_1235_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_boxed_1232_, v_origDecl_1222_, v_isMeta_boxed_1233_, v_isPublic_boxed_1234_, v_code_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1235_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t v_pu_1236_, lean_object* v_origDecl_1237_, uint8_t v_isMeta_1238_, uint8_t v_isPublic_1239_, lean_object* v_decl_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_value_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; 
v_value_1247_ = lean_ctor_get(v_decl_1240_, 1);
lean_inc_ref(v_value_1247_);
lean_dec_ref(v_decl_1240_);
v___x_1248_ = lean_box(v_pu_1236_);
v___x_1249_ = lean_box(v_isMeta_1238_);
v___x_1250_ = lean_box(v_isPublic_1239_);
v___f_1251_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1251_, 0, v___x_1248_);
lean_closure_set(v___f_1251_, 1, v_origDecl_1237_);
lean_closure_set(v___f_1251_, 2, v___x_1249_);
lean_closure_set(v___f_1251_, 3, v___x_1250_);
v___x_1252_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_1251_, v_value_1247_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1252_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1236_ = stack[0].m_num;
lean_object* v_origDecl_1237_ = stack[1].m_obj;
uint8_t v_isMeta_1238_ = stack[2].m_num;
uint8_t v_isPublic_1239_ = stack[3].m_num;
lean_object* v_decl_1240_ = stack[4].m_obj;
lean_object* v_a_1241_ = stack[5].m_obj;
lean_object* v_a_1242_ = stack[6].m_obj;
lean_object* v_a_1243_ = stack[7].m_obj;
lean_object* v_a_1244_ = stack[8].m_obj;
lean_object* v_a_1245_ = stack[9].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1236_, v_origDecl_1237_, v_isMeta_1238_, v_isPublic_1239_, v_decl_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object* v_pu_1254_, lean_object* v_origDecl_1255_, lean_object* v_isMeta_1256_, lean_object* v_isPublic_1257_, lean_object* v_decl_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
uint8_t v_pu_boxed_1265_; uint8_t v_isMeta_boxed_1266_; uint8_t v_isPublic_boxed_1267_; lean_object* v_res_1268_; 
v_pu_boxed_1265_ = lean_unbox(v_pu_1254_);
v_isMeta_boxed_1266_ = lean_unbox(v_isMeta_1256_);
v_isPublic_boxed_1267_ = lean_unbox(v_isPublic_1257_);
v_res_1268_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_boxed_1265_, v_origDecl_1255_, v_isMeta_boxed_1266_, v_isPublic_boxed_1267_, v_decl_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object* v_pu_1269_, lean_object* v_origDecl_1270_, lean_object* v_isMeta_1271_, lean_object* v_isPublic_1272_, lean_object* v_init_1273_, lean_object* v_x_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v_pu_boxed_1281_; uint8_t v_isMeta_boxed_1282_; uint8_t v_isPublic_boxed_1283_; lean_object* v_res_1284_; 
v_pu_boxed_1281_ = lean_unbox(v_pu_1269_);
v_isMeta_boxed_1282_ = lean_unbox(v_isMeta_1271_);
v_isPublic_boxed_1283_ = lean_unbox(v_isPublic_1272_);
v_res_1284_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_1281_, v_origDecl_1270_, v_isMeta_boxed_1282_, v_isPublic_boxed_1283_, v_init_1273_, v_x_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1284_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object* v_opt_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1286_);
v___x_1289_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1288_, v_opt_1285_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = lean_box(v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1285_ = stack[0].m_obj;
lean_object* v___y_1286_ = stack[1].m_obj;
lean_object* v_res_1292_;
v_res_1292_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1285_, v___y_1286_);
stack->m_obj
 = v_res_1292_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1293_, v___y_1294_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_opt_1293_);
return v_res_1296_;
}
}
lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1297_, lean_object* v_origDecl_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v_env_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1364_; 
v___x_1304_ = lean_st_ref_get(v_a_1302_);
v_env_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc_ref(v_env_1305_);
lean_dec(v___x_1304_);
v___x_1306_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1307_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1306_, v_a_1301_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1364_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1364_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1363_; 
v___x_1312_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1313_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1312_, v_a_1301_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1363_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1363_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1323_; uint8_t v_isModule_1324_; 
v___x_1323_ = l_Lean_Environment_header(v_env_1305_);
lean_dec_ref(v_env_1305_);
v_isModule_1324_ = lean_ctor_get_uint8(v___x_1323_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1323_);
if (v_isModule_1324_ == 0)
{
lean_dec(v_a_1314_);
lean_del_object(v___x_1310_);
lean_dec(v_a_1308_);
lean_dec_ref(v_origDecl_1298_);
goto v___jp_1318_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_unbox(v_a_1308_);
lean_dec(v_a_1308_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_unbox(v_a_1314_);
if (v___x_1326_ == 0)
{
lean_dec(v_a_1314_);
lean_del_object(v___x_1310_);
lean_dec_ref(v_origDecl_1298_);
goto v___jp_1318_;
}
else
{
lean_object* v___x_1327_; lean_object* v_toSignature_1328_; lean_object* v_env_1329_; lean_object* v_name_1330_; uint8_t v___x_1331_; uint8_t v___y_1333_; uint8_t v___x_1355_; uint8_t v___x_1356_; 
lean_del_object(v___x_1316_);
v___x_1327_ = lean_st_ref_get(v_a_1302_);
v_toSignature_1328_ = lean_ctor_get(v_origDecl_1298_, 0);
v_env_1329_ = lean_ctor_get(v___x_1327_, 0);
lean_inc_ref(v_env_1329_);
lean_dec(v___x_1327_);
v_name_1330_ = lean_ctor_get(v_toSignature_1328_, 0);
lean_inc(v_name_1330_);
v___x_1331_ = l_Lean_getIRPhases(v_env_1329_, v_name_1330_);
v___x_1355_ = 2;
v___x_1356_ = l_Lean_instBEqIRPhases_beq(v___x_1331_, v___x_1355_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; 
lean_del_object(v___x_1310_);
v___x_1357_ = l_Lean_isPrivateName(v_name_1330_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
v___y_1333_ = v___x_1358_;
goto v___jp_1332_;
}
else
{
lean_dec(v_a_1314_);
v___y_1333_ = v___x_1356_;
goto v___jp_1332_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_dec(v_a_1314_);
lean_dec_ref(v_origDecl_1298_);
v___x_1359_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1359_);
v___x_1361_ = v___x_1310_;
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
v___jp_1332_:
{
uint8_t v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = 1;
v___x_1335_ = l_Lean_instBEqIRPhases_beq(v___x_1331_, v___x_1334_);
v___x_1336_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1298_);
v___x_1337_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1297_, v_origDecl_1298_, v___x_1335_, v___y_1333_, v_origDecl_1298_, v___x_1336_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1346_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_fst_1342_; lean_object* v___x_1344_; 
v_fst_1342_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_fst_1342_);
lean_dec(v_a_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_fst_1342_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_fst_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1347_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1314_);
lean_del_object(v___x_1310_);
lean_dec_ref(v_origDecl_1298_);
goto v___jp_1318_;
}
}
v___jp_1318_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_box(0);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1319_);
v___x_1321_ = v___x_1316_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_checkMeta_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1297_ = stack[0].m_num;
lean_object* v_origDecl_1298_ = stack[1].m_obj;
lean_object* v_a_1299_ = stack[2].m_obj;
lean_object* v_a_1300_ = stack[3].m_obj;
lean_object* v_a_1301_ = stack[4].m_obj;
lean_object* v_a_1302_ = stack[5].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_1297_, v_origDecl_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1366_, lean_object* v_origDecl_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
uint8_t v_pu_boxed_1373_; lean_object* v_res_1374_; 
v_pu_boxed_1373_ = lean_unbox(v_pu_1366_);
v_res_1374_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1373_, v_origDecl_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
return v_res_1374_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1375_, v___y_1378_);
return v___x_1381_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1375_ = stack[0].m_obj;
lean_object* v___y_1376_ = stack[1].m_obj;
lean_object* v___y_1377_ = stack[2].m_obj;
lean_object* v___y_1378_ = stack[3].m_obj;
lean_object* v___y_1379_ = stack[4].m_obj;
lean_object* v_res_1382_;
v_res_1382_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v_opt_1383_);
return v_res_1389_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(uint8_t v_isExporting_1390_, lean_object* v___x_1391_, lean_object* v_x_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v_env_1400_; lean_object* v_nextMacroScope_1401_; lean_object* v_ngen_1402_; lean_object* v_auxDeclNGen_1403_; lean_object* v_traceState_1404_; lean_object* v_recordedDeps_1405_; lean_object* v_messages_1406_; lean_object* v_infoState_1407_; lean_object* v_snapshotTasks_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1420_; 
v___x_1399_ = lean_st_ref_take(v___y_1397_);
v_env_1400_ = lean_ctor_get(v___x_1399_, 0);
v_nextMacroScope_1401_ = lean_ctor_get(v___x_1399_, 1);
v_ngen_1402_ = lean_ctor_get(v___x_1399_, 2);
v_auxDeclNGen_1403_ = lean_ctor_get(v___x_1399_, 3);
v_traceState_1404_ = lean_ctor_get(v___x_1399_, 4);
v_recordedDeps_1405_ = lean_ctor_get(v___x_1399_, 6);
v_messages_1406_ = lean_ctor_get(v___x_1399_, 7);
v_infoState_1407_ = lean_ctor_get(v___x_1399_, 8);
v_snapshotTasks_1408_ = lean_ctor_get(v___x_1399_, 9);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1399_, 5);
lean_dec(v_unused_1421_);
v___x_1410_ = v___x_1399_;
v_isShared_1411_ = v_isSharedCheck_1420_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snapshotTasks_1408_);
lean_inc(v_infoState_1407_);
lean_inc(v_messages_1406_);
lean_inc(v_recordedDeps_1405_);
lean_inc(v_traceState_1404_);
lean_inc(v_auxDeclNGen_1403_);
lean_inc(v_ngen_1402_);
lean_inc(v_nextMacroScope_1401_);
lean_inc(v_env_1400_);
lean_dec(v___x_1399_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1420_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = l_Lean_Environment_setExporting(v_env_1400_, v_isExporting_1390_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 5, v___x_1391_);
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_nextMacroScope_1401_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_ngen_1402_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_auxDeclNGen_1403_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_traceState_1404_);
lean_ctor_set(v_reuseFailAlloc_1419_, 5, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1419_, 6, v_recordedDeps_1405_);
lean_ctor_set(v_reuseFailAlloc_1419_, 7, v_messages_1406_);
lean_ctor_set(v_reuseFailAlloc_1419_, 8, v_infoState_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 9, v_snapshotTasks_1408_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_st_ref_put(v___y_1397_, v___x_1415_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1412_);
lean_ctor_set(v___x_1417_, 1, v___y_1393_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_isExporting_1390_ = stack[0].m_num;
lean_object* v___x_1391_ = stack[1].m_obj;
lean_object* v_x_1392_ = stack[2].m_obj;
lean_object* v___y_1393_ = stack[3].m_obj;
lean_object* v___y_1394_ = stack[4].m_obj;
lean_object* v___y_1395_ = stack[5].m_obj;
lean_object* v___y_1396_ = stack[6].m_obj;
lean_object* v___y_1397_ = stack[7].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_1390_, v___x_1391_, v_x_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(lean_object* v_isExporting_1423_, lean_object* v___x_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_isExporting_boxed_1432_; lean_object* v_res_1433_; 
v_isExporting_boxed_1432_ = lean_unbox(v_isExporting_1423_);
v_res_1433_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_boxed_1432_, v___x_1424_, v_x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v_x_1425_);
return v_res_1433_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(lean_object* v___f_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v_a_x3f_1440_){
_start:
{
if (lean_obj_tag(v_a_x3f_1440_) == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_box(0);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1443_ = lean_apply_7(v___f_1434_, v___x_1442_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, lean_box(0));
return v___x_1443_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v___y_1435_);
v_val_1444_ = lean_ctor_get(v_a_x3f_1440_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_a_x3f_1440_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1446_ = v_a_x3f_1440_;
v_isShared_1447_ = v_isSharedCheck_1454_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_val_1444_);
lean_dec(v_a_x3f_1440_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1454_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___x_1451_; 
v_fst_1448_ = lean_ctor_get(v_val_1444_, 0);
lean_inc(v_fst_1448_);
v_snd_1449_ = lean_ctor_get(v_val_1444_, 1);
lean_inc(v_snd_1449_);
lean_dec(v_val_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v_fst_1448_);
v___x_1451_ = v___x_1446_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_fst_1448_);
v___x_1451_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1452_ = lean_apply_7(v___f_1434_, v___x_1451_, v_snd_1449_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, lean_box(0));
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1434_ = stack[0].m_obj;
lean_object* v___y_1435_ = stack[1].m_obj;
lean_object* v___y_1436_ = stack[2].m_obj;
lean_object* v___y_1437_ = stack[3].m_obj;
lean_object* v___y_1438_ = stack[4].m_obj;
lean_object* v___y_1439_ = stack[5].m_obj;
lean_object* v_a_x3f_1440_ = stack[6].m_obj;
lean_object* v_res_1455_;
v_res_1455_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v_a_x3f_1440_);
stack->m_obj
 = v_res_1455_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(lean_object* v___f_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v_a_x3f_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v_a_x3f_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
return v_res_1464_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object* v_x_1465_, uint8_t v_isExporting_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_env_1474_; lean_object* v___x_1475_; uint8_t v_isModule_1476_; 
v___x_1473_ = lean_st_ref_get(v___y_1471_);
v_env_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_ref(v_env_1474_);
lean_dec(v___x_1473_);
v___x_1475_ = l_Lean_Environment_header(v_env_1474_);
v_isModule_1476_ = lean_ctor_get_uint8(v___x_1475_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1475_);
if (v_isModule_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v_env_1474_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
v___x_1477_ = lean_apply_6(v_x_1465_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
return v___x_1477_;
}
else
{
uint8_t v_isExporting_1478_; 
v_isExporting_1478_ = lean_ctor_get_uint8(v_env_1474_, sizeof(void*)*13);
lean_dec_ref(v_env_1474_);
if (v_isExporting_1466_ == 0)
{
if (v_isExporting_1478_ == 0)
{
lean_object* v___x_1558_; 
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
v___x_1558_ = lean_apply_6(v_x_1465_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
return v___x_1558_;
}
else
{
goto v___jp_1479_;
}
}
else
{
if (v_isExporting_1478_ == 0)
{
goto v___jp_1479_;
}
else
{
lean_object* v___x_1559_; 
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
v___x_1559_ = lean_apply_6(v_x_1465_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
return v___x_1559_;
}
}
v___jp_1479_:
{
lean_object* v___x_1480_; lean_object* v_env_1481_; lean_object* v_nextMacroScope_1482_; lean_object* v_ngen_1483_; lean_object* v_auxDeclNGen_1484_; lean_object* v_traceState_1485_; lean_object* v_recordedDeps_1486_; lean_object* v_messages_1487_; lean_object* v_infoState_1488_; lean_object* v_snapshotTasks_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1556_; 
v___x_1480_ = lean_st_ref_take(v___y_1471_);
v_env_1481_ = lean_ctor_get(v___x_1480_, 0);
v_nextMacroScope_1482_ = lean_ctor_get(v___x_1480_, 1);
v_ngen_1483_ = lean_ctor_get(v___x_1480_, 2);
v_auxDeclNGen_1484_ = lean_ctor_get(v___x_1480_, 3);
v_traceState_1485_ = lean_ctor_get(v___x_1480_, 4);
v_recordedDeps_1486_ = lean_ctor_get(v___x_1480_, 6);
v_messages_1487_ = lean_ctor_get(v___x_1480_, 7);
v_infoState_1488_ = lean_ctor_get(v___x_1480_, 8);
v_snapshotTasks_1489_ = lean_ctor_get(v___x_1480_, 9);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v___x_1480_, 5);
lean_dec(v_unused_1557_);
v___x_1491_ = v___x_1480_;
v_isShared_1492_ = v_isSharedCheck_1556_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snapshotTasks_1489_);
lean_inc(v_infoState_1488_);
lean_inc(v_messages_1487_);
lean_inc(v_recordedDeps_1486_);
lean_inc(v_traceState_1485_);
lean_inc(v_auxDeclNGen_1484_);
lean_inc(v_ngen_1483_);
lean_inc(v_nextMacroScope_1482_);
lean_inc(v_env_1481_);
lean_dec(v___x_1480_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1556_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1498_; 
v___x_1493_ = l_Lean_Environment_setExporting(v_env_1481_, v_isExporting_1466_);
v___x_1494_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1495_ = lean_box(v_isExporting_1478_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1496_, 0, v___x_1495_);
lean_closure_set(v___f_1496_, 1, v___x_1494_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 5, v___x_1494_);
lean_ctor_set(v___x_1491_, 0, v___x_1493_);
v___x_1498_ = v___x_1491_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_nextMacroScope_1482_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_ngen_1483_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_auxDeclNGen_1484_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_traceState_1485_);
lean_ctor_set(v_reuseFailAlloc_1555_, 5, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1555_, 6, v_recordedDeps_1486_);
lean_ctor_set(v_reuseFailAlloc_1555_, 7, v_messages_1487_);
lean_ctor_set(v_reuseFailAlloc_1555_, 8, v_infoState_1488_);
lean_ctor_set(v_reuseFailAlloc_1555_, 9, v_snapshotTasks_1489_);
v___x_1498_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v_r_1500_; 
v___x_1499_ = lean_st_ref_put(v___y_1471_, v___x_1498_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
v_r_1500_ = lean_apply_6(v_x_1465_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
if (lean_obj_tag(v_r_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1535_; 
v_a_1501_ = lean_ctor_get(v_r_1500_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_r_1500_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1503_ = v_r_1500_;
v_isShared_1504_ = v_isSharedCheck_1535_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v_r_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1535_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
lean_inc(v_a_1501_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 1);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1496_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1525_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1525_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1525_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_fst_1512_; lean_object* v_snd_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1523_; 
v_fst_1512_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_fst_1512_);
lean_dec(v_a_1501_);
v_snd_1513_ = lean_ctor_get(v_a_1508_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_a_1508_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_a_1508_, 0);
lean_dec(v_unused_1524_);
v___x_1515_ = v_a_1508_;
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snd_1513_);
lean_dec(v_a_1508_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_fst_1512_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_fst_1512_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_snd_1513_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1518_);
v___x_1520_ = v___x_1510_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1501_);
v_a_1526_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1507_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1507_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1536_ = lean_ctor_get(v_r_1500_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v_r_1500_, 1);
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1496_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___x_1537_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v_a_1536_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1536_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1536_);
v_a_1547_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1538_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1538_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1465_ = stack[0].m_obj;
uint8_t v_isExporting_1466_ = stack[1].m_num;
lean_object* v___y_1467_ = stack[2].m_obj;
lean_object* v___y_1468_ = stack[3].m_obj;
lean_object* v___y_1469_ = stack[4].m_obj;
lean_object* v___y_1470_ = stack[5].m_obj;
lean_object* v___y_1471_ = stack[6].m_obj;
lean_object* v_res_1560_;
v_res_1560_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1465_, v_isExporting_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
stack->m_obj
 = v_res_1560_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_x_1561_, lean_object* v_isExporting_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_isExporting_boxed_1569_; lean_object* v_res_1570_; 
v_isExporting_boxed_1569_ = lean_unbox(v_isExporting_1562_);
v_res_1570_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1561_, v_isExporting_boxed_1569_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1570_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_00_u03b1_1571_, lean_object* v_x_1572_, uint8_t v_isExporting_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1572_, v_isExporting_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1572_ = stack[1].m_obj;
uint8_t v_isExporting_1573_ = stack[2].m_num;
lean_object* v___y_1574_ = stack[3].m_obj;
lean_object* v___y_1575_ = stack[4].m_obj;
lean_object* v___y_1576_ = stack[5].m_obj;
lean_object* v___y_1577_ = stack[6].m_obj;
lean_object* v___y_1578_ = stack[7].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_box(0), v_x_1572_, v_isExporting_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_x_1583_, lean_object* v_isExporting_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_isExporting_boxed_1591_; lean_object* v_res_1592_; 
v_isExporting_boxed_1591_ = lean_unbox(v_isExporting_1584_);
v_res_1592_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_1582_, v_x_1583_, v_isExporting_boxed_1591_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1592_;
}
}
lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(lean_object* v_opt_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1597_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1595_);
v___x_1598_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v___x_1597_, v_opt_1593_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = lean_box(v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___y_1594_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1593_ = stack[0].m_obj;
lean_object* v___y_1594_ = stack[1].m_obj;
lean_object* v___y_1595_ = stack[2].m_obj;
lean_object* v_res_1602_;
v_res_1602_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_1593_, v___y_1594_, v___y_1595_);
stack->m_obj
 = v_res_1602_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(lean_object* v_opt_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_1603_, v___y_1604_, v___y_1605_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_opt_1603_);
return v_res_1607_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(lean_object* v_cls_1608_, lean_object* v_msg_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_ref_1616_; lean_object* v___x_1617_; lean_object* v_env_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_ref_1616_ = lean_ctor_get(v___y_1613_, 2);
v___x_1617_ = lean_st_ref_get(v___y_1614_);
v_env_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_env_1618_);
lean_dec(v___x_1617_);
v___x_1619_ = lean_st_ref_get(v___y_1612_);
v___x_1620_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1611_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1681_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1681_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1681_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_lctx_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1679_; 
v_lctx_1625_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1619_, 1);
lean_dec(v_unused_1680_);
v___x_1627_ = v___x_1619_;
v_isShared_1628_ = v_isSharedCheck_1679_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_lctx_1625_);
lean_dec(v___x_1619_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1679_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1629_ = lean_unbox(v_a_1621_);
lean_dec(v_a_1621_);
v___x_1630_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1625_, v___x_1629_);
lean_dec_ref(v_lctx_1625_);
v___x_1631_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1613_);
v___x_1632_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_1633_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1633_, 0, v_env_1618_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
lean_ctor_set(v___x_1633_, 2, v___x_1630_);
lean_ctor_set(v___x_1633_, 3, v___x_1631_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 3);
lean_ctor_set(v___x_1627_, 1, v_msg_1609_);
lean_ctor_set(v___x_1627_, 0, v___x_1633_);
v___x_1635_ = v___x_1627_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_msg_1609_);
v___x_1635_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v_traceState_1637_; lean_object* v_env_1638_; lean_object* v_nextMacroScope_1639_; lean_object* v_ngen_1640_; lean_object* v_auxDeclNGen_1641_; lean_object* v_cache_1642_; lean_object* v_recordedDeps_1643_; lean_object* v_messages_1644_; lean_object* v_infoState_1645_; lean_object* v_snapshotTasks_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1677_; 
v___x_1636_ = lean_st_ref_take(v___y_1614_);
v_traceState_1637_ = lean_ctor_get(v___x_1636_, 4);
v_env_1638_ = lean_ctor_get(v___x_1636_, 0);
v_nextMacroScope_1639_ = lean_ctor_get(v___x_1636_, 1);
v_ngen_1640_ = lean_ctor_get(v___x_1636_, 2);
v_auxDeclNGen_1641_ = lean_ctor_get(v___x_1636_, 3);
v_cache_1642_ = lean_ctor_get(v___x_1636_, 5);
v_recordedDeps_1643_ = lean_ctor_get(v___x_1636_, 6);
v_messages_1644_ = lean_ctor_get(v___x_1636_, 7);
v_infoState_1645_ = lean_ctor_get(v___x_1636_, 8);
v_snapshotTasks_1646_ = lean_ctor_get(v___x_1636_, 9);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1677_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snapshotTasks_1646_);
lean_inc(v_infoState_1645_);
lean_inc(v_messages_1644_);
lean_inc(v_recordedDeps_1643_);
lean_inc(v_cache_1642_);
lean_inc(v_traceState_1637_);
lean_inc(v_auxDeclNGen_1641_);
lean_inc(v_ngen_1640_);
lean_inc(v_nextMacroScope_1639_);
lean_inc(v_env_1638_);
lean_dec(v___x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1677_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint64_t v_tid_1650_; lean_object* v_traces_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1676_; 
v_tid_1650_ = lean_ctor_get_uint64(v_traceState_1637_, sizeof(void*)*1);
v_traces_1651_ = lean_ctor_get(v_traceState_1637_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_traceState_1637_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1653_ = v_traceState_1637_;
v_isShared_1654_ = v_isSharedCheck_1676_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_traces_1651_);
lean_dec(v_traceState_1637_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1676_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; double v___x_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_1658_ = 0;
v___x_1659_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1660_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1660_, 0, v_cls_1608_);
lean_ctor_set(v___x_1660_, 1, v___x_1656_);
lean_ctor_set(v___x_1660_, 2, v___x_1659_);
lean_ctor_set_float(v___x_1660_, sizeof(void*)*3, v___x_1657_);
lean_ctor_set_float(v___x_1660_, sizeof(void*)*3 + 8, v___x_1657_);
lean_ctor_set_uint8(v___x_1660_, sizeof(void*)*3 + 16, v___x_1658_);
v___x_1661_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_1662_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1635_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
lean_inc(v_ref_1616_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v_ref_1616_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_PersistentArray_push___redArg(v_traces_1651_, v___x_1663_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1664_);
v___x_1666_ = v___x_1653_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1664_);
lean_ctor_set_uint64(v_reuseFailAlloc_1675_, sizeof(void*)*1, v_tid_1650_);
v___x_1666_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v___x_1666_);
v___x_1668_ = v___x_1648_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_env_1638_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_nextMacroScope_1639_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_ngen_1640_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_auxDeclNGen_1641_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1674_, 5, v_cache_1642_);
lean_ctor_set(v_reuseFailAlloc_1674_, 6, v_recordedDeps_1643_);
lean_ctor_set(v_reuseFailAlloc_1674_, 7, v_messages_1644_);
lean_ctor_set(v_reuseFailAlloc_1674_, 8, v_infoState_1645_);
lean_ctor_set(v_reuseFailAlloc_1674_, 9, v_snapshotTasks_1646_);
v___x_1668_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1669_ = lean_st_ref_put(v___y_1614_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1655_);
lean_ctor_set(v___x_1670_, 1, v___y_1610_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1670_);
v___x_1672_ = v___x_1623_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
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
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v___x_1619_);
lean_dec_ref(v_env_1618_);
lean_dec(v___y_1610_);
lean_dec_ref(v_msg_1609_);
lean_dec(v_cls_1608_);
v_a_1682_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1620_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1620_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1608_ = stack[0].m_obj;
lean_object* v_msg_1609_ = stack[1].m_obj;
lean_object* v___y_1610_ = stack[2].m_obj;
lean_object* v___y_1611_ = stack[3].m_obj;
lean_object* v___y_1612_ = stack[4].m_obj;
lean_object* v___y_1613_ = stack[5].m_obj;
lean_object* v___y_1614_ = stack[6].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1608_, v_msg_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7___boxed(lean_object* v_cls_1691_, lean_object* v_msg_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1691_, v_msg_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___lam__0(lean_object* v___x_1700_, lean_object* v_entry_1701_, lean_object* v_s_1702_){
_start:
{
lean_object* v_addEntryFn_1703_; lean_object* v_importedEntries_1704_; lean_object* v_state_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_addEntryFn_1703_ = lean_ctor_get(v___x_1700_, 3);
lean_inc(v_addEntryFn_1703_);
lean_dec_ref(v___x_1700_);
v_importedEntries_1704_ = lean_ctor_get(v_s_1702_, 0);
v_state_1705_ = lean_ctor_get(v_s_1702_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_s_1702_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_s_1702_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_state_1705_);
lean_inc(v_importedEntries_1704_);
lean_dec(v_s_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_state_1709_; lean_object* v___x_1711_; 
v_state_1709_ = lean_apply_2(v_addEntryFn_1703_, v_state_1705_, v_entry_1701_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_state_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_importedEntries_1704_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_state_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object* v_keys_1714_, lean_object* v_i_1715_, lean_object* v_k_1716_){
_start:
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = lean_array_get_size(v_keys_1714_);
v___x_1718_ = lean_nat_dec_lt(v_i_1715_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_dec(v_i_1715_);
return v___x_1718_;
}
else
{
lean_object* v_k_x27_1719_; uint8_t v___x_1720_; 
v_k_x27_1719_ = lean_array_fget_borrowed(v_keys_1714_, v_i_1715_);
v___x_1720_ = l_Lean_instBEqExtraModUse_beq(v_k_1716_, v_k_x27_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_add(v_i_1715_, v___x_1721_);
lean_dec(v_i_1715_);
v_i_1715_ = v___x_1722_;
goto _start;
}
else
{
lean_dec(v_i_1715_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1714_ = stack[0].m_obj;
lean_object* v_i_1715_ = stack[1].m_obj;
lean_object* v_k_1716_ = stack[2].m_obj;
uint8_t v_res_1724_;
v_res_1724_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_1714_, v_i_1715_, v_k_1716_);
stack->m_num = v_res_1724_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1725_, lean_object* v_i_1726_, lean_object* v_k_1727_){
_start:
{
uint8_t v_res_1728_; lean_object* v_r_1729_; 
v_res_1728_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_1725_, v_i_1726_, v_k_1727_);
lean_dec_ref(v_k_1727_);
lean_dec_ref(v_keys_1725_);
v_r_1729_ = lean_box(v_res_1728_);
return v_r_1729_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1730_, size_t v_x_1731_, lean_object* v_x_1732_){
_start:
{
if (lean_obj_tag(v_x_1730_) == 0)
{
lean_object* v_es_1733_; lean_object* v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; lean_object* v_j_1737_; lean_object* v___x_1738_; 
v_es_1733_ = lean_ctor_get(v_x_1730_, 0);
v___x_1734_ = lean_box(2);
v___x_1735_ = ((size_t)31ULL);
v___x_1736_ = lean_usize_land(v_x_1731_, v___x_1735_);
v_j_1737_ = lean_usize_to_nat(v___x_1736_);
v___x_1738_ = lean_array_get_borrowed(v___x_1734_, v_es_1733_, v_j_1737_);
lean_dec(v_j_1737_);
switch(lean_obj_tag(v___x_1738_))
{
case 0:
{
lean_object* v_key_1739_; uint8_t v___x_1740_; 
v_key_1739_ = lean_ctor_get(v___x_1738_, 0);
v___x_1740_ = l_Lean_instBEqExtraModUse_beq(v_x_1732_, v_key_1739_);
return v___x_1740_;
}
case 1:
{
lean_object* v_node_1741_; size_t v___x_1742_; size_t v___x_1743_; 
v_node_1741_ = lean_ctor_get(v___x_1738_, 0);
v___x_1742_ = ((size_t)5ULL);
v___x_1743_ = lean_usize_shift_right(v_x_1731_, v___x_1742_);
v_x_1730_ = v_node_1741_;
v_x_1731_ = v___x_1743_;
goto _start;
}
default: 
{
uint8_t v___x_1745_; 
v___x_1745_ = 0;
return v___x_1745_;
}
}
}
else
{
lean_object* v_ks_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_ks_1746_ = lean_ctor_get(v_x_1730_, 0);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_1746_, v___x_1747_, v_x_1732_);
return v___x_1748_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1730_ = stack[0].m_obj;
size_t v_x_1731_ = stack[1].m_num;
lean_object* v_x_1732_ = stack[2].m_obj;
uint8_t v_res_1749_;
v_res_1749_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1730_, v_x_1731_, v_x_1732_);
stack->m_num = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
size_t v_x_27175__boxed_1753_; uint8_t v_res_1754_; lean_object* v_r_1755_; 
v_x_27175__boxed_1753_ = lean_unbox_usize(v_x_1751_);
lean_dec(v_x_1751_);
v_res_1754_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1750_, v_x_27175__boxed_1753_, v_x_1752_);
lean_dec_ref(v_x_1752_);
lean_dec_ref(v_x_1750_);
v_r_1755_ = lean_box(v_res_1754_);
return v_r_1755_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
uint64_t v___x_1758_; size_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = l_Lean_instHashableExtraModUse_hash(v_x_1757_);
v___x_1759_ = lean_uint64_to_usize(v___x_1758_);
v___x_1760_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1756_, v___x_1759_, v_x_1757_);
return v___x_1760_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1756_ = stack[0].m_obj;
lean_object* v_x_1757_ = stack[1].m_obj;
uint8_t v_res_1761_;
v_res_1761_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_1756_, v_x_1757_);
stack->m_num = v_res_1761_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_res_1764_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_1762_, v_x_1763_);
lean_dec_ref(v_x_1763_);
lean_dec_ref(v_x_1762_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1766_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1777_ = l_Lean_stringToMessageData(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v_cls_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_cls_1778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2));
v___x_1779_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1780_ = l_Lean_Name_append(v___x_1779_, v_cls_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object* v_mod_1791_, uint8_t v_isMeta_1792_, lean_object* v_hint_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_env_1820_; uint8_t v_isExporting_1821_; lean_object* v_entry_1822_; lean_object* v___x_1823_; lean_object* v_env_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1818_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0);
v___x_1819_ = lean_st_ref_get(v___y_1798_);
v_env_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc_ref(v_env_1820_);
lean_dec(v___x_1819_);
v_isExporting_1821_ = lean_ctor_get_uint8(v_env_1820_, sizeof(void*)*13);
lean_dec_ref(v_env_1820_);
lean_inc(v_mod_1791_);
v_entry_1822_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1822_, 0, v_mod_1791_);
lean_ctor_set_uint8(v_entry_1822_, sizeof(void*)*1, v_isExporting_1821_);
lean_ctor_set_uint8(v_entry_1822_, sizeof(void*)*1 + 1, v_isMeta_1792_);
v___x_1823_ = lean_st_ref_get(v___y_1798_);
v_env_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_ref(v_env_1824_);
lean_dec(v___x_1823_);
v___x_1825_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1826_ = lean_box(1);
v___x_1827_ = lean_box(0);
v___x_1828_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1818_, v___x_1825_, v_env_1824_, v___x_1826_, v___x_1827_);
v___x_1829_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_1828_, v_entry_1822_);
lean_dec(v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v_toCold_1830_; lean_object* v_options_1831_; lean_object* v_inheritedTraceOptions_1832_; uint8_t v_hasTrace_1833_; lean_object* v___f_1834_; uint8_t v___x_1835_; lean_object* v___y_1837_; lean_object* v___y_1838_; 
v_toCold_1830_ = lean_ctor_get(v___y_1797_, 0);
v_options_1831_ = lean_ctor_get(v_toCold_1830_, 2);
v_inheritedTraceOptions_1832_ = lean_ctor_get(v_toCold_1830_, 11);
v_hasTrace_1833_ = lean_ctor_get_uint8(v_options_1831_, sizeof(void*)*1);
v___f_1834_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_1834_, 0, v___x_1825_);
lean_closure_set(v___f_1834_, 1, v_entry_1822_);
v___x_1835_ = 1;
if (v_hasTrace_1833_ == 0)
{
lean_dec(v_hint_1793_);
lean_dec(v_mod_1791_);
v___y_1837_ = v___y_1794_;
v___y_1838_ = v___y_1798_;
goto v___jp_1836_;
}
else
{
lean_object* v_cls_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_cls_1856_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2));
v___x_1878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
v___x_1879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1832_, v_options_1831_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_dec(v_hint_1793_);
lean_dec(v_mod_1791_);
v___y_1837_ = v___y_1794_;
v___y_1838_ = v___y_1798_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1880_; lean_object* v___y_1882_; 
v___x_1880_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
if (v_isExporting_1821_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15));
v___y_1882_ = v___x_1889_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16));
v___y_1882_ = v___x_1890_;
goto v___jp_1881_;
}
v___jp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_inc_ref(v___y_1882_);
v___x_1883_ = l_Lean_stringToMessageData(v___y_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1880_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
if (v_isMeta_1792_ == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13));
v___y_1865_ = v___x_1886_;
v___y_1866_ = v___x_1887_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14));
v___y_1865_ = v___x_1886_;
v___y_1866_ = v___x_1888_;
goto v___jp_1864_;
}
}
}
v___jp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1858_);
lean_ctor_set(v___x_1860_, 1, v___y_1859_);
v___x_1861_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1856_, v___x_1860_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v_snd_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v_snd_1863_ = lean_ctor_get(v_a_1862_, 1);
lean_inc(v_snd_1863_);
lean_dec(v_a_1862_);
v___y_1837_ = v_snd_1863_;
v___y_1838_ = v___y_1798_;
goto v___jp_1836_;
}
else
{
lean_dec_ref(v___f_1834_);
return v___x_1861_;
}
}
v___jp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
lean_inc_ref(v___y_1866_);
v___x_1867_ = l_Lean_stringToMessageData(v___y_1866_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___y_1865_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_MessageData_ofName(v_mod_1791_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_Name_isAnonymous(v_hint_1793_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
v___x_1875_ = l_Lean_MessageData_ofName(v_hint_1793_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___y_1858_ = v___x_1872_;
v___y_1859_ = v___x_1876_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1877_; 
lean_dec(v_hint_1793_);
v___x_1877_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7);
v___y_1858_ = v___x_1872_;
v___y_1859_ = v___x_1877_;
goto v___jp_1857_;
}
}
}
v___jp_1836_:
{
lean_object* v___x_1839_; lean_object* v_toEnvExtension_1840_; lean_object* v_env_1841_; lean_object* v_nextMacroScope_1842_; lean_object* v_ngen_1843_; lean_object* v_auxDeclNGen_1844_; lean_object* v_traceState_1845_; lean_object* v_recordedDeps_1846_; lean_object* v_messages_1847_; lean_object* v_infoState_1848_; lean_object* v_snapshotTasks_1849_; lean_object* v_asyncMode_1850_; uint8_t v_logWrites_1851_; lean_object* v___x_1852_; 
v___x_1839_ = lean_st_ref_take(v___y_1838_);
v_toEnvExtension_1840_ = lean_ctor_get(v___x_1825_, 0);
v_env_1841_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_env_1841_);
v_nextMacroScope_1842_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_nextMacroScope_1842_);
v_ngen_1843_ = lean_ctor_get(v___x_1839_, 2);
lean_inc_ref(v_ngen_1843_);
v_auxDeclNGen_1844_ = lean_ctor_get(v___x_1839_, 3);
lean_inc_ref(v_auxDeclNGen_1844_);
v_traceState_1845_ = lean_ctor_get(v___x_1839_, 4);
lean_inc_ref(v_traceState_1845_);
v_recordedDeps_1846_ = lean_ctor_get(v___x_1839_, 6);
lean_inc_ref(v_recordedDeps_1846_);
v_messages_1847_ = lean_ctor_get(v___x_1839_, 7);
lean_inc_ref(v_messages_1847_);
v_infoState_1848_ = lean_ctor_get(v___x_1839_, 8);
lean_inc_ref(v_infoState_1848_);
v_snapshotTasks_1849_ = lean_ctor_get(v___x_1839_, 9);
lean_inc_ref(v_snapshotTasks_1849_);
lean_dec(v___x_1839_);
v_asyncMode_1850_ = lean_ctor_get(v_toEnvExtension_1840_, 2);
v_logWrites_1851_ = lean_ctor_get_uint8(v_toEnvExtension_1840_, sizeof(void*)*6);
v___x_1852_ = lean_box(0);
if (v_logWrites_1851_ == 0)
{
lean_object* v___x_1853_; 
lean_inc_ref(v_toEnvExtension_1840_);
v___x_1853_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1840_, v_env_1841_, v___f_1834_, v_asyncMode_1850_, v___x_1827_, v___x_1835_);
v___y_1801_ = v___y_1837_;
v___y_1802_ = v_snapshotTasks_1849_;
v___y_1803_ = v_traceState_1845_;
v___y_1804_ = v___y_1838_;
v___y_1805_ = v_infoState_1848_;
v___y_1806_ = v_auxDeclNGen_1844_;
v___y_1807_ = v_ngen_1843_;
v___y_1808_ = v_recordedDeps_1846_;
v___y_1809_ = v_nextMacroScope_1842_;
v___y_1810_ = v___x_1852_;
v___y_1811_ = v_messages_1847_;
v___y_1812_ = v___x_1853_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_inc_ref_n(v_toEnvExtension_1840_, 2);
v___x_1854_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1840_, v_env_1841_);
lean_dec_ref(v_env_1841_);
v___x_1855_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1840_, v___x_1854_, v___f_1834_, v_asyncMode_1850_, v___x_1827_, v___x_1835_);
v___y_1801_ = v___y_1837_;
v___y_1802_ = v_snapshotTasks_1849_;
v___y_1803_ = v_traceState_1845_;
v___y_1804_ = v___y_1838_;
v___y_1805_ = v_infoState_1848_;
v___y_1806_ = v_auxDeclNGen_1844_;
v___y_1807_ = v_ngen_1843_;
v___y_1808_ = v_recordedDeps_1846_;
v___y_1809_ = v_nextMacroScope_1842_;
v___y_1810_ = v___x_1852_;
v___y_1811_ = v_messages_1847_;
v___y_1812_ = v___x_1855_;
goto v___jp_1800_;
}
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec_ref_known(v_entry_1822_, 1);
lean_dec(v_hint_1793_);
lean_dec(v_mod_1791_);
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___y_1794_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
v___jp_1800_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1813_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1814_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1814_, 0, v___y_1812_);
lean_ctor_set(v___x_1814_, 1, v___y_1809_);
lean_ctor_set(v___x_1814_, 2, v___y_1807_);
lean_ctor_set(v___x_1814_, 3, v___y_1806_);
lean_ctor_set(v___x_1814_, 4, v___y_1803_);
lean_ctor_set(v___x_1814_, 5, v___x_1813_);
lean_ctor_set(v___x_1814_, 6, v___y_1808_);
lean_ctor_set(v___x_1814_, 7, v___y_1811_);
lean_ctor_set(v___x_1814_, 8, v___y_1805_);
lean_ctor_set(v___x_1814_, 9, v___y_1802_);
v___x_1815_ = lean_st_ref_put(v___y_1804_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1810_);
lean_ctor_set(v___x_1816_, 1, v___y_1801_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1791_ = stack[0].m_obj;
uint8_t v_isMeta_1792_ = stack[1].m_num;
lean_object* v_hint_1793_ = stack[2].m_obj;
lean_object* v___y_1794_ = stack[3].m_obj;
lean_object* v___y_1795_ = stack[4].m_obj;
lean_object* v___y_1796_ = stack[5].m_obj;
lean_object* v___y_1797_ = stack[6].m_obj;
lean_object* v___y_1798_ = stack[7].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_1791_, v_isMeta_1792_, v_hint_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object* v_mod_1895_, lean_object* v_isMeta_1896_, lean_object* v_hint_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v_isMeta_boxed_1904_; lean_object* v_res_1905_; 
v_isMeta_boxed_1904_ = lean_unbox(v_isMeta_1896_);
v_res_1905_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_1895_, v_isMeta_boxed_1904_, v_hint_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object* v_a_1906_, lean_object* v_x_1907_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_box(0);
return v___x_1908_;
}
else
{
lean_object* v_key_1909_; lean_object* v_value_1910_; lean_object* v_tail_1911_; uint8_t v___x_1912_; 
v_key_1909_ = lean_ctor_get(v_x_1907_, 0);
v_value_1910_ = lean_ctor_get(v_x_1907_, 1);
v_tail_1911_ = lean_ctor_get(v_x_1907_, 2);
v___x_1912_ = lean_name_eq(v_key_1909_, v_a_1906_);
if (v___x_1912_ == 0)
{
v_x_1907_ = v_tail_1911_;
goto _start;
}
else
{
lean_object* v___x_1914_; 
lean_inc(v_value_1910_);
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_value_1910_);
return v___x_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1915_, v_x_1916_);
lean_dec(v_x_1916_);
lean_dec(v_a_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object* v_m_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_buckets_1920_; lean_object* v___x_1921_; uint64_t v___y_1923_; 
v_buckets_1920_ = lean_ctor_get(v_m_1918_, 1);
v___x_1921_ = lean_array_get_size(v_buckets_1920_);
if (lean_obj_tag(v_a_1919_) == 0)
{
uint64_t v___x_1937_; 
v___x_1937_ = 1723ULL;
v___y_1923_ = v___x_1937_;
goto v___jp_1922_;
}
else
{
uint64_t v_hash_1938_; 
v_hash_1938_ = lean_ctor_get_uint64(v_a_1919_, sizeof(void*)*2);
v___y_1923_ = v_hash_1938_;
goto v___jp_1922_;
}
v___jp_1922_:
{
uint64_t v___x_1924_; uint64_t v___x_1925_; uint64_t v_fold_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; uint64_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1924_ = 32ULL;
v___x_1925_ = lean_uint64_shift_right(v___y_1923_, v___x_1924_);
v_fold_1926_ = lean_uint64_xor(v___y_1923_, v___x_1925_);
v___x_1927_ = 16ULL;
v___x_1928_ = lean_uint64_shift_right(v_fold_1926_, v___x_1927_);
v___x_1929_ = lean_uint64_xor(v_fold_1926_, v___x_1928_);
v___x_1930_ = lean_uint64_to_usize(v___x_1929_);
v___x_1931_ = lean_usize_of_nat(v___x_1921_);
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_sub(v___x_1931_, v___x_1932_);
v___x_1934_ = lean_usize_land(v___x_1930_, v___x_1933_);
v___x_1935_ = lean_array_uget_borrowed(v_buckets_1920_, v___x_1934_);
v___x_1936_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1919_, v___x_1935_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object* v_m_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_m_1939_);
return v_res_1941_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object* v___x_1942_, lean_object* v_declName_1943_, lean_object* v_as_1944_, size_t v_sz_1945_, size_t v_i_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_usize_dec_lt(v_i_1946_, v_sz_1945_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v_declName_1943_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_b_1947_);
lean_ctor_set(v___x_1955_, 1, v___y_1948_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v_modules_1958_; lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v_toImport_1962_; lean_object* v_module_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; lean_object* v___x_1966_; 
v___x_1957_ = l_Lean_Environment_header(v___x_1942_);
v_modules_1958_ = lean_ctor_get(v___x_1957_, 3);
lean_inc_ref(v_modules_1958_);
lean_dec_ref(v___x_1957_);
v___x_1959_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1960_ = lean_array_uget_borrowed(v_as_1944_, v_i_1946_);
v___x_1961_ = lean_array_get(v___x_1959_, v_modules_1958_, v_a_1960_);
lean_dec_ref(v_modules_1958_);
v_toImport_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc_ref(v_toImport_1962_);
lean_dec(v___x_1961_);
v_module_1963_ = lean_ctor_get(v_toImport_1962_, 0);
lean_inc(v_module_1963_);
lean_dec_ref(v_toImport_1962_);
v___x_1964_ = lean_box(0);
v___x_1965_ = 0;
lean_inc(v_declName_1943_);
v___x_1966_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1963_, v___x_1965_, v_declName_1943_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v_snd_1968_; size_t v___x_1969_; size_t v___x_1970_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v_snd_1968_ = lean_ctor_get(v_a_1967_, 1);
lean_inc(v_snd_1968_);
lean_dec(v_a_1967_);
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1946_, v___x_1969_);
v_i_1946_ = v___x_1970_;
v_b_1947_ = v___x_1964_;
v___y_1948_ = v_snd_1968_;
goto _start;
}
else
{
lean_dec(v_declName_1943_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1942_ = stack[0].m_obj;
lean_object* v_declName_1943_ = stack[1].m_obj;
lean_object* v_as_1944_ = stack[2].m_obj;
size_t v_sz_1945_ = stack[3].m_num;
size_t v_i_1946_ = stack[4].m_num;
lean_object* v_b_1947_ = stack[5].m_obj;
lean_object* v___y_1948_ = stack[6].m_obj;
lean_object* v___y_1949_ = stack[7].m_obj;
lean_object* v___y_1950_ = stack[8].m_obj;
lean_object* v___y_1951_ = stack[9].m_obj;
lean_object* v___y_1952_ = stack[10].m_obj;
lean_object* v_res_1972_;
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_1942_, v_declName_1943_, v_as_1944_, v_sz_1945_, v_i_1946_, v_b_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
stack->m_obj
 = v_res_1972_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object* v___x_1973_, lean_object* v_declName_1974_, lean_object* v_as_1975_, lean_object* v_sz_1976_, lean_object* v_i_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
size_t v_sz_boxed_1985_; size_t v_i_boxed_1986_; lean_object* v_res_1987_; 
v_sz_boxed_1985_ = lean_unbox_usize(v_sz_1976_);
lean_dec(v_sz_1976_);
v_i_boxed_1986_ = lean_unbox_usize(v_i_1977_);
lean_dec(v_i_1977_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_1973_, v_declName_1974_, v_as_1975_, v_sz_boxed_1985_, v_i_boxed_1986_, v_b_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v_as_1975_);
lean_dec_ref(v___x_1973_);
return v_res_1987_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1988_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_declName_1991_, uint8_t v_isMeta_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v_env_2005_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___x_2030_; 
v___x_1999_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0);
v___x_2000_ = lean_st_ref_get(v___y_1997_);
v_env_2005_ = lean_ctor_get(v___x_2000_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2000_);
v___x_2030_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2005_, v_declName_1991_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_dec_ref(v_env_2005_);
lean_dec(v_declName_1991_);
goto v___jp_2001_;
}
else
{
lean_object* v_val_2031_; lean_object* v___x_2032_; lean_object* v_modules_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_val_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_val_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = l_Lean_Environment_header(v_env_2005_);
v_modules_2033_ = lean_ctor_get(v___x_2032_, 3);
lean_inc_ref(v_modules_2033_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = lean_array_get_size(v_modules_2033_);
v___x_2035_ = lean_nat_dec_lt(v_val_2031_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_dec_ref(v_modules_2033_);
lean_dec(v_val_2031_);
lean_dec_ref(v_env_2005_);
lean_dec(v_declName_1991_);
goto v___jp_2001_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___y_2039_; 
v___x_2036_ = lean_array_fget(v_modules_2033_, v_val_2031_);
lean_dec(v_val_2031_);
lean_dec_ref(v_modules_2033_);
v___x_2037_ = lean_st_ref_get(v___y_1997_);
if (v_isMeta_1992_ == 0)
{
lean_dec(v___x_2037_);
v___y_2039_ = v_isMeta_1992_;
goto v___jp_2038_;
}
else
{
lean_object* v_env_2052_; uint8_t v___x_2053_; 
v_env_2052_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2037_);
lean_inc(v_declName_1991_);
v___x_2053_ = l_Lean_isMarkedMeta(v_env_2052_, v_declName_1991_);
if (v___x_2053_ == 0)
{
v___y_2039_ = v_isMeta_1992_;
goto v___jp_2038_;
}
else
{
uint8_t v___x_2054_; 
v___x_2054_ = 0;
v___y_2039_ = v___x_2054_;
goto v___jp_2038_;
}
}
v___jp_2038_:
{
lean_object* v_toImport_2040_; lean_object* v_module_2041_; lean_object* v___x_2042_; 
v_toImport_2040_ = lean_ctor_get(v___x_2036_, 0);
lean_inc_ref(v_toImport_2040_);
lean_dec(v___x_2036_);
v_module_2041_ = lean_ctor_get(v_toImport_2040_, 0);
lean_inc(v_module_2041_);
lean_dec_ref(v_toImport_2040_);
lean_inc(v_declName_1991_);
v___x_2042_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_2041_, v___y_2039_, v_declName_1991_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v_snd_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v_snd_2044_ = lean_ctor_get(v_a_2043_, 1);
lean_inc(v_snd_2044_);
lean_dec(v_a_2043_);
v___x_2045_ = l_Lean_indirectModUseExt;
v___x_2046_ = lean_box(1);
v___x_2047_ = lean_box(0);
lean_inc_ref(v_env_2005_);
v___x_2048_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1999_, v___x_2045_, v_env_2005_, v___x_2046_, v___x_2047_);
v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_2048_, v_declName_1991_);
lean_dec(v___x_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___y_2007_ = v_snd_2044_;
v___y_2008_ = v___x_2050_;
goto v___jp_2006_;
}
else
{
lean_object* v_val_2051_; 
v_val_2051_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2049_, 1);
v___y_2007_ = v_snd_2044_;
v___y_2008_ = v_val_2051_;
goto v___jp_2006_;
}
}
else
{
lean_dec_ref(v_env_2005_);
lean_dec(v_declName_1991_);
return v___x_2042_;
}
}
}
}
v___jp_2001_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___y_1993_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
v___jp_2006_:
{
lean_object* v___x_2009_; size_t v_sz_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2009_ = lean_box(0);
v_sz_2010_ = lean_array_size(v___y_2008_);
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_2005_, v_declName_1991_, v___y_2008_, v_sz_2010_, v___x_2011_, v___x_2009_, v___y_2007_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec_ref(v___y_2008_);
lean_dec_ref(v_env_2005_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2029_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2029_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2029_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_snd_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
v_snd_2017_ = lean_ctor_get(v_a_2013_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_2013_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_a_2013_, 0);
lean_dec(v_unused_2028_);
v___x_2019_ = v_a_2013_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_snd_2017_);
lean_dec(v_a_2013_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2009_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_snd_2017_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2022_);
v___x_2024_ = v___x_2015_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
return v___x_2012_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1991_ = stack[0].m_obj;
uint8_t v_isMeta_1992_ = stack[1].m_num;
lean_object* v___y_1993_ = stack[2].m_obj;
lean_object* v___y_1994_ = stack[3].m_obj;
lean_object* v___y_1995_ = stack[4].m_obj;
lean_object* v___y_1996_ = stack[5].m_obj;
lean_object* v___y_1997_ = stack[6].m_obj;
lean_object* v_res_2055_;
v_res_2055_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_1991_, v_isMeta_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
stack->m_obj
 = v_res_2055_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_declName_2056_, lean_object* v_isMeta_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v_isMeta_boxed_2064_; lean_object* v_res_2065_; 
v_isMeta_boxed_2064_ = lean_unbox(v_isMeta_2057_);
v_res_2065_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_2056_, v_isMeta_boxed_2064_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2066_, lean_object* v_vals_2067_, lean_object* v_i_2068_, lean_object* v_k_2069_){
_start:
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_array_get_size(v_keys_2066_);
v___x_2071_ = lean_nat_dec_lt(v_i_2068_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_i_2068_);
v___x_2072_ = lean_box(0);
return v___x_2072_;
}
else
{
lean_object* v_k_x27_2073_; uint8_t v___x_2074_; 
v_k_x27_2073_ = lean_array_fget_borrowed(v_keys_2066_, v_i_2068_);
v___x_2074_ = lean_name_eq(v_k_2069_, v_k_x27_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = lean_nat_add(v_i_2068_, v___x_2075_);
lean_dec(v_i_2068_);
v_i_2068_ = v___x_2076_;
goto _start;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_array_fget_borrowed(v_vals_2067_, v_i_2068_);
lean_dec(v_i_2068_);
lean_inc(v___x_2078_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_i_2082_, lean_object* v_k_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2080_, v_vals_2081_, v_i_2082_, v_k_2083_);
lean_dec(v_k_2083_);
lean_dec_ref(v_vals_2081_);
lean_dec_ref(v_keys_2080_);
return v_res_2084_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_2085_, size_t v_x_2086_, lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2085_) == 0)
{
lean_object* v_es_2088_; lean_object* v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; lean_object* v_j_2092_; lean_object* v___x_2093_; 
v_es_2088_ = lean_ctor_get(v_x_2085_, 0);
v___x_2089_ = lean_box(2);
v___x_2090_ = ((size_t)31ULL);
v___x_2091_ = lean_usize_land(v_x_2086_, v___x_2090_);
v_j_2092_ = lean_usize_to_nat(v___x_2091_);
v___x_2093_ = lean_array_get_borrowed(v___x_2089_, v_es_2088_, v_j_2092_);
lean_dec(v_j_2092_);
switch(lean_obj_tag(v___x_2093_))
{
case 0:
{
lean_object* v_key_2094_; lean_object* v_val_2095_; uint8_t v___x_2096_; 
v_key_2094_ = lean_ctor_get(v___x_2093_, 0);
v_val_2095_ = lean_ctor_get(v___x_2093_, 1);
v___x_2096_ = lean_name_eq(v_x_2087_, v_key_2094_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_box(0);
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
lean_inc(v_val_2095_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_val_2095_);
return v___x_2098_;
}
}
case 1:
{
lean_object* v_node_2099_; size_t v___x_2100_; size_t v___x_2101_; 
v_node_2099_ = lean_ctor_get(v___x_2093_, 0);
v___x_2100_ = ((size_t)5ULL);
v___x_2101_ = lean_usize_shift_right(v_x_2086_, v___x_2100_);
v_x_2085_ = v_node_2099_;
v_x_2086_ = v___x_2101_;
goto _start;
}
default: 
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_box(0);
return v___x_2103_;
}
}
}
else
{
lean_object* v_ks_2104_; lean_object* v_vs_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_ks_2104_ = lean_ctor_get(v_x_2085_, 0);
v_vs_2105_ = lean_ctor_get(v_x_2085_, 1);
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_2104_, v_vs_2105_, v___x_2106_, v_x_2087_);
return v___x_2107_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2085_ = stack[0].m_obj;
size_t v_x_2086_ = stack[1].m_num;
lean_object* v_x_2087_ = stack[2].m_obj;
lean_object* v_res_2108_;
v_res_2108_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2085_, v_x_2086_, v_x_2087_);
stack->m_obj
 = v_res_2108_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
size_t v_x_28000__boxed_2112_; lean_object* v_res_2113_; 
v_x_28000__boxed_2112_ = lean_unbox_usize(v_x_2110_);
lean_dec(v_x_2110_);
v_res_2113_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2109_, v_x_28000__boxed_2112_, v_x_2111_);
lean_dec(v_x_2111_);
lean_dec_ref(v_x_2109_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_2114_, lean_object* v_x_2115_){
_start:
{
uint64_t v___y_2117_; 
if (lean_obj_tag(v_x_2115_) == 0)
{
uint64_t v___x_2120_; 
v___x_2120_ = 1723ULL;
v___y_2117_ = v___x_2120_;
goto v___jp_2116_;
}
else
{
uint64_t v_hash_2121_; 
v_hash_2121_ = lean_ctor_get_uint64(v_x_2115_, sizeof(void*)*2);
v___y_2117_ = v_hash_2121_;
goto v___jp_2116_;
}
v___jp_2116_:
{
size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_uint64_to_usize(v___y_2117_);
v___x_2119_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2114_, v___x_2118_, v_x_2115_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2122_, v_x_2123_);
lean_dec(v_x_2123_);
lean_dec_ref(v_x_2122_);
return v_res_2124_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2125_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_2128_ = l_Lean_stringToMessageData(v___x_2127_);
return v___x_2128_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2137_ = l_Lean_stringToMessageData(v___x_2136_);
return v___x_2137_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2138_, lean_object* v_init_2139_, lean_object* v_x_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
if (lean_obj_tag(v_x_2140_) == 0)
{
lean_object* v_k_2147_; lean_object* v_l_2148_; lean_object* v_r_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_k_2147_ = lean_ctor_get(v_x_2140_, 1);
lean_inc(v_k_2147_);
v_l_2148_ = lean_ctor_get(v_x_2140_, 3);
lean_inc(v_l_2148_);
v_r_2149_ = lean_ctor_get(v_x_2140_, 4);
lean_inc(v_r_2149_);
lean_dec_ref_known(v_x_2140_, 5);
v___x_2150_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_box(0);
lean_inc_ref(v_origDecl_2138_);
v___x_2153_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2138_, v_init_2139_, v_l_2148_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v_snd_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2275_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v_snd_2155_ = lean_ctor_get(v_a_2154_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; 
v_unused_2276_ = lean_ctor_get(v_a_2154_, 0);
lean_dec(v_unused_2276_);
v___x_2157_ = v_a_2154_;
v_isShared_2158_ = v_isSharedCheck_2275_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_snd_2155_);
lean_dec(v_a_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2275_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
uint8_t v___x_2159_; 
v___x_2159_ = l_Lean_NameSet_contains(v_snd_2155_, v_k_2147_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_env_2163_; lean_object* v___x_2164_; lean_object* v_toEnvExtension_2165_; lean_object* v_asyncMode_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2160_ = 1;
lean_inc(v_k_2147_);
v___x_2161_ = l_Lean_NameSet_insert(v_snd_2155_, v_k_2147_);
v___x_2162_ = lean_st_ref_get(v___y_2145_);
v_env_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_env_2163_);
lean_dec(v___x_2162_);
v___x_2164_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2165_ = lean_ctor_get(v___x_2164_, 0);
v_asyncMode_2166_ = lean_ctor_get(v_toEnvExtension_2165_, 2);
v___x_2167_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2150_, v___x_2164_, v_env_2163_, v_asyncMode_2166_, v___x_2152_, v___x_2159_);
v___x_2168_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2167_, v_k_2147_);
lean_dec(v___x_2167_);
if (lean_obj_tag(v___x_2168_) == 1)
{
lean_object* v_val_2169_; lean_object* v___x_2170_; 
lean_del_object(v___x_2157_);
lean_dec(v_k_2147_);
v_val_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_n(v_val_2169_, 2);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2169_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; uint8_t v___y_2173_; lean_object* v_toSignature_2187_; lean_object* v_name_2188_; uint8_t v___x_2189_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v_toSignature_2187_ = lean_ctor_get(v_val_2169_, 0);
v_name_2188_ = lean_ctor_get(v_toSignature_2187_, 0);
v___x_2189_ = l_Lean_isPrivateName(v_name_2188_);
if (v___x_2189_ == 0)
{
lean_dec(v_a_2171_);
v___y_2173_ = v___x_2159_;
goto v___jp_2172_;
}
else
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_unbox(v_a_2171_);
lean_dec(v_a_2171_);
v___y_2173_ = v___x_2190_;
goto v___jp_2172_;
}
v___jp_2172_:
{
if (v___y_2173_ == 0)
{
lean_dec(v_val_2169_);
v_init_2139_ = v___x_2151_;
v_x_2140_ = v_r_2149_;
v___y_2141_ = v___x_2161_;
goto _start;
}
else
{
lean_object* v___x_2175_; 
lean_inc_ref(v_origDecl_2138_);
v___x_2175_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2138_, v_val_2169_, v___x_2161_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_snd_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v_snd_2177_ = lean_ctor_get(v_a_2176_, 1);
lean_inc(v_snd_2177_);
lean_dec(v_a_2176_);
v_init_2139_ = v___x_2151_;
v_x_2140_ = v_r_2149_;
v___y_2141_ = v_snd_2177_;
goto _start;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_r_2149_);
lean_dec_ref(v_origDecl_2138_);
v_a_2179_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2175_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_val_2169_);
lean_dec(v___x_2161_);
lean_dec(v_r_2149_);
lean_dec_ref(v_origDecl_2138_);
v_a_2191_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2170_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2170_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2199_; lean_object* v_env_2200_; lean_object* v___x_2201_; 
lean_dec(v___x_2168_);
v___x_2199_ = lean_st_ref_get(v___y_2145_);
v_env_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc_ref(v_env_2200_);
lean_dec(v___x_2199_);
v___x_2201_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2200_, v_k_2147_);
lean_dec_ref(v_env_2200_);
if (lean_obj_tag(v___x_2201_) == 1)
{
lean_object* v_val_2202_; lean_object* v___x_2235_; uint8_t v___y_2245_; lean_object* v_env_2265_; lean_object* v___x_2266_; lean_object* v_modules_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_val_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_val_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2235_ = lean_st_ref_get(v___y_2145_);
v_env_2265_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_ref(v_env_2265_);
lean_dec(v___x_2235_);
v___x_2266_ = l_Lean_Environment_header(v_env_2265_);
lean_dec_ref(v_env_2265_);
v_modules_2267_ = lean_ctor_get(v___x_2266_, 3);
lean_inc_ref(v_modules_2267_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = lean_array_get_size(v_modules_2267_);
v___x_2269_ = lean_nat_dec_lt(v_val_2202_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v_modules_2267_);
v___y_2245_ = v___x_2159_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2270_; lean_object* v_toImport_2271_; uint8_t v_isExported_2272_; 
v___x_2270_ = lean_array_fget(v_modules_2267_, v_val_2202_);
lean_dec_ref(v_modules_2267_);
v_toImport_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc_ref(v_toImport_2271_);
lean_dec(v___x_2270_);
v_isExported_2272_ = lean_ctor_get_uint8(v_toImport_2271_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2271_);
if (v_isExported_2272_ == 0)
{
goto v___jp_2236_;
}
else
{
v___y_2245_ = v___x_2159_;
goto v___jp_2244_;
}
}
v___jp_2203_:
{
lean_object* v___x_2204_; lean_object* v_toSignature_2205_; lean_object* v_env_2206_; lean_object* v_name_2207_; lean_object* v___x_2208_; lean_object* v_moduleNames_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2204_ = lean_st_ref_get(v___y_2145_);
v_toSignature_2205_ = lean_ctor_get(v_origDecl_2138_, 0);
lean_inc_ref(v_toSignature_2205_);
lean_dec_ref(v_origDecl_2138_);
v_env_2206_ = lean_ctor_get(v___x_2204_, 0);
lean_inc_ref(v_env_2206_);
lean_dec(v___x_2204_);
v_name_2207_ = lean_ctor_get(v_toSignature_2205_, 0);
lean_inc(v_name_2207_);
lean_dec_ref(v_toSignature_2205_);
v___x_2208_ = l_Lean_Environment_header(v_env_2206_);
lean_dec_ref(v_env_2206_);
v_moduleNames_2209_ = lean_ctor_get(v___x_2208_, 4);
lean_inc_ref(v_moduleNames_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = l_Lean_MessageData_ofConstName(v_name_2207_, v___x_2159_);
v___x_2211_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 7);
lean_ctor_set(v___x_2157_, 1, v___x_2210_);
lean_ctor_set(v___x_2157_, 0, v___x_2211_);
v___x_2213_ = v___x_2157_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2210_);
v___x_2213_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
v___x_2214_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_MessageData_ofConstName(v_k_2147_, v___x_2159_);
v___x_2217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_array_get(v___x_2152_, v_moduleNames_2209_, v_val_2202_);
lean_dec(v_val_2202_);
lean_dec_ref(v_moduleNames_2209_);
v___x_2221_ = l_Lean_MessageData_ofName(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2224_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
v___jp_2236_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_a_2239_; lean_object* v_fst_2240_; uint8_t v___x_2241_; 
v___x_2237_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2238_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v___x_2237_, v___x_2161_, v___y_2144_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v_fst_2240_ = lean_ctor_get(v_a_2239_, 0);
v___x_2241_ = lean_unbox(v_fst_2240_);
if (v___x_2241_ == 0)
{
lean_dec(v_a_2239_);
lean_dec(v_r_2149_);
goto v___jp_2203_;
}
else
{
if (v___x_2159_ == 0)
{
lean_object* v_snd_2242_; 
lean_dec(v_val_2202_);
lean_del_object(v___x_2157_);
lean_dec(v_k_2147_);
v_snd_2242_ = lean_ctor_get(v_a_2239_, 1);
lean_inc(v_snd_2242_);
lean_dec(v_a_2239_);
v_init_2139_ = v___x_2151_;
v_x_2140_ = v_r_2149_;
v___y_2141_ = v_snd_2242_;
goto _start;
}
else
{
lean_dec(v_a_2239_);
lean_dec(v_r_2149_);
goto v___jp_2203_;
}
}
}
v___jp_2244_:
{
if (v___y_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v_env_2247_; uint8_t v___x_2248_; uint8_t v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_val_2202_);
lean_del_object(v___x_2157_);
v___x_2246_ = lean_st_ref_get(v___y_2145_);
v_env_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc_ref(v_env_2247_);
lean_dec(v___x_2246_);
lean_inc(v_k_2147_);
v___x_2248_ = l_Lean_getIRPhases(v_env_2247_, v_k_2147_);
v___x_2249_ = 1;
v___x_2250_ = l_Lean_instBEqIRPhases_beq(v___x_2248_, v___x_2249_);
v___x_2251_ = lean_box(v___x_2250_);
v___x_2252_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed), 8, 2);
lean_closure_set(v___x_2252_, 0, v_k_2147_);
lean_closure_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2252_, v___x_2160_, v___x_2161_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v_snd_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v_snd_2255_ = lean_ctor_get(v_a_2254_, 1);
lean_inc(v_snd_2255_);
lean_dec(v_a_2254_);
v_init_2139_ = v___x_2151_;
v_x_2140_ = v_r_2149_;
v___y_2141_ = v_snd_2255_;
goto _start;
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_r_2149_);
lean_dec_ref(v_origDecl_2138_);
v_a_2257_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2253_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2253_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
goto v___jp_2236_;
}
}
}
else
{
lean_dec(v___x_2201_);
lean_del_object(v___x_2157_);
lean_dec(v_k_2147_);
v_init_2139_ = v___x_2151_;
v_x_2140_ = v_r_2149_;
v___y_2141_ = v___x_2161_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2157_);
lean_dec(v_k_2147_);
v_init_2139_ = v___x_2151_;
v_x_2140_ = v_r_2149_;
v___y_2141_ = v_snd_2155_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2149_);
lean_dec(v_k_2147_);
lean_dec_ref(v_origDecl_2138_);
return v___x_2153_;
}
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_origDecl_2138_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_init_2139_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___y_2141_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_origDecl_2138_ = stack[0].m_obj;
lean_object* v_init_2139_ = stack[1].m_obj;
lean_object* v_x_2140_ = stack[2].m_obj;
lean_object* v___y_2141_ = stack[3].m_obj;
lean_object* v___y_2142_ = stack[4].m_obj;
lean_object* v___y_2143_ = stack[5].m_obj;
lean_object* v___y_2144_ = stack[6].m_obj;
lean_object* v___y_2145_ = stack[7].m_obj;
lean_object* v_res_2280_;
v_res_2280_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2138_, v_init_2139_, v_x_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
stack->m_obj
 = v_res_2280_;
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2281_, lean_object* v_origDecl_2282_, lean_object* v_code_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2290_ = l_Lean_NameSet_empty;
v___x_2291_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2281_, v_code_2283_, v___x_2290_);
v___x_2292_ = lean_box(0);
v___x_2293_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2282_, v___x_2292_, v___x_2291_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2310_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2310_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2310_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_snd_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2308_; 
v_snd_2298_ = lean_ctor_get(v_a_2294_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_a_2294_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_a_2294_, 0);
lean_dec(v_unused_2309_);
v___x_2300_ = v_a_2294_;
v_isShared_2301_ = v_isSharedCheck_2308_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_snd_2298_);
lean_dec(v_a_2294_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2308_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2292_);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_snd_2298_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2303_);
v___x_2305_ = v___x_2296_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2293_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2293_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2281_ = stack[0].m_num;
lean_object* v_origDecl_2282_ = stack[1].m_obj;
lean_object* v_code_2283_ = stack[2].m_obj;
lean_object* v___y_2284_ = stack[3].m_obj;
lean_object* v___y_2285_ = stack[4].m_obj;
lean_object* v___y_2286_ = stack[5].m_obj;
lean_object* v___y_2287_ = stack[6].m_obj;
lean_object* v___y_2288_ = stack[7].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_2281_, v_origDecl_2282_, v_code_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2320_, lean_object* v_origDecl_2321_, lean_object* v_code_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v___x_28114__boxed_2329_; lean_object* v_res_2330_; 
v___x_28114__boxed_2329_ = lean_unbox(v___x_2320_);
v_res_2330_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_28114__boxed_2329_, v_origDecl_2321_, v_code_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2330_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2331_, lean_object* v_decl_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_value_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; 
v_value_2339_ = lean_ctor_get(v_decl_2332_, 1);
lean_inc_ref(v_value_2339_);
lean_dec_ref(v_decl_2332_);
v___x_2340_ = 0;
v___x_2341_ = lean_box(v___x_2340_);
v___f_2342_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2342_, 0, v___x_2341_);
lean_closure_set(v___f_2342_, 1, v_origDecl_2331_);
v___x_2343_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2342_, v_value_2339_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2343_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_origDecl_2331_ = stack[0].m_obj;
lean_object* v_decl_2332_ = stack[1].m_obj;
lean_object* v_a_2333_ = stack[2].m_obj;
lean_object* v_a_2334_ = stack[3].m_obj;
lean_object* v_a_2335_ = stack[4].m_obj;
lean_object* v_a_2336_ = stack[5].m_obj;
lean_object* v_a_2337_ = stack[6].m_obj;
lean_object* v_res_2344_;
v_res_2344_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2331_, v_decl_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
stack->m_obj
 = v_res_2344_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2345_, lean_object* v_decl_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2345_, v_decl_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2354_, lean_object* v_init_2355_, lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2354_, v_init_2355_, v_x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2365_, v_x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2368_, v_x_2369_, v_x_2370_);
lean_dec(v_x_2370_);
lean_dec_ref(v_x_2369_);
return v_res_2371_;
}
}
lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_opt_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_2372_, v___y_2373_, v___y_2376_);
return v___x_2379_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_2372_ = stack[0].m_obj;
lean_object* v___y_2373_ = stack[1].m_obj;
lean_object* v___y_2374_ = stack[2].m_obj;
lean_object* v___y_2375_ = stack[3].m_obj;
lean_object* v___y_2376_ = stack[4].m_obj;
lean_object* v___y_2377_ = stack[5].m_obj;
lean_object* v_res_2380_;
v_res_2380_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
stack->m_obj
 = v_res_2380_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_opt_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_opt_2381_);
return v_res_2388_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2389_, lean_object* v_x_2390_, size_t v_x_2391_, lean_object* v_x_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2390_, v_x_2391_, v_x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2390_ = stack[1].m_obj;
size_t v_x_2391_ = stack[2].m_num;
lean_object* v_x_2392_ = stack[3].m_obj;
lean_object* v_res_2394_;
v_res_2394_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_box(0), v_x_2390_, v_x_2391_, v_x_2392_);
stack->m_obj
 = v_res_2394_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
size_t v_x_28739__boxed_2399_; lean_object* v_res_2400_; 
v_x_28739__boxed_2399_ = lean_unbox_usize(v_x_2397_);
lean_dec(v_x_2397_);
v_res_2400_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2395_, v_x_2396_, v_x_28739__boxed_2399_, v_x_2398_);
lean_dec(v_x_2398_);
lean_dec_ref(v_x_2396_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(lean_object* v_00_u03b2_2401_, lean_object* v_m_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_2402_, v_a_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2405_, lean_object* v_m_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_2405_, v_m_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_m_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2409_, lean_object* v_keys_2410_, lean_object* v_vals_2411_, lean_object* v_heq_2412_, lean_object* v_i_2413_, lean_object* v_k_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2410_, v_vals_2411_, v_i_2413_, v_k_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2416_, lean_object* v_keys_2417_, lean_object* v_vals_2418_, lean_object* v_heq_2419_, lean_object* v_i_2420_, lean_object* v_k_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2416_, v_keys_2417_, v_vals_2418_, v_heq_2419_, v_i_2420_, v_k_2421_);
lean_dec(v_k_2421_);
lean_dec_ref(v_vals_2418_);
lean_dec_ref(v_keys_2417_);
return v_res_2422_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
uint8_t v___x_2426_; 
v___x_2426_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_2424_, v_x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2424_ = stack[1].m_obj;
lean_object* v_x_2425_ = stack[2].m_obj;
uint8_t v_res_2427_;
v_res_2427_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_box(0), v_x_2424_, v_x_2425_);
stack->m_num = v_res_2427_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2428_, lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
uint8_t v_res_2431_; lean_object* v_r_2432_; 
v_res_2431_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_2428_, v_x_2429_, v_x_2430_);
lean_dec_ref(v_x_2430_);
lean_dec_ref(v_x_2429_);
v_r_2432_ = lean_box(v_res_2431_);
return v_r_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_2433_, lean_object* v_a_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_2434_, v_x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_2437_, v_a_2438_, v_x_2439_);
lean_dec(v_x_2439_);
lean_dec(v_a_2438_);
return v_res_2440_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2441_, lean_object* v_x_2442_, size_t v_x_2443_, lean_object* v_x_2444_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_2442_, v_x_2443_, v_x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2442_ = stack[1].m_obj;
size_t v_x_2443_ = stack[2].m_num;
lean_object* v_x_2444_ = stack[3].m_obj;
uint8_t v_res_2446_;
v_res_2446_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_box(0), v_x_2442_, v_x_2443_, v_x_2444_);
stack->m_num = v_res_2446_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2447_, lean_object* v_x_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
size_t v_x_28784__boxed_2451_; uint8_t v_res_2452_; lean_object* v_r_2453_; 
v_x_28784__boxed_2451_ = lean_unbox_usize(v_x_2449_);
lean_dec(v_x_2449_);
v_res_2452_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_2447_, v_x_2448_, v_x_28784__boxed_2451_, v_x_2450_);
lean_dec_ref(v_x_2450_);
lean_dec_ref(v_x_2448_);
v_r_2453_ = lean_box(v_res_2452_);
return v_r_2453_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_2454_, lean_object* v_keys_2455_, lean_object* v_vals_2456_, lean_object* v_heq_2457_, lean_object* v_i_2458_, lean_object* v_k_2459_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_2455_, v_i_2458_, v_k_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2455_ = stack[1].m_obj;
lean_object* v_vals_2456_ = stack[2].m_obj;
lean_object* v_i_2458_ = stack[4].m_obj;
lean_object* v_k_2459_ = stack[5].m_obj;
uint8_t v_res_2461_;
v_res_2461_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_box(0), v_keys_2455_, v_vals_2456_, lean_box(0), v_i_2458_, v_k_2459_);
stack->m_num = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2462_, lean_object* v_keys_2463_, lean_object* v_vals_2464_, lean_object* v_heq_2465_, lean_object* v_i_2466_, lean_object* v_k_2467_){
_start:
{
uint8_t v_res_2468_; lean_object* v_r_2469_; 
v_res_2468_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_2462_, v_keys_2463_, v_vals_2464_, v_heq_2465_, v_i_2466_, v_k_2467_);
lean_dec_ref(v_k_2467_);
lean_dec_ref(v_vals_2464_);
lean_dec_ref(v_keys_2463_);
v_r_2469_ = lean_box(v_res_2468_);
return v_r_2469_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2470_, size_t v_sz_2471_, size_t v_i_2472_, lean_object* v_b_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_a_2480_; uint8_t v___x_2484_; 
v___x_2484_ = lean_usize_dec_lt(v_i_2472_, v_sz_2471_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_b_2473_);
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; lean_object* v_a_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_box(0);
v_a_2487_ = lean_array_uget_borrowed(v_as_2470_, v_i_2472_);
lean_inc(v_a_2487_);
v___x_2488_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2487_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_toSignature_2489_; lean_object* v_a_2490_; lean_object* v_name_2491_; uint8_t v___x_2492_; 
v_toSignature_2489_ = lean_ctor_get(v_a_2487_, 0);
v_a_2490_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2488_, 1);
v_name_2491_ = lean_ctor_get(v_toSignature_2489_, 0);
v___x_2492_ = l_Lean_isPrivateName(v_name_2491_);
if (v___x_2492_ == 0)
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_unbox(v_a_2490_);
lean_dec(v_a_2490_);
if (v___x_2493_ == 0)
{
v_a_2480_ = v___x_2486_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_st_ref_get(v___y_2477_);
lean_dec(v___x_2494_);
v___x_2495_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2487_, 2);
v___x_2496_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2487_, v_a_2487_, v___x_2495_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_dec_ref_known(v___x_2496_, 1);
v_a_2480_ = v___x_2486_;
goto v___jp_2479_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
else
{
lean_dec(v_a_2490_);
v_a_2480_ = v___x_2486_;
goto v___jp_2479_;
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2505_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2488_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2488_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
v___jp_2479_:
{
size_t v___x_2481_; size_t v___x_2482_; 
v___x_2481_ = ((size_t)1ULL);
v___x_2482_ = lean_usize_add(v_i_2472_, v___x_2481_);
v_i_2472_ = v___x_2482_;
v_b_2473_ = v_a_2480_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2470_ = stack[0].m_obj;
size_t v_sz_2471_ = stack[1].m_num;
size_t v_i_2472_ = stack[2].m_num;
lean_object* v_b_2473_ = stack[3].m_obj;
lean_object* v___y_2474_ = stack[4].m_obj;
lean_object* v___y_2475_ = stack[5].m_obj;
lean_object* v___y_2476_ = stack[6].m_obj;
lean_object* v___y_2477_ = stack[7].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2470_, v_sz_2471_, v_i_2472_, v_b_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2514_, lean_object* v_sz_2515_, lean_object* v_i_2516_, lean_object* v_b_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
size_t v_sz_boxed_2523_; size_t v_i_boxed_2524_; lean_object* v_res_2525_; 
v_sz_boxed_2523_ = lean_unbox_usize(v_sz_2515_);
lean_dec(v_sz_2515_);
v_i_boxed_2524_ = lean_unbox_usize(v_i_2516_);
lean_dec(v_i_2516_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2514_, v_sz_boxed_2523_, v_i_boxed_2524_, v_b_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v_as_2514_);
return v_res_2525_;
}
}
lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; lean_object* v_env_2533_; lean_object* v___x_2534_; uint8_t v_isModule_2535_; 
v___x_2532_ = lean_st_ref_get(v___y_2530_);
v_env_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_ref(v_env_2533_);
lean_dec(v___x_2532_);
v___x_2534_ = l_Lean_Environment_header(v_env_2533_);
lean_dec_ref(v_env_2533_);
v_isModule_2535_ = lean_ctor_get_uint8(v___x_2534_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2534_);
if (v_isModule_2535_ == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_decls_2526_);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; size_t v_sz_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2537_ = lean_box(0);
v_sz_2538_ = lean_array_size(v_decls_2526_);
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2526_, v_sz_2538_, v___x_2539_, v___x_2537_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v___x_2540_, 0);
lean_dec(v_unused_2548_);
v___x_2542_ = v___x_2540_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_dec(v___x_2540_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_decls_2526_);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_decls_2526_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_decls_2526_);
v_a_2549_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2540_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2540_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_2526_ = stack[0].m_obj;
lean_object* v___y_2527_ = stack[1].m_obj;
lean_object* v___y_2528_ = stack[2].m_obj;
lean_object* v___y_2529_ = stack[3].m_obj;
lean_object* v___y_2530_ = stack[4].m_obj;
lean_object* v_res_2557_;
v_res_2557_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
stack->m_obj
 = v_res_2557_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2564_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2578_ = l_Lean_stringToMessageData(v___x_2577_);
return v___x_2578_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2579_, uint8_t v___x_2580_, lean_object* v_as_2581_, size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_a_2591_; uint8_t v___x_2595_; 
v___x_2595_ = lean_usize_dec_lt(v_i_2583_, v_sz_2582_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v_b_2584_);
return v___x_2596_;
}
else
{
lean_object* v___x_2597_; lean_object* v_a_2598_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___x_2606_; lean_object* v_toSignature_2607_; lean_object* v_env_2608_; lean_object* v_name_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2597_ = lean_box(0);
v_a_2598_ = lean_array_uget_borrowed(v_as_2581_, v_i_2583_);
v___x_2606_ = lean_st_ref_get(v___y_2588_);
v_toSignature_2607_ = lean_ctor_get(v_a_2598_, 0);
v_env_2608_ = lean_ctor_get(v___x_2606_, 0);
lean_inc_ref(v_env_2608_);
lean_dec(v___x_2606_);
v_name_2609_ = lean_ctor_get(v_toSignature_2607_, 0);
v___x_2610_ = l_Lean_Environment_setExporting(v_env_2608_, v___x_2580_);
lean_inc(v_name_2609_);
v___x_2611_ = l_Lean_Environment_contains(v___x_2610_, v_name_2609_, v___x_2580_);
if (v___x_2611_ == 0)
{
v_a_2591_ = v___x_2597_;
goto v___jp_2590_;
}
else
{
lean_object* v_toCold_2612_; lean_object* v_options_2613_; uint8_t v_hasTrace_2614_; 
v_toCold_2612_ = lean_ctor_get(v___y_2587_, 0);
v_options_2613_ = lean_ctor_get(v_toCold_2612_, 2);
v_hasTrace_2614_ = lean_ctor_get_uint8(v_options_2613_, sizeof(void*)*1);
if (v_hasTrace_2614_ == 0)
{
v___y_2600_ = v___y_2585_;
v___y_2601_ = v___y_2586_;
v___y_2602_ = v___y_2587_;
v___y_2603_ = v___y_2588_;
goto v___jp_2599_;
}
else
{
lean_object* v_inheritedTraceOptions_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_inheritedTraceOptions_2615_ = lean_ctor_get(v_toCold_2612_, 11);
v___x_2616_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2617_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2618_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2615_, v_options_2613_, v___x_2617_);
if (v___x_2618_ == 0)
{
v___y_2600_ = v___y_2585_;
v___y_2601_ = v___y_2586_;
v___y_2602_ = v___y_2587_;
v___y_2603_ = v___y_2588_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2619_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2609_);
v___x_2620_ = l_Lean_MessageData_ofName(v_name_2609_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2616_, v___x_2623_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_dec_ref_known(v___x_2624_, 1);
v___y_2600_ = v___y_2585_;
v___y_2601_ = v___y_2586_;
v___y_2602_ = v___y_2587_;
v___y_2603_ = v___y_2588_;
goto v___jp_2599_;
}
else
{
return v___x_2624_;
}
}
}
}
v___jp_2599_:
{
uint8_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2579_);
lean_inc(v_a_2598_);
v___x_2605_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2604_, v_phase_2579_, v_a_2598_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_dec_ref_known(v___x_2605_, 1);
v_a_2591_ = v___x_2597_;
goto v___jp_2590_;
}
else
{
return v___x_2605_;
}
}
}
v___jp_2590_:
{
size_t v___x_2592_; size_t v___x_2593_; 
v___x_2592_ = ((size_t)1ULL);
v___x_2593_ = lean_usize_add(v_i_2583_, v___x_2592_);
v_i_2583_ = v___x_2593_;
v_b_2584_ = v_a_2591_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_2579_ = stack[0].m_num;
uint8_t v___x_2580_ = stack[1].m_num;
lean_object* v_as_2581_ = stack[2].m_obj;
size_t v_sz_2582_ = stack[3].m_num;
size_t v_i_2583_ = stack[4].m_num;
lean_object* v_b_2584_ = stack[5].m_obj;
lean_object* v___y_2585_ = stack[6].m_obj;
lean_object* v___y_2586_ = stack[7].m_obj;
lean_object* v___y_2587_ = stack[8].m_obj;
lean_object* v___y_2588_ = stack[9].m_obj;
lean_object* v_res_2625_;
v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2579_, v___x_2580_, v_as_2581_, v_sz_2582_, v_i_2583_, v_b_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
stack->m_obj
 = v_res_2625_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2626_, lean_object* v___x_2627_, lean_object* v_as_2628_, lean_object* v_sz_2629_, lean_object* v_i_2630_, lean_object* v_b_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v_phase_boxed_2637_; uint8_t v___x_2258__boxed_2638_; size_t v_sz_boxed_2639_; size_t v_i_boxed_2640_; lean_object* v_res_2641_; 
v_phase_boxed_2637_ = lean_unbox(v_phase_2626_);
v___x_2258__boxed_2638_ = lean_unbox(v___x_2627_);
v_sz_boxed_2639_ = lean_unbox_usize(v_sz_2629_);
lean_dec(v_sz_2629_);
v_i_boxed_2640_ = lean_unbox_usize(v_i_2630_);
lean_dec(v_i_2630_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2637_, v___x_2258__boxed_2638_, v_as_2628_, v_sz_boxed_2639_, v_i_boxed_2640_, v_b_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec_ref(v_as_2628_);
return v_res_2641_;
}
}
lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2642_, lean_object* v_decls_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; lean_object* v_env_2650_; lean_object* v___x_2651_; uint8_t v_isModule_2652_; 
v___x_2649_ = lean_st_ref_get(v___y_2647_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2651_ = l_Lean_Environment_header(v_env_2650_);
lean_dec_ref(v_env_2650_);
v_isModule_2652_ = lean_ctor_get_uint8(v___x_2651_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2651_);
if (v_isModule_2652_ == 0)
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_decls_2643_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; size_t v_sz_2655_; size_t v___x_2656_; lean_object* v___x_2657_; 
v___x_2654_ = lean_box(0);
v_sz_2655_ = lean_array_size(v_decls_2643_);
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2642_, v_isModule_2652_, v_decls_2643_, v_sz_2655_, v___x_2656_, v___x_2654_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2657_, 0);
lean_dec(v_unused_2665_);
v___x_2659_ = v___x_2657_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_dec(v___x_2657_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v_decls_2643_);
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_decls_2643_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v_decls_2643_);
v_a_2666_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2657_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2657_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_inferVisibility___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_2642_ = stack[0].m_num;
lean_object* v_decls_2643_ = stack[1].m_obj;
lean_object* v___y_2644_ = stack[2].m_obj;
lean_object* v___y_2645_ = stack[3].m_obj;
lean_object* v___y_2646_ = stack[4].m_obj;
lean_object* v___y_2647_ = stack[5].m_obj;
lean_object* v_res_2674_;
v_res_2674_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_2642_, v_decls_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
stack->m_obj
 = v_res_2674_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2675_, lean_object* v_decls_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_phase_boxed_2682_; lean_object* v_res_2683_; 
v_phase_boxed_2682_ = lean_unbox(v_phase_2675_);
v_res_2683_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2682_, v_decls_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
return v_res_2683_;
}
}
lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2686_){
_start:
{
lean_object* v___x_2687_; lean_object* v___f_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2687_ = lean_box(v_phase_2686_);
v___f_2688_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2688_, 0, v___x_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = 0;
v___x_2691_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2692_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2692_, 0, v___x_2689_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_ctor_set(v___x_2692_, 2, v___f_2688_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*3, v_phase_2686_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*3 + 1, v_phase_2686_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*3 + 2, v___x_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_inferVisibility_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_2686_ = stack[0].m_num;
lean_object* v_res_2693_;
v_res_2693_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_2686_);
stack->m_obj
 = v_res_2693_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2694_){
_start:
{
uint8_t v_phase_boxed_2695_; lean_object* v_res_2696_; 
v_phase_boxed_2695_ = lean_unbox(v_phase_2694_);
v_res_2696_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2695_);
return v_res_2696_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = lean_unsigned_to_nat(3356661454u);
v___x_2749_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2750_ = l_Lean_Name_num___override(v___x_2749_, v___x_2748_);
return v___x_2750_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2753_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2754_ = l_Lean_Name_str___override(v___x_2753_, v___x_2752_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2757_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2758_ = l_Lean_Name_str___override(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = lean_unsigned_to_nat(2u);
v___x_2760_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2761_ = l_Lean_Name_num___override(v___x_2760_, v___x_2759_);
return v___x_2761_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2764_ = 0;
v___x_2765_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2766_ = l_Lean_registerTraceClass(v___x_2763_, v___x_2764_, v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2767_;
v_res_2767_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2767_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2769_;
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
