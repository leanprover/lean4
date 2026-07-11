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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_getIRPhases(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_baseExt;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqConstantKind_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_compiler_small;
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclTransparent(lean_object*, uint8_t, lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = " as transparent because it is opaque and its body looks relevant"};
static const lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4;
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__3_value;
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
lean_object* v_options_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v_options_165_ = lean_ctor_get(v___y_143_, 2);
v___x_166_ = l_Lean_Compiler_LCNF_compiler_small;
v___x_167_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_options_165_, v___x_166_);
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
uint8_t v_a_951__boxed_183_; uint8_t v_pu_boxed_184_; lean_object* v_res_185_; 
v_a_951__boxed_183_ = lean_unbox(v_a_175_);
v_pu_boxed_184_ = lean_unbox(v_pu_176_);
v_res_185_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_174_, v_a_951__boxed_183_, v_pu_boxed_184_, v_code_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
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
lean_inc(v_a_194_);
v___x_195_ = lean_unbox(v_a_194_);
if (v___x_195_ == 0)
{
lean_object* v_toSignature_196_; lean_object* v_value_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___x_200_; 
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
lean_dec(v_a_194_);
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
v___x_210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
lean_ctor_set(v___x_215_, 3, v___x_214_);
lean_ctor_set(v___x_215_, 4, v___x_213_);
lean_ctor_set(v___x_215_, 5, v___x_213_);
lean_ctor_set(v___x_215_, 6, v___x_213_);
lean_ctor_set(v___x_215_, 7, v___x_213_);
lean_ctor_set(v___x_215_, 8, v___x_213_);
lean_ctor_set(v___x_215_, 9, v___x_213_);
return v___x_215_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_216_; double v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_float_of_nat(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(lean_object* v_cls_221_, lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_options_228_; lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_options_228_ = lean_ctor_get(v___y_225_, 2);
v_ref_229_ = lean_ctor_get(v___y_225_, 5);
v___x_230_ = lean_st_ref_get(v___y_226_);
v___x_231_ = lean_st_ref_get(v___y_224_);
v___x_232_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_223_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_291_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_291_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_291_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_291_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_env_237_; lean_object* v_lctx_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_289_; 
v_env_237_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_env_237_);
lean_dec(v___x_230_);
v_lctx_238_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_231_, 1);
lean_dec(v_unused_290_);
v___x_240_ = v___x_231_;
v_isShared_241_ = v_isSharedCheck_289_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_lctx_238_);
lean_dec(v___x_231_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_289_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_traceState_244_; lean_object* v_env_245_; lean_object* v_nextMacroScope_246_; lean_object* v_ngen_247_; lean_object* v_auxDeclNGen_248_; lean_object* v_cache_249_; lean_object* v_messages_250_; lean_object* v_infoState_251_; lean_object* v_snapshotTasks_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_288_; 
v___x_242_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_243_ = lean_st_ref_take(v___y_226_);
v_traceState_244_ = lean_ctor_get(v___x_243_, 4);
v_env_245_ = lean_ctor_get(v___x_243_, 0);
v_nextMacroScope_246_ = lean_ctor_get(v___x_243_, 1);
v_ngen_247_ = lean_ctor_get(v___x_243_, 2);
v_auxDeclNGen_248_ = lean_ctor_get(v___x_243_, 3);
v_cache_249_ = lean_ctor_get(v___x_243_, 5);
v_messages_250_ = lean_ctor_get(v___x_243_, 6);
v_infoState_251_ = lean_ctor_get(v___x_243_, 7);
v_snapshotTasks_252_ = lean_ctor_get(v___x_243_, 8);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_288_ == 0)
{
v___x_254_ = v___x_243_;
v_isShared_255_ = v_isSharedCheck_288_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snapshotTasks_252_);
lean_inc(v_infoState_251_);
lean_inc(v_messages_250_);
lean_inc(v_cache_249_);
lean_inc(v_traceState_244_);
lean_inc(v_auxDeclNGen_248_);
lean_inc(v_ngen_247_);
lean_inc(v_nextMacroScope_246_);
lean_inc(v_env_245_);
lean_dec(v___x_243_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_288_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint64_t v_tid_256_; lean_object* v_traces_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_287_; 
v_tid_256_ = lean_ctor_get_uint64(v_traceState_244_, sizeof(void*)*1);
v_traces_257_ = lean_ctor_get(v_traceState_244_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_traceState_244_);
if (v_isSharedCheck_287_ == 0)
{
v___x_259_ = v_traceState_244_;
v_isShared_260_ = v_isSharedCheck_287_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_traces_257_);
lean_dec(v_traceState_244_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_287_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_261_ = lean_unbox(v_a_233_);
lean_dec(v_a_233_);
v___x_262_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_238_, v___x_261_);
lean_dec_ref(v_lctx_238_);
lean_inc_ref(v_options_228_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_237_);
lean_ctor_set(v___x_263_, 1, v___x_242_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v_options_228_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 3);
lean_ctor_set(v___x_240_, 1, v_msg_222_);
lean_ctor_set(v___x_240_, 0, v___x_263_);
v___x_265_ = v___x_240_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_msg_222_);
v___x_265_ = v_reuseFailAlloc_286_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; double v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_268_ = 0;
v___x_269_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_270_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_270_, 0, v_cls_221_);
lean_ctor_set(v___x_270_, 1, v___x_266_);
lean_ctor_set(v___x_270_, 2, v___x_269_);
lean_ctor_set_float(v___x_270_, sizeof(void*)*3, v___x_267_);
lean_ctor_set_float(v___x_270_, sizeof(void*)*3 + 8, v___x_267_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*3 + 16, v___x_268_);
v___x_271_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_272_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_265_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
lean_inc(v_ref_229_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_229_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = l_Lean_PersistentArray_push___redArg(v_traces_257_, v___x_273_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_274_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_274_);
lean_ctor_set_uint64(v_reuseFailAlloc_285_, sizeof(void*)*1, v_tid_256_);
v___x_276_ = v_reuseFailAlloc_285_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v___x_276_);
v___x_278_ = v___x_254_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_env_245_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_nextMacroScope_246_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_ngen_247_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_auxDeclNGen_248_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_284_, 5, v_cache_249_);
lean_ctor_set(v_reuseFailAlloc_284_, 6, v_messages_250_);
lean_ctor_set(v_reuseFailAlloc_284_, 7, v_infoState_251_);
lean_ctor_set(v_reuseFailAlloc_284_, 8, v_snapshotTasks_252_);
v___x_278_ = v_reuseFailAlloc_284_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_st_ref_set(v___y_226_, v___x_278_);
v___x_280_ = lean_box(0);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_280_);
v___x_282_ = v___x_235_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
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
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v___x_231_);
lean_dec(v___x_230_);
lean_dec_ref(v_msg_222_);
lean_dec(v_cls_221_);
v_a_292_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_232_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_232_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___boxed(lean_object* v_cls_300_, lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v_cls_300_, v_msg_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(lean_object* v_f_308_, lean_object* v_v_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
if (lean_obj_tag(v_v_309_) == 0)
{
lean_object* v_code_315_; lean_object* v___x_316_; 
v_code_315_ = lean_ctor_get(v_v_309_, 0);
lean_inc_ref(v_code_315_);
lean_dec_ref_known(v_v_309_, 1);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
v___x_316_ = lean_apply_6(v_f_308_, v_code_315_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, lean_box(0));
return v___x_316_;
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_f_308_);
v_isSharedCheck_324_ = !lean_is_exclusive(v_v_309_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v_v_309_, 0);
lean_dec(v_unused_325_);
v___x_318_ = v_v_309_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_v_309_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_box(0);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 0);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg___boxed(lean_object* v_f_326_, lean_object* v_v_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_326_, v_v_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(uint8_t v_pu_334_, lean_object* v_f_335_, lean_object* v_v_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_335_, v_v_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(lean_object* v_pu_343_, lean_object* v_f_344_, lean_object* v_v_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
uint8_t v_pu_boxed_351_; lean_object* v_res_352_; 
v_pu_boxed_351_ = lean_unbox(v_pu_343_);
v_res_352_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_boxed_351_, v_f_344_, v_v_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object* v_pu_358_, lean_object* v_phase_359_, lean_object* v_decl_360_, lean_object* v_code_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v_pu_boxed_367_; uint8_t v_phase_boxed_368_; lean_object* v_res_369_; 
v_pu_boxed_367_ = lean_unbox(v_pu_358_);
v_phase_boxed_368_ = lean_unbox(v_phase_359_);
v_res_369_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(v_pu_boxed_367_, v_phase_boxed_368_, v_decl_360_, v_code_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_369_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_379_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_380_ = l_Lean_Name_append(v___x_379_, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec(uint8_t v_pu_387_, uint8_t v_phase_388_, lean_object* v_decl_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; lean_object* v_toSignature_396_; lean_object* v_env_397_; lean_object* v_nextMacroScope_398_; lean_object* v_ngen_399_; lean_object* v_auxDeclNGen_400_; lean_object* v_traceState_401_; lean_object* v_messages_402_; lean_object* v_infoState_403_; lean_object* v_snapshotTasks_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_479_; 
v___x_395_ = lean_st_ref_take(v_a_393_);
v_toSignature_396_ = lean_ctor_get(v_decl_389_, 0);
v_env_397_ = lean_ctor_get(v___x_395_, 0);
v_nextMacroScope_398_ = lean_ctor_get(v___x_395_, 1);
v_ngen_399_ = lean_ctor_get(v___x_395_, 2);
v_auxDeclNGen_400_ = lean_ctor_get(v___x_395_, 3);
v_traceState_401_ = lean_ctor_get(v___x_395_, 4);
v_messages_402_ = lean_ctor_get(v___x_395_, 6);
v_infoState_403_ = lean_ctor_get(v___x_395_, 7);
v_snapshotTasks_404_ = lean_ctor_get(v___x_395_, 8);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v___x_395_, 5);
lean_dec(v_unused_480_);
v___x_406_ = v___x_395_;
v_isShared_407_ = v_isSharedCheck_479_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snapshotTasks_404_);
lean_inc(v_infoState_403_);
lean_inc(v_messages_402_);
lean_inc(v_traceState_401_);
lean_inc(v_auxDeclNGen_400_);
lean_inc(v_ngen_399_);
lean_inc(v_nextMacroScope_398_);
lean_inc(v_env_397_);
lean_dec(v___x_395_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_479_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_value_408_; lean_object* v_name_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v_value_408_ = lean_ctor_get(v_decl_389_, 1);
lean_inc_ref(v_value_408_);
v_name_409_ = lean_ctor_get(v_toSignature_396_, 0);
lean_inc_n(v_name_409_, 2);
v___x_410_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_397_, v_name_409_);
v___x_411_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 5, v___x_411_);
lean_ctor_set(v___x_406_, 0, v___x_410_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_nextMacroScope_398_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_ngen_399_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_auxDeclNGen_400_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_traceState_401_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_messages_402_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_infoState_403_);
lean_ctor_set(v_reuseFailAlloc_478_, 8, v_snapshotTasks_404_);
v___x_413_ = v_reuseFailAlloc_478_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_st_ref_set(v_a_393_, v___x_413_);
lean_inc_ref(v_decl_389_);
v___x_415_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_387_, v_decl_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_469_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_469_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_469_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_469_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
uint8_t v___x_420_; 
v___x_420_ = lean_unbox(v_a_416_);
lean_dec(v_a_416_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec(v_name_409_);
lean_dec_ref(v_value_408_);
lean_dec_ref(v_decl_389_);
v___x_421_ = lean_box(0);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_421_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v___x_425_; lean_object* v_env_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___f_429_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; uint8_t v___x_455_; 
lean_del_object(v___x_418_);
v___x_425_ = lean_st_ref_get(v_a_393_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_425_);
v___x_427_ = lean_box(v_pu_387_);
v___x_428_ = lean_box(v_phase_388_);
v___f_429_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed), 9, 3);
lean_closure_set(v___f_429_, 0, v___x_427_);
lean_closure_set(v___f_429_, 1, v___x_428_);
lean_closure_set(v___f_429_, 2, v_decl_389_);
v___x_455_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_426_, v_phase_388_, v_name_409_);
if (v___x_455_ == 0)
{
lean_object* v_options_456_; uint8_t v_hasTrace_457_; 
v_options_456_ = lean_ctor_get(v_a_392_, 2);
v_hasTrace_457_ = lean_ctor_get_uint8(v_options_456_, sizeof(void*)*1);
if (v_hasTrace_457_ == 0)
{
v___y_431_ = v_a_390_;
v___y_432_ = v_a_391_;
v___y_433_ = v_a_392_;
v___y_434_ = v_a_393_;
goto v___jp_430_;
}
else
{
lean_object* v_inheritedTraceOptions_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_inheritedTraceOptions_458_ = lean_ctor_get(v_a_392_, 13);
v___x_459_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_460_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_458_, v_options_456_, v___x_460_);
if (v___x_461_ == 0)
{
v___y_431_ = v_a_390_;
v___y_432_ = v_a_391_;
v___y_433_ = v_a_392_;
v___y_434_ = v_a_393_;
goto v___jp_430_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_462_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_409_);
v___x_463_ = l_Lean_MessageData_ofName(v_name_409_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_459_, v___x_466_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec_ref_known(v___x_467_, 1);
v___y_431_ = v_a_390_;
v___y_432_ = v_a_391_;
v___y_433_ = v_a_392_;
v___y_434_ = v_a_393_;
goto v___jp_430_;
}
else
{
lean_dec_ref(v___f_429_);
lean_dec(v_name_409_);
lean_dec_ref(v_value_408_);
return v___x_467_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_name_409_);
v___x_468_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_429_, v_value_408_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_468_;
}
v___jp_430_:
{
lean_object* v___x_435_; lean_object* v_env_436_; lean_object* v_nextMacroScope_437_; lean_object* v_ngen_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_traceState_440_; lean_object* v_messages_441_; lean_object* v_infoState_442_; lean_object* v_snapshotTasks_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v___x_435_ = lean_st_ref_take(v___y_434_);
v_env_436_ = lean_ctor_get(v___x_435_, 0);
v_nextMacroScope_437_ = lean_ctor_get(v___x_435_, 1);
v_ngen_438_ = lean_ctor_get(v___x_435_, 2);
v_auxDeclNGen_439_ = lean_ctor_get(v___x_435_, 3);
v_traceState_440_ = lean_ctor_get(v___x_435_, 4);
v_messages_441_ = lean_ctor_get(v___x_435_, 6);
v_infoState_442_ = lean_ctor_get(v___x_435_, 7);
v_snapshotTasks_443_ = lean_ctor_get(v___x_435_, 8);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_435_, 5);
lean_dec(v_unused_454_);
v___x_445_ = v___x_435_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snapshotTasks_443_);
lean_inc(v_infoState_442_);
lean_inc(v_messages_441_);
lean_inc(v_traceState_440_);
lean_inc(v_auxDeclNGen_439_);
lean_inc(v_ngen_438_);
lean_inc(v_nextMacroScope_437_);
lean_inc(v_env_436_);
lean_dec(v___x_435_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_436_, v_phase_388_, v_name_409_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 5, v___x_411_);
lean_ctor_set(v___x_445_, 0, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_nextMacroScope_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_ngen_438_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_auxDeclNGen_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_traceState_440_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_messages_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_infoState_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_snapshotTasks_443_);
v___x_449_ = v_reuseFailAlloc_452_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_st_ref_set(v___y_434_, v___x_449_);
v___x_451_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_429_, v_value_408_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_451_;
}
}
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec(v_name_409_);
lean_dec_ref(v_value_408_);
lean_dec_ref(v_decl_389_);
v_a_470_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_415_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_415_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
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
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(uint8_t v_phase_484_, lean_object* v_decl_485_, lean_object* v_init_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v_k_493_; lean_object* v_l_494_; lean_object* v_r_495_; lean_object* v___x_496_; 
v_k_493_ = lean_ctor_get(v_x_487_, 1);
lean_inc(v_k_493_);
v_l_494_ = lean_ctor_get(v_x_487_, 3);
lean_inc(v_l_494_);
v_r_495_ = lean_ctor_get(v_x_487_, 4);
lean_inc(v_r_495_);
lean_dec_ref_known(v_x_487_, 5);
lean_inc_ref(v_decl_485_);
v___x_496_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_484_, v_decl_485_, v_init_486_, v_l_494_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; 
lean_dec_ref_known(v___x_496_, 1);
v___x_497_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_493_, v_phase_484_, v___y_491_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = lean_box(0);
if (lean_obj_tag(v_a_498_) == 1)
{
lean_object* v_val_500_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___x_517_; lean_object* v_env_518_; uint8_t v___x_519_; uint8_t v___x_520_; 
v_val_500_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_a_498_, 1);
v___x_517_ = lean_st_ref_get(v___y_491_);
v_env_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_env_518_);
lean_dec(v___x_517_);
v___x_519_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_518_, v_k_493_);
v___x_520_ = lean_bool_not(v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v_val_500_);
lean_dec(v_k_493_);
v_init_486_ = v___x_499_;
v_x_487_ = v_r_495_;
goto _start;
}
else
{
lean_object* v_options_522_; uint8_t v_hasTrace_523_; 
v_options_522_ = lean_ctor_get(v___y_490_, 2);
v_hasTrace_523_ = lean_ctor_get_uint8(v_options_522_, sizeof(void*)*1);
if (v_hasTrace_523_ == 0)
{
lean_dec(v_k_493_);
v___y_502_ = v___y_488_;
v___y_503_ = v___y_489_;
v___y_504_ = v___y_490_;
v___y_505_ = v___y_491_;
goto v___jp_501_;
}
else
{
lean_object* v_inheritedTraceOptions_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_inheritedTraceOptions_524_ = lean_ctor_get(v___y_490_, 13);
v___x_525_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_526_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_527_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_524_, v_options_522_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec(v_k_493_);
v___y_502_ = v___y_488_;
v___y_503_ = v___y_489_;
v___y_504_ = v___y_490_;
v___y_505_ = v___y_491_;
goto v___jp_501_;
}
else
{
lean_object* v_toSignature_528_; lean_object* v_name_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_toSignature_528_ = lean_ctor_get(v_decl_485_, 0);
v_name_529_ = lean_ctor_get(v_toSignature_528_, 0);
v___x_530_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
v___x_531_ = l_Lean_MessageData_ofName(v_k_493_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc(v_name_529_);
v___x_535_ = l_Lean_MessageData_ofName(v_name_529_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_525_, v___x_536_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_dec_ref_known(v___x_537_, 1);
v___y_502_ = v___y_488_;
v___y_503_ = v___y_489_;
v___y_504_ = v___y_490_;
v___y_505_ = v___y_491_;
goto v___jp_501_;
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_val_500_);
lean_dec(v_r_495_);
lean_dec_ref(v_decl_485_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
v___jp_501_:
{
uint8_t v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_484_);
v___x_507_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_506_, v_phase_484_, v_val_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_dec_ref_known(v___x_507_, 1);
v_init_486_ = v___x_499_;
v_x_487_ = v_r_495_;
goto _start;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_r_495_);
lean_dec_ref(v_decl_485_);
v_a_509_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_507_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
else
{
lean_dec(v_a_498_);
lean_dec(v_k_493_);
v_init_486_ = v___x_499_;
v_x_487_ = v_r_495_;
goto _start;
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_r_495_);
lean_dec(v_k_493_);
lean_dec_ref(v_decl_485_);
v_a_547_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_497_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_497_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_dec(v_r_495_);
lean_dec(v_k_493_);
lean_dec_ref(v_decl_485_);
return v___x_496_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_decl_485_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_init_486_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t v_pu_557_, uint8_t v_phase_558_, lean_object* v_decl_559_, lean_object* v_code_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = l_Lean_NameSet_empty;
v___x_567_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_557_, v_code_560_, v___x_566_);
v___x_568_ = lean_box(0);
v___x_569_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_558_, v_decl_559_, v___x_568_, v___x_567_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v___x_569_, 0);
lean_dec(v_unused_577_);
v___x_571_ = v___x_569_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_dec(v___x_569_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_568_);
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_568_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object* v_phase_586_, lean_object* v_decl_587_, lean_object* v_init_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v_phase_boxed_595_; lean_object* v_res_596_; 
v_phase_boxed_595_ = lean_unbox(v_phase_586_);
v_res_596_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_595_, v_decl_587_, v_init_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object* v_pu_597_, lean_object* v_phase_598_, lean_object* v_decl_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_pu_boxed_605_; uint8_t v_phase_boxed_606_; lean_object* v_res_607_; 
v_pu_boxed_605_ = lean_unbox(v_pu_597_);
v_phase_boxed_606_ = lean_unbox(v_phase_598_);
v_res_607_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_boxed_605_, v_phase_boxed_606_, v_decl_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_options_614_; lean_object* v_ref_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_options_614_ = lean_ctor_get(v___y_611_, 2);
v_ref_615_ = lean_ctor_get(v___y_611_, 5);
v___x_616_ = lean_st_ref_get(v___y_612_);
v___x_617_ = lean_st_ref_get(v___y_610_);
v___x_618_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_609_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_641_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_641_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_641_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_641_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_env_623_; lean_object* v_lctx_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_639_; 
v_env_623_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_616_);
v_lctx_624_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_617_, 1);
lean_dec(v_unused_640_);
v___x_626_ = v___x_617_;
v_isShared_627_ = v_isSharedCheck_639_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_lctx_624_);
lean_dec(v___x_617_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_639_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_628_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
v___x_629_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_624_, v___x_628_);
lean_dec_ref(v_lctx_624_);
v___x_630_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
lean_inc_ref(v_options_614_);
v___x_631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_631_, 0, v_env_623_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_ctor_set(v___x_631_, 2, v___x_629_);
lean_ctor_set(v___x_631_, 3, v_options_614_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 3);
lean_ctor_set(v___x_626_, 1, v_msg_608_);
lean_ctor_set(v___x_626_, 0, v___x_631_);
v___x_633_ = v___x_626_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_msg_608_);
v___x_633_ = v_reuseFailAlloc_638_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_inc(v_ref_615_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_ref_615_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 1);
lean_ctor_set(v___x_621_, 0, v___x_634_);
v___x_636_ = v___x_621_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v___x_617_);
lean_dec(v___x_616_);
lean_dec_ref(v_msg_608_);
v_a_642_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_618_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_618_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_658_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_666_, v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
return v_res_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_675_, lean_object* v_opt_676_){
_start:
{
lean_object* v_name_677_; lean_object* v_defValue_678_; lean_object* v_map_679_; lean_object* v___x_680_; 
v_name_677_ = lean_ctor_get(v_opt_676_, 0);
v_defValue_678_ = lean_ctor_get(v_opt_676_, 1);
v_map_679_ = lean_ctor_get(v_opts_675_, 0);
v___x_680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_679_, v_name_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
uint8_t v___x_681_; 
v___x_681_ = lean_unbox(v_defValue_678_);
return v___x_681_;
}
else
{
lean_object* v_val_682_; 
v_val_682_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_682_);
lean_dec_ref_known(v___x_680_, 1);
if (lean_obj_tag(v_val_682_) == 1)
{
uint8_t v_v_683_; 
v_v_683_ = lean_ctor_get_uint8(v_val_682_, 0);
lean_dec_ref_known(v_val_682_, 0);
return v_v_683_;
}
else
{
uint8_t v___x_684_; 
lean_dec(v_val_682_);
v___x_684_ = lean_unbox(v_defValue_678_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_685_, lean_object* v_opt_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_685_, v_opt_686_);
lean_dec_ref(v_opt_686_);
lean_dec_ref(v_opts_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_689_, lean_object* v_v_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
if (lean_obj_tag(v_v_690_) == 0)
{
lean_object* v_code_697_; lean_object* v___x_698_; 
v_code_697_ = lean_ctor_get(v_v_690_, 0);
lean_inc_ref(v_code_697_);
lean_dec_ref_known(v_v_690_, 1);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
v___x_698_ = lean_apply_7(v_f_689_, v_code_697_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, lean_box(0));
return v___x_698_;
}
else
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_f_689_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_v_690_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_v_690_, 0);
lean_dec(v_unused_708_);
v___x_700_ = v_v_690_;
v_isShared_701_ = v_isSharedCheck_707_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_v_690_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_707_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___y_691_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
lean_ctor_set(v___x_700_, 0, v___x_703_);
v___x_705_ = v___x_700_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_709_, lean_object* v_v_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_709_, v_v_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_718_, lean_object* v_f_719_, lean_object* v_v_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_719_, v_v_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_728_, lean_object* v_f_729_, lean_object* v_v_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v_pu_boxed_737_; lean_object* v_res_738_; 
v_pu_boxed_737_ = lean_unbox(v_pu_728_);
v_res_738_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_737_, v_f_729_, v_v_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_738_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_741_ = l_Lean_stringToMessageData(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_772_, lean_object* v_origDecl_773_, uint8_t v_isMeta_774_, uint8_t v_isPublic_775_, lean_object* v_init_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_k_784_; lean_object* v_l_785_; lean_object* v_r_786_; lean_object* v___x_787_; 
v_k_784_ = lean_ctor_get(v_x_777_, 1);
lean_inc(v_k_784_);
v_l_785_ = lean_ctor_get(v_x_777_, 3);
lean_inc(v_l_785_);
v_r_786_ = lean_ctor_get(v_x_777_, 4);
lean_inc(v_r_786_);
lean_dec_ref_known(v_x_777_, 5);
lean_inc_ref(v_origDecl_773_);
v___x_787_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_772_, v_origDecl_773_, v_isMeta_774_, v_isPublic_775_, v_init_776_, v_l_785_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v_snd_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_1094_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v_snd_789_ = lean_ctor_get(v_a_788_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_a_788_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_a_788_, 0);
lean_dec(v_unused_1095_);
v___x_791_ = v_a_788_;
v_isShared_792_ = v_isSharedCheck_1094_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_789_);
lean_dec(v_a_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_1094_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___x_850_; uint8_t v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; 
v___x_793_ = lean_box(0);
v___x_850_ = l_Lean_NameSet_contains(v_snd_789_, v_k_784_);
if (v___x_850_ == 0)
{
lean_object* v___x_880_; lean_object* v_env_881_; lean_object* v___y_883_; lean_object* v___y_884_; uint8_t v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; uint8_t v___y_924_; uint8_t v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; uint8_t v___y_940_; lean_object* v___y_941_; uint8_t v___y_942_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; uint8_t v___y_999_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___x_1015_; 
v___x_880_ = lean_st_ref_get(v___y_782_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_881_);
lean_dec(v___x_880_);
lean_inc(v_k_784_);
v___x_1015_ = l_Lean_NameSet_insert(v_snd_789_, v_k_784_);
if (v_isMeta_774_ == 0)
{
v___y_1005_ = v___x_1015_;
v___y_1006_ = v___y_779_;
v___y_1007_ = v___y_780_;
v___y_1008_ = v___y_781_;
v___y_1009_ = v___y_782_;
goto v___jp_1004_;
}
else
{
if (v_isPublic_775_ == 0)
{
v___y_1005_ = v___x_1015_;
v___y_1006_ = v___y_779_;
v___y_1007_ = v___y_780_;
v___y_1008_ = v___y_781_;
v___y_1009_ = v___y_782_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_881_, v_k_784_);
if (lean_obj_tag(v___x_1016_) == 1)
{
lean_object* v_val_1017_; uint8_t v___x_1018_; 
v_val_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v___x_1016_, 1);
lean_inc(v_k_784_);
lean_inc_ref(v_env_881_);
v___x_1018_ = l_Lean_isMarkedMeta(v_env_881_, v_k_784_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; uint8_t v___y_1021_; lean_object* v_modules_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1019_ = l_Lean_Environment_header(v_env_881_);
v_modules_1049_ = lean_ctor_get(v___x_1019_, 3);
lean_inc_ref(v_modules_1049_);
v___x_1050_ = lean_array_get_size(v_modules_1049_);
v___x_1051_ = lean_nat_dec_lt(v_val_1017_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_modules_1049_);
v___y_1021_ = v___x_1018_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1052_; lean_object* v_toImport_1053_; uint8_t v_isExported_1054_; uint8_t v___x_1055_; 
v___x_1052_ = lean_array_fget(v_modules_1049_, v_val_1017_);
lean_dec_ref(v_modules_1049_);
v_toImport_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_toImport_1053_);
lean_dec(v___x_1052_);
v_isExported_1054_ = lean_ctor_get_uint8(v_toImport_1053_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1053_);
v___x_1055_ = lean_bool_not(v_isExported_1054_);
v___y_1021_ = v___x_1055_;
goto v___jp_1020_;
}
v___jp_1020_:
{
if (v___y_1021_ == 0)
{
lean_dec_ref(v___x_1019_);
lean_dec(v_val_1017_);
v___y_1005_ = v___x_1015_;
v___y_1006_ = v___y_779_;
v___y_1007_ = v___y_780_;
v___y_1008_ = v___y_781_;
v___y_1009_ = v___y_782_;
goto v___jp_1004_;
}
else
{
lean_object* v_toSignature_1022_; lean_object* v_name_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v___x_1015_);
lean_dec_ref(v_env_881_);
lean_del_object(v___x_791_);
lean_dec(v_r_786_);
v_toSignature_1022_ = lean_ctor_get(v_origDecl_773_, 0);
lean_inc_ref(v_toSignature_1022_);
lean_dec_ref(v_origDecl_773_);
v_name_1023_ = lean_ctor_get(v_toSignature_1022_, 0);
lean_inc(v_name_1023_);
lean_dec_ref(v_toSignature_1022_);
v___x_1024_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1025_ = l_Lean_MessageData_ofConstName(v_name_1023_, v___x_1018_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_ofConstName(v_k_784_, v___x_1018_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1019_);
v___x_1035_ = lean_array_get(v___x_1033_, v___x_1034_, v_val_1017_);
lean_dec(v_val_1017_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_MessageData_ofName(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1032_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1039_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v___x_1056_; uint8_t v___y_1058_; lean_object* v_modules_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1056_ = l_Lean_Environment_header(v_env_881_);
v_modules_1086_ = lean_ctor_get(v___x_1056_, 3);
lean_inc_ref(v_modules_1086_);
v___x_1087_ = lean_array_get_size(v_modules_1086_);
v___x_1088_ = lean_nat_dec_lt(v_val_1017_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v_modules_1086_);
v___y_1058_ = v___x_850_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1089_; lean_object* v_toImport_1090_; uint8_t v_isExported_1091_; uint8_t v___x_1092_; 
v___x_1089_ = lean_array_fget(v_modules_1086_, v_val_1017_);
lean_dec_ref(v_modules_1086_);
v_toImport_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_toImport_1090_);
lean_dec(v___x_1089_);
v_isExported_1091_ = lean_ctor_get_uint8(v_toImport_1090_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1090_);
v___x_1092_ = lean_bool_not(v_isExported_1091_);
v___y_1058_ = v___x_1092_;
goto v___jp_1057_;
}
v___jp_1057_:
{
if (v___y_1058_ == 0)
{
lean_dec_ref(v___x_1056_);
lean_dec(v_val_1017_);
v___y_1005_ = v___x_1015_;
v___y_1006_ = v___y_779_;
v___y_1007_ = v___y_780_;
v___y_1008_ = v___y_781_;
v___y_1009_ = v___y_782_;
goto v___jp_1004_;
}
else
{
lean_object* v_toSignature_1059_; lean_object* v_name_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v___x_1015_);
lean_dec_ref(v_env_881_);
lean_del_object(v___x_791_);
lean_dec(v_r_786_);
v_toSignature_1059_ = lean_ctor_get(v_origDecl_773_, 0);
lean_inc_ref(v_toSignature_1059_);
lean_dec_ref(v_origDecl_773_);
v_name_1060_ = lean_ctor_get(v_toSignature_1059_, 0);
lean_inc(v_name_1060_);
lean_dec_ref(v_toSignature_1059_);
v___x_1061_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1062_ = l_Lean_MessageData_ofConstName(v_name_1060_, v___x_850_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_ofConstName(v_k_784_, v___x_850_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1056_);
v___x_1072_ = lean_array_get(v___x_1070_, v___x_1071_, v_val_1017_);
lean_dec(v_val_1017_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = l_Lean_MessageData_ofName(v___x_1072_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1069_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1076_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1016_);
v___y_1005_ = v___x_1015_;
v___y_1006_ = v___y_779_;
v___y_1007_ = v___y_780_;
v___y_1008_ = v___y_781_;
v___y_1009_ = v___y_782_;
goto v___jp_1004_;
}
}
}
v___jp_882_:
{
if (v___y_889_ == 0)
{
lean_dec_ref(v_env_881_);
lean_del_object(v___x_791_);
v___y_839_ = v___y_885_;
v___y_840_ = v___y_888_;
v___y_841_ = v___y_883_;
v___y_842_ = v___y_886_;
v___y_843_ = v___y_887_;
v___y_844_ = v___y_884_;
goto v___jp_838_;
}
else
{
uint8_t v___x_890_; 
v___x_890_ = lean_bool_not(v_isMeta_774_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_env_881_);
lean_del_object(v___x_791_);
v___y_839_ = v___y_885_;
v___y_840_ = v___y_888_;
v___y_841_ = v___y_883_;
v___y_842_ = v___y_886_;
v___y_843_ = v___y_887_;
v___y_844_ = v___y_884_;
goto v___jp_838_;
}
else
{
lean_object* v___x_891_; 
lean_dec(v_r_786_);
v___x_891_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_881_, v_k_784_);
if (lean_obj_tag(v___x_891_) == 1)
{
lean_object* v_val_892_; uint8_t v___x_893_; uint8_t v___x_894_; 
v_val_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v___x_891_, 1);
lean_inc(v_k_784_);
lean_inc_ref(v_env_881_);
v___x_893_ = l_Lean_isMarkedMeta(v_env_881_, v_k_784_);
v___x_894_ = lean_bool_not(v___x_893_);
if (v___x_894_ == 0)
{
lean_dec(v_val_892_);
lean_dec_ref(v_env_881_);
v___y_852_ = v___y_885_;
v___y_853_ = v___y_888_;
v___y_854_ = v___y_883_;
v___y_855_ = v___y_886_;
v___y_856_ = v___y_887_;
v___y_857_ = v___y_884_;
goto v___jp_851_;
}
else
{
lean_object* v_toSignature_895_; lean_object* v_name_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_888_);
lean_del_object(v___x_791_);
v_toSignature_895_ = lean_ctor_get(v_origDecl_773_, 0);
lean_inc_ref(v_toSignature_895_);
lean_dec_ref(v_origDecl_773_);
v_name_896_ = lean_ctor_get(v_toSignature_895_, 0);
lean_inc(v_name_896_);
lean_dec_ref(v_toSignature_895_);
v___x_897_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_898_ = l_Lean_MessageData_ofConstName(v_name_896_, v___x_850_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_MessageData_ofConstName(v_k_784_, v___x_850_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_box(0);
v___x_907_ = l_Lean_Environment_header(v_env_881_);
lean_dec_ref(v_env_881_);
v___x_908_ = l_Lean_EnvironmentHeader_moduleNames(v___x_907_);
v___x_909_ = lean_array_get(v___x_906_, v___x_908_, v_val_892_);
lean_dec(v_val_892_);
lean_dec_ref(v___x_908_);
v___x_910_ = l_Lean_MessageData_ofName(v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_905_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_913_, v___y_883_, v___y_886_, v___y_887_, v___y_884_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_dec(v___x_891_);
lean_dec_ref(v_env_881_);
v___y_852_ = v___y_885_;
v___y_853_ = v___y_888_;
v___y_854_ = v___y_883_;
v___y_855_ = v___y_886_;
v___y_856_ = v___y_887_;
v___y_857_ = v___y_884_;
goto v___jp_851_;
}
}
}
}
v___jp_923_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_bool_not(v___y_925_);
if (v___x_931_ == 0)
{
v___y_883_ = v___y_927_;
v___y_884_ = v___y_930_;
v___y_885_ = v___y_924_;
v___y_886_ = v___y_928_;
v___y_887_ = v___y_929_;
v___y_888_ = v___y_926_;
v___y_889_ = v___x_931_;
goto v___jp_882_;
}
else
{
uint8_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = 1;
v___x_933_ = l_Lean_instBEqIRPhases_beq(v___y_924_, v___x_932_);
v___y_883_ = v___y_927_;
v___y_884_ = v___y_930_;
v___y_885_ = v___y_924_;
v___y_886_ = v___y_928_;
v___y_887_ = v___y_929_;
v___y_888_ = v___y_926_;
v___y_889_ = v___x_933_;
goto v___jp_882_;
}
}
v___jp_934_:
{
if (v___y_942_ == 0)
{
v___y_924_ = v___y_935_;
v___y_925_ = v___y_940_;
v___y_926_ = v___y_937_;
v___y_927_ = v___y_936_;
v___y_928_ = v___y_939_;
v___y_929_ = v___y_938_;
v___y_930_ = v___y_941_;
goto v___jp_923_;
}
else
{
if (v_isMeta_774_ == 0)
{
v___y_924_ = v___y_935_;
v___y_925_ = v___y_940_;
v___y_926_ = v___y_937_;
v___y_927_ = v___y_936_;
v___y_928_ = v___y_939_;
v___y_929_ = v___y_938_;
v___y_930_ = v___y_941_;
goto v___jp_923_;
}
else
{
lean_object* v___x_943_; 
lean_dec(v___y_937_);
lean_del_object(v___x_791_);
lean_dec(v_r_786_);
v___x_943_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_881_, v_k_784_);
if (lean_obj_tag(v___x_943_) == 1)
{
lean_object* v_toSignature_944_; lean_object* v_val_945_; lean_object* v_name_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_toSignature_944_ = lean_ctor_get(v_origDecl_773_, 0);
lean_inc_ref(v_toSignature_944_);
lean_dec_ref(v_origDecl_773_);
v_val_945_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v___x_943_, 1);
v_name_946_ = lean_ctor_get(v_toSignature_944_, 0);
lean_inc(v_name_946_);
lean_dec_ref(v_toSignature_944_);
v___x_947_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_948_ = l_Lean_MessageData_ofConstName(v_name_946_, v___x_850_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_MessageData_ofConstName(v_k_784_, v___x_850_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_Environment_header(v_env_881_);
lean_dec_ref(v_env_881_);
v___x_958_ = l_Lean_EnvironmentHeader_moduleNames(v___x_957_);
v___x_959_ = lean_array_get(v___x_956_, v___x_958_, v_val_945_);
lean_dec(v_val_945_);
lean_dec_ref(v___x_958_);
v___x_960_ = l_Lean_MessageData_ofName(v___x_959_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_955_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_963_, v___y_936_, v___y_939_, v___y_938_, v___y_941_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v_toSignature_973_; lean_object* v_name_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v___x_943_);
lean_dec_ref(v_env_881_);
v_toSignature_973_ = lean_ctor_get(v_origDecl_773_, 0);
lean_inc_ref(v_toSignature_973_);
lean_dec_ref(v_origDecl_773_);
v_name_974_ = lean_ctor_get(v_toSignature_973_, 0);
lean_inc(v_name_974_);
lean_dec_ref(v_toSignature_973_);
v___x_975_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_976_ = l_Lean_MessageData_ofConstName(v_name_974_, v___x_850_);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l_Lean_MessageData_ofConstName(v_k_784_, v___x_850_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_983_, v___y_936_, v___y_939_, v___y_938_, v___y_941_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
v___jp_993_:
{
uint8_t v___x_1000_; uint8_t v___x_1001_; 
lean_inc(v_k_784_);
lean_inc_ref(v_env_881_);
v___x_1000_ = l_Lean_getIRPhases(v_env_881_, v_k_784_);
v___x_1001_ = lean_bool_not(v___y_999_);
if (v___x_1001_ == 0)
{
v___y_935_ = v___x_1000_;
v___y_936_ = v___y_995_;
v___y_937_ = v___y_994_;
v___y_938_ = v___y_997_;
v___y_939_ = v___y_996_;
v___y_940_ = v___y_999_;
v___y_941_ = v___y_998_;
v___y_942_ = v___x_1001_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = 0;
v___x_1003_ = l_Lean_instBEqIRPhases_beq(v___x_1000_, v___x_1002_);
v___y_935_ = v___x_1000_;
v___y_936_ = v___y_995_;
v___y_937_ = v___y_994_;
v___y_938_ = v___y_997_;
v___y_939_ = v___y_996_;
v___y_940_ = v___y_999_;
v___y_941_ = v___y_998_;
v___y_942_ = v___x_1003_;
goto v___jp_934_;
}
}
v___jp_1004_:
{
lean_object* v_options_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_options_1010_ = lean_ctor_get(v___y_1008_, 2);
v___x_1011_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_1012_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
v___y_994_ = v___y_1005_;
v___y_995_ = v___y_1006_;
v___y_996_ = v___y_1007_;
v___y_997_ = v___y_1008_;
v___y_998_ = v___y_1009_;
v___y_999_ = v___x_1012_;
goto v___jp_993_;
}
else
{
uint8_t v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = l_Lean_Environment_isImportedConst(v_env_881_, v_k_784_);
v___x_1014_ = lean_bool_not(v___x_1013_);
v___y_994_ = v___y_1005_;
v___y_995_ = v___y_1006_;
v___y_996_ = v___y_1007_;
v___y_997_ = v___y_1008_;
v___y_998_ = v___y_1009_;
v___y_999_ = v___x_1014_;
goto v___jp_993_;
}
}
}
else
{
lean_del_object(v___x_791_);
lean_dec(v_k_784_);
v_init_776_ = v___x_793_;
v_x_777_ = v_r_786_;
v___y_778_ = v_snd_789_;
goto _start;
}
v___jp_794_:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_797_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; uint8_t v___x_802_; lean_object* v___x_803_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = lean_unbox(v_a_801_);
v___x_803_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_784_, v___x_802_, v___y_799_);
lean_dec(v_k_784_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
if (lean_obj_tag(v_a_804_) == 1)
{
lean_object* v_val_805_; uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_val_805_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_804_, 1);
v___x_806_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
v___x_807_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_806_);
v___x_808_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_807_, v_val_805_, v_pu_772_);
lean_dec(v_val_805_);
lean_inc_ref(v_origDecl_773_);
v___x_809_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_772_, v_origDecl_773_, v_isMeta_774_, v_isPublic_775_, v___x_808_, v___y_795_, v___y_797_, v___y_796_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_snd_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_snd_811_ = lean_ctor_get(v_a_810_, 1);
lean_inc(v_snd_811_);
lean_dec(v_a_810_);
v_init_776_ = v___x_793_;
v_x_777_ = v_r_786_;
v___y_778_ = v_snd_811_;
goto _start;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_r_786_);
lean_dec_ref(v_origDecl_773_);
v_a_813_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_809_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_809_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
else
{
lean_dec(v_a_804_);
lean_dec(v_a_801_);
v_init_776_ = v___x_793_;
v_x_777_ = v_r_786_;
v___y_778_ = v___y_795_;
goto _start;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_801_);
lean_dec(v___y_795_);
lean_dec(v_r_786_);
lean_dec_ref(v_origDecl_773_);
v_a_822_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_803_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_803_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
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
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v___y_795_);
lean_dec(v_r_786_);
lean_dec(v_k_784_);
lean_dec_ref(v_origDecl_773_);
v_a_830_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_800_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_800_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
v___jp_838_:
{
uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 2;
v___x_846_ = l_Lean_instBEqIRPhases_beq(v___y_839_, v___x_845_);
if (v___x_846_ == 0)
{
if (v_isPublic_775_ == 0)
{
lean_dec(v_k_784_);
v_init_776_ = v___x_793_;
v_x_777_ = v_r_786_;
v___y_778_ = v___y_840_;
goto _start;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_isPrivateName(v_k_784_);
if (v___x_848_ == 0)
{
lean_dec(v_k_784_);
v_init_776_ = v___x_793_;
v_x_777_ = v_r_786_;
v___y_778_ = v___y_840_;
goto _start;
}
else
{
v___y_795_ = v___y_840_;
v___y_796_ = v___y_842_;
v___y_797_ = v___y_841_;
v___y_798_ = v___y_843_;
v___y_799_ = v___y_844_;
goto v___jp_794_;
}
}
}
else
{
v___y_795_ = v___y_840_;
v___y_796_ = v___y_842_;
v___y_797_ = v___y_841_;
v___y_798_ = v___y_843_;
v___y_799_ = v___y_844_;
goto v___jp_794_;
}
}
v___jp_851_:
{
lean_object* v_toSignature_858_; lean_object* v_name_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec(v___y_853_);
v_toSignature_858_ = lean_ctor_get(v_origDecl_773_, 0);
lean_inc_ref(v_toSignature_858_);
lean_dec_ref(v_origDecl_773_);
v_name_859_ = lean_ctor_get(v_toSignature_858_, 0);
lean_inc(v_name_859_);
lean_dec_ref(v_toSignature_858_);
v___x_860_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_861_ = l_Lean_MessageData_ofConstName(v_name_859_, v___x_850_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 7);
lean_ctor_set(v___x_791_, 1, v___x_861_);
lean_ctor_set(v___x_791_, 0, v___x_860_);
v___x_863_ = v___x_791_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_861_);
v___x_863_ = v_reuseFailAlloc_879_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v___x_864_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_MessageData_ofConstName(v_k_784_, v___x_850_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_869_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
else
{
lean_dec(v_r_786_);
lean_dec(v_k_784_);
lean_dec_ref(v_origDecl_773_);
return v___x_787_;
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_origDecl_773_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_init_776_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___y_778_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t v_pu_1099_, lean_object* v_origDecl_1100_, uint8_t v_isMeta_1101_, uint8_t v_isPublic_1102_, lean_object* v_code_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1110_ = l_Lean_NameSet_empty;
v___x_1111_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_1099_, v_code_1103_, v___x_1110_);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_1099_, v_origDecl_1100_, v_isMeta_1101_, v_isPublic_1102_, v___x_1112_, v___x_1111_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1130_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1130_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1130_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_snd_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v_snd_1118_ = lean_ctor_get(v_a_1114_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_a_1114_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_a_1114_, 0);
lean_dec(v_unused_1129_);
v___x_1120_ = v_a_1114_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_snd_1118_);
lean_dec(v_a_1114_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1112_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_snd_1118_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1123_);
v___x_1125_ = v___x_1116_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1113_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1113_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object* v_pu_1139_, lean_object* v_origDecl_1140_, lean_object* v_isMeta_1141_, lean_object* v_isPublic_1142_, lean_object* v_code_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_pu_boxed_1150_; uint8_t v_isMeta_boxed_1151_; uint8_t v_isPublic_boxed_1152_; lean_object* v_res_1153_; 
v_pu_boxed_1150_ = lean_unbox(v_pu_1139_);
v_isMeta_boxed_1151_ = lean_unbox(v_isMeta_1141_);
v_isPublic_boxed_1152_ = lean_unbox(v_isPublic_1142_);
v_res_1153_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_boxed_1150_, v_origDecl_1140_, v_isMeta_boxed_1151_, v_isPublic_boxed_1152_, v_code_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t v_pu_1154_, lean_object* v_origDecl_1155_, uint8_t v_isMeta_1156_, uint8_t v_isPublic_1157_, lean_object* v_decl_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_value_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v_value_1165_ = lean_ctor_get(v_decl_1158_, 1);
lean_inc_ref(v_value_1165_);
lean_dec_ref(v_decl_1158_);
v___x_1166_ = lean_box(v_pu_1154_);
v___x_1167_ = lean_box(v_isMeta_1156_);
v___x_1168_ = lean_box(v_isPublic_1157_);
v___f_1169_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1169_, 0, v___x_1166_);
lean_closure_set(v___f_1169_, 1, v_origDecl_1155_);
lean_closure_set(v___f_1169_, 2, v___x_1167_);
lean_closure_set(v___f_1169_, 3, v___x_1168_);
v___x_1170_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_1169_, v_value_1165_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object* v_pu_1171_, lean_object* v_origDecl_1172_, lean_object* v_isMeta_1173_, lean_object* v_isPublic_1174_, lean_object* v_decl_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
uint8_t v_pu_boxed_1182_; uint8_t v_isMeta_boxed_1183_; uint8_t v_isPublic_boxed_1184_; lean_object* v_res_1185_; 
v_pu_boxed_1182_ = lean_unbox(v_pu_1171_);
v_isMeta_boxed_1183_ = lean_unbox(v_isMeta_1173_);
v_isPublic_boxed_1184_ = lean_unbox(v_isPublic_1174_);
v_res_1185_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_boxed_1182_, v_origDecl_1172_, v_isMeta_boxed_1183_, v_isPublic_boxed_1184_, v_decl_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object* v_pu_1186_, lean_object* v_origDecl_1187_, lean_object* v_isMeta_1188_, lean_object* v_isPublic_1189_, lean_object* v_init_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_pu_boxed_1198_; uint8_t v_isMeta_boxed_1199_; uint8_t v_isPublic_boxed_1200_; lean_object* v_res_1201_; 
v_pu_boxed_1198_ = lean_unbox(v_pu_1186_);
v_isMeta_boxed_1199_ = lean_unbox(v_isMeta_1188_);
v_isPublic_boxed_1200_ = lean_unbox(v_isPublic_1189_);
v_res_1201_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_1198_, v_origDecl_1187_, v_isMeta_boxed_1199_, v_isPublic_boxed_1200_, v_init_1190_, v_x_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object* v_opt_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_options_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_options_1205_ = lean_ctor_get(v___y_1203_, 2);
v___x_1206_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1205_, v_opt_1202_);
v___x_1207_ = lean_box(v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1209_, v___y_1210_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v_opt_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1213_, lean_object* v_origDecl_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1282_; 
v___x_1220_ = lean_st_ref_get(v_a_1218_);
v___x_1221_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1222_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1221_, v_a_1217_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1282_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1282_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1281_; 
v___x_1227_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1228_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1227_, v_a_1217_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1281_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1281_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint8_t v___y_1239_; lean_object* v_env_1276_; lean_object* v___x_1277_; uint8_t v_isModule_1278_; uint8_t v___x_1279_; 
v_env_1276_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_env_1276_);
lean_dec(v___x_1220_);
v___x_1277_ = l_Lean_Environment_header(v_env_1276_);
lean_dec_ref(v_env_1276_);
v_isModule_1278_ = lean_ctor_get_uint8(v___x_1277_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_bool_not(v_isModule_1278_);
if (v___x_1279_ == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_unbox(v_a_1223_);
lean_dec(v_a_1223_);
v___y_1239_ = v___x_1280_;
goto v___jp_1238_;
}
else
{
lean_dec(v_a_1223_);
v___y_1239_ = v___x_1279_;
goto v___jp_1238_;
}
v___jp_1233_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_box(0);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
v___jp_1238_:
{
if (v___y_1239_ == 0)
{
uint8_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = lean_unbox(v_a_1229_);
lean_dec(v_a_1229_);
v___x_1241_ = lean_bool_not(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v_toSignature_1243_; lean_object* v_env_1244_; lean_object* v_name_1245_; uint8_t v___x_1246_; uint8_t v___x_1247_; uint8_t v___x_1248_; 
lean_del_object(v___x_1231_);
v___x_1242_ = lean_st_ref_get(v_a_1218_);
v_toSignature_1243_ = lean_ctor_get(v_origDecl_1214_, 0);
v_env_1244_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_env_1244_);
lean_dec(v___x_1242_);
v_name_1245_ = lean_ctor_get(v_toSignature_1243_, 0);
lean_inc(v_name_1245_);
v___x_1246_ = l_Lean_getIRPhases(v_env_1244_, v_name_1245_);
v___x_1247_ = 2;
v___x_1248_ = l_Lean_instBEqIRPhases_beq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
uint8_t v___x_1249_; uint8_t v___x_1250_; uint8_t v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_del_object(v___x_1225_);
v___x_1249_ = l_Lean_isPrivateName(v_name_1245_);
v___x_1250_ = lean_bool_not(v___x_1249_);
v___x_1251_ = 1;
v___x_1252_ = l_Lean_instBEqIRPhases_beq(v___x_1246_, v___x_1251_);
v___x_1253_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1214_);
v___x_1254_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1213_, v_origDecl_1214_, v___x_1252_, v___x_1250_, v_origDecl_1214_, v___x_1253_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1263_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; lean_object* v___x_1261_; 
v_fst_1259_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_fst_1259_);
lean_dec(v_a_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_fst_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_fst_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v_a_1264_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1254_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1254_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_dec_ref(v_origDecl_1214_);
v___x_1272_ = lean_box(0);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1272_);
v___x_1274_ = v___x_1225_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_del_object(v___x_1225_);
lean_dec_ref(v_origDecl_1214_);
goto v___jp_1233_;
}
}
else
{
lean_dec(v_a_1229_);
lean_del_object(v___x_1225_);
lean_dec_ref(v_origDecl_1214_);
goto v___jp_1233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1283_, lean_object* v_origDecl_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_pu_boxed_1290_; lean_object* v_res_1291_; 
v_pu_boxed_1290_ = lean_unbox(v_pu_1283_);
v_res_1291_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1290_, v_origDecl_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1292_, v___y_1295_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_opt_1299_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0(uint8_t v_isExporting_1306_, lean_object* v___x_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v_env_1316_; lean_object* v_nextMacroScope_1317_; lean_object* v_ngen_1318_; lean_object* v_auxDeclNGen_1319_; lean_object* v_traceState_1320_; lean_object* v_messages_1321_; lean_object* v_infoState_1322_; lean_object* v_snapshotTasks_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1335_; 
v___x_1315_ = lean_st_ref_take(v___y_1313_);
v_env_1316_ = lean_ctor_get(v___x_1315_, 0);
v_nextMacroScope_1317_ = lean_ctor_get(v___x_1315_, 1);
v_ngen_1318_ = lean_ctor_get(v___x_1315_, 2);
v_auxDeclNGen_1319_ = lean_ctor_get(v___x_1315_, 3);
v_traceState_1320_ = lean_ctor_get(v___x_1315_, 4);
v_messages_1321_ = lean_ctor_get(v___x_1315_, 6);
v_infoState_1322_ = lean_ctor_get(v___x_1315_, 7);
v_snapshotTasks_1323_ = lean_ctor_get(v___x_1315_, 8);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1315_, 5);
lean_dec(v_unused_1336_);
v___x_1325_ = v___x_1315_;
v_isShared_1326_ = v_isSharedCheck_1335_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_snapshotTasks_1323_);
lean_inc(v_infoState_1322_);
lean_inc(v_messages_1321_);
lean_inc(v_traceState_1320_);
lean_inc(v_auxDeclNGen_1319_);
lean_inc(v_ngen_1318_);
lean_inc(v_nextMacroScope_1317_);
lean_inc(v_env_1316_);
lean_dec(v___x_1315_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1335_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = l_Lean_Environment_setExporting(v_env_1316_, v_isExporting_1306_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 5, v___x_1307_);
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_nextMacroScope_1317_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_ngen_1318_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_auxDeclNGen_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_traceState_1320_);
lean_ctor_set(v_reuseFailAlloc_1334_, 5, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1334_, 6, v_messages_1321_);
lean_ctor_set(v_reuseFailAlloc_1334_, 7, v_infoState_1322_);
lean_ctor_set(v_reuseFailAlloc_1334_, 8, v_snapshotTasks_1323_);
v___x_1329_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = lean_st_ref_set(v___y_1313_, v___x_1329_);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___y_1309_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0___boxed(lean_object* v_isExporting_1337_, lean_object* v___x_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_isExporting_boxed_1346_; lean_object* v_res_1347_; 
v_isExporting_boxed_1346_ = lean_unbox(v_isExporting_1337_);
v_res_1347_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0(v_isExporting_boxed_1346_, v___x_1338_, v_x_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v_x_1339_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(lean_object* v___f_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v_a_x3f_1354_){
_start:
{
if (lean_obj_tag(v_a_x3f_1354_) == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_box(0);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1357_ = lean_apply_7(v___f_1348_, v___x_1356_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
return v___x_1357_;
}
else
{
lean_object* v_val_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v___y_1349_);
v_val_1358_ = lean_ctor_get(v_a_x3f_1354_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_a_x3f_1354_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1360_ = v_a_x3f_1354_;
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_val_1358_);
lean_dec(v_a_x3f_1354_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_fst_1362_; lean_object* v_snd_1363_; lean_object* v___x_1365_; 
v_fst_1362_ = lean_ctor_get(v_val_1358_, 0);
lean_inc(v_fst_1362_);
v_snd_1363_ = lean_ctor_get(v_val_1358_, 1);
lean_inc(v_snd_1363_);
lean_dec(v_val_1358_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_fst_1362_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1362_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1366_ = lean_apply_7(v___f_1348_, v___x_1365_, v_snd_1363_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1___boxed(lean_object* v___f_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v_a_x3f_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(v___f_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v_a_x3f_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(lean_object* v_x_1378_, uint8_t v_isExporting_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; lean_object* v_env_1387_; uint8_t v_isExporting_1388_; uint8_t v___y_1468_; lean_object* v___x_1470_; uint8_t v_isModule_1471_; uint8_t v___x_1472_; 
v___x_1386_ = lean_st_ref_get(v___y_1384_);
v_env_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_ref(v_env_1387_);
lean_dec(v___x_1386_);
v_isExporting_1388_ = lean_ctor_get_uint8(v_env_1387_, sizeof(void*)*8);
v___x_1470_ = l_Lean_Environment_header(v_env_1387_);
lean_dec_ref(v_env_1387_);
v_isModule_1471_ = lean_ctor_get_uint8(v___x_1470_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1470_);
v___x_1472_ = lean_bool_not(v_isModule_1471_);
if (v___x_1472_ == 0)
{
if (v_isExporting_1388_ == 0)
{
if (v_isExporting_1379_ == 0)
{
lean_object* v___x_1473_; 
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
v___x_1473_ = lean_apply_6(v_x_1378_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, lean_box(0));
return v___x_1473_;
}
else
{
goto v___jp_1389_;
}
}
else
{
v___y_1468_ = v_isExporting_1379_;
goto v___jp_1467_;
}
}
else
{
v___y_1468_ = v___x_1472_;
goto v___jp_1467_;
}
v___jp_1389_:
{
lean_object* v___x_1390_; lean_object* v_env_1391_; lean_object* v_nextMacroScope_1392_; lean_object* v_ngen_1393_; lean_object* v_auxDeclNGen_1394_; lean_object* v_traceState_1395_; lean_object* v_messages_1396_; lean_object* v_infoState_1397_; lean_object* v_snapshotTasks_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1465_; 
v___x_1390_ = lean_st_ref_take(v___y_1384_);
v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
v_nextMacroScope_1392_ = lean_ctor_get(v___x_1390_, 1);
v_ngen_1393_ = lean_ctor_get(v___x_1390_, 2);
v_auxDeclNGen_1394_ = lean_ctor_get(v___x_1390_, 3);
v_traceState_1395_ = lean_ctor_get(v___x_1390_, 4);
v_messages_1396_ = lean_ctor_get(v___x_1390_, 6);
v_infoState_1397_ = lean_ctor_get(v___x_1390_, 7);
v_snapshotTasks_1398_ = lean_ctor_get(v___x_1390_, 8);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1390_, 5);
lean_dec(v_unused_1466_);
v___x_1400_ = v___x_1390_;
v_isShared_1401_ = v_isSharedCheck_1465_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snapshotTasks_1398_);
lean_inc(v_infoState_1397_);
lean_inc(v_messages_1396_);
lean_inc(v_traceState_1395_);
lean_inc(v_auxDeclNGen_1394_);
lean_inc(v_ngen_1393_);
lean_inc(v_nextMacroScope_1392_);
lean_inc(v_env_1391_);
lean_dec(v___x_1390_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1465_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1402_ = l_Lean_Environment_setExporting(v_env_1391_, v_isExporting_1379_);
v___x_1403_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 5, v___x_1403_);
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1405_ = v___x_1400_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_nextMacroScope_1392_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_ngen_1393_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_auxDeclNGen_1394_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_traceState_1395_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_messages_1396_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_infoState_1397_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_snapshotTasks_1398_);
v___x_1405_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___f_1408_; lean_object* v_r_1409_; 
v___x_1406_ = lean_st_ref_set(v___y_1384_, v___x_1405_);
v___x_1407_ = lean_box(v_isExporting_1388_);
v___f_1408_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1408_, 0, v___x_1407_);
lean_closure_set(v___f_1408_, 1, v___x_1403_);
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
lean_inc(v___y_1380_);
v_r_1409_ = lean_apply_6(v_x_1378_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, lean_box(0));
if (lean_obj_tag(v_r_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1444_; 
v_a_1410_ = lean_ctor_get(v_r_1409_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_r_1409_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1412_ = v_r_1409_;
v_isShared_1413_ = v_isSharedCheck_1444_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v_r_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1444_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
lean_inc(v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 1);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(v___f_1408_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___x_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1434_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1434_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1434_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_fst_1421_; lean_object* v_snd_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1432_; 
v_fst_1421_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_fst_1421_);
lean_dec(v_a_1410_);
v_snd_1422_ = lean_ctor_get(v_a_1417_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1417_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_a_1417_, 0);
lean_dec(v_unused_1433_);
v___x_1424_ = v_a_1417_;
v_isShared_1425_ = v_isSharedCheck_1432_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_snd_1422_);
lean_dec(v_a_1417_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1432_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_fst_1421_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_fst_1421_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_snd_1422_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
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
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1410_);
v_a_1435_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1416_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1416_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v_r_1409_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v_r_1409_, 1);
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___lam__1(v___f_1408_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1447_, 0);
lean_dec(v_unused_1455_);
v___x_1449_ = v___x_1447_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___x_1447_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 1);
lean_ctor_set(v___x_1449_, 0, v_a_1445_);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1445_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1445_);
v_a_1456_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1447_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1447_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
}
v___jp_1467_:
{
if (v___y_1468_ == 0)
{
goto v___jp_1389_;
}
else
{
lean_object* v___x_1469_; 
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
v___x_1469_ = lean_apply_6(v_x_1378_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, lean_box(0));
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg___boxed(lean_object* v_x_1474_, lean_object* v_isExporting_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_isExporting_boxed_1482_; lean_object* v_res_1483_; 
v_isExporting_boxed_1482_ = lean_unbox(v_isExporting_1475_);
v_res_1483_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(v_x_1474_, v_isExporting_boxed_1482_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_00_u03b1_1484_, lean_object* v_x_1485_, uint8_t v_isExporting_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(v_x_1485_, v_isExporting_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_x_1495_, lean_object* v_isExporting_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_isExporting_boxed_1503_; lean_object* v_res_1504_; 
v_isExporting_boxed_1503_ = lean_unbox(v_isExporting_1496_);
v_res_1504_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_00_u03b1_1494_, v_x_1495_, v_isExporting_boxed_1503_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object* v_opt_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_options_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_options_1509_ = lean_ctor_get(v___y_1507_, 2);
v___x_1510_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1509_, v_opt_1505_);
v___x_1511_ = lean_box(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___y_1506_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_opt_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_opt_1514_, v___y_1515_, v___y_1516_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_opt_1514_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
if (lean_obj_tag(v_x_1520_) == 0)
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_box(0);
return v___x_1521_;
}
else
{
lean_object* v_key_1522_; lean_object* v_value_1523_; lean_object* v_tail_1524_; uint8_t v___x_1525_; 
v_key_1522_ = lean_ctor_get(v_x_1520_, 0);
v_value_1523_ = lean_ctor_get(v_x_1520_, 1);
v_tail_1524_ = lean_ctor_get(v_x_1520_, 2);
v___x_1525_ = lean_name_eq(v_key_1522_, v_a_1519_);
if (v___x_1525_ == 0)
{
v_x_1520_ = v_tail_1524_;
goto _start;
}
else
{
lean_object* v___x_1527_; 
lean_inc(v_value_1523_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_value_1523_);
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_a_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(v_a_1528_, v_x_1529_);
lean_dec(v_x_1529_);
lean_dec(v_a_1528_);
return v_res_1530_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1531_; uint64_t v___x_1532_; 
v___x_1531_ = lean_unsigned_to_nat(1723u);
v___x_1532_ = lean_uint64_of_nat(v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(lean_object* v_m_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_buckets_1535_; lean_object* v___x_1536_; uint64_t v___y_1538_; 
v_buckets_1535_ = lean_ctor_get(v_m_1533_, 1);
v___x_1536_ = lean_array_get_size(v_buckets_1535_);
if (lean_obj_tag(v_a_1534_) == 0)
{
uint64_t v___x_1552_; 
v___x_1552_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0);
v___y_1538_ = v___x_1552_;
goto v___jp_1537_;
}
else
{
uint64_t v_hash_1553_; 
v_hash_1553_ = lean_ctor_get_uint64(v_a_1534_, sizeof(void*)*2);
v___y_1538_ = v_hash_1553_;
goto v___jp_1537_;
}
v___jp_1537_:
{
uint64_t v___x_1539_; uint64_t v___x_1540_; uint64_t v_fold_1541_; uint64_t v___x_1542_; uint64_t v___x_1543_; uint64_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1539_ = 32ULL;
v___x_1540_ = lean_uint64_shift_right(v___y_1538_, v___x_1539_);
v_fold_1541_ = lean_uint64_xor(v___y_1538_, v___x_1540_);
v___x_1542_ = 16ULL;
v___x_1543_ = lean_uint64_shift_right(v_fold_1541_, v___x_1542_);
v___x_1544_ = lean_uint64_xor(v_fold_1541_, v___x_1543_);
v___x_1545_ = lean_uint64_to_usize(v___x_1544_);
v___x_1546_ = lean_usize_of_nat(v___x_1536_);
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_sub(v___x_1546_, v___x_1547_);
v___x_1549_ = lean_usize_land(v___x_1545_, v___x_1548_);
v___x_1550_ = lean_array_uget_borrowed(v_buckets_1535_, v___x_1549_);
v___x_1551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(v_a_1534_, v___x_1550_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___boxed(lean_object* v_m_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(v_m_1554_, v_a_1555_);
lean_dec(v_a_1555_);
lean_dec_ref(v_m_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(lean_object* v_cls_1557_, lean_object* v_msg_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_options_1565_; lean_object* v_ref_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_options_1565_ = lean_ctor_get(v___y_1562_, 2);
v_ref_1566_ = lean_ctor_get(v___y_1562_, 5);
v___x_1567_ = lean_st_ref_get(v___y_1563_);
v___x_1568_ = lean_st_ref_get(v___y_1561_);
v___x_1569_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1560_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1629_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1629_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1629_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_env_1574_; lean_object* v_lctx_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1627_; 
v_env_1574_ = lean_ctor_get(v___x_1567_, 0);
lean_inc_ref(v_env_1574_);
lean_dec(v___x_1567_);
v_lctx_1575_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1568_, 1);
lean_dec(v_unused_1628_);
v___x_1577_ = v___x_1568_;
v_isShared_1578_ = v_isSharedCheck_1627_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_lctx_1575_);
lean_dec(v___x_1568_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1627_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_traceState_1581_; lean_object* v_env_1582_; lean_object* v_nextMacroScope_1583_; lean_object* v_ngen_1584_; lean_object* v_auxDeclNGen_1585_; lean_object* v_cache_1586_; lean_object* v_messages_1587_; lean_object* v_infoState_1588_; lean_object* v_snapshotTasks_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1626_; 
v___x_1579_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_1580_ = lean_st_ref_take(v___y_1563_);
v_traceState_1581_ = lean_ctor_get(v___x_1580_, 4);
v_env_1582_ = lean_ctor_get(v___x_1580_, 0);
v_nextMacroScope_1583_ = lean_ctor_get(v___x_1580_, 1);
v_ngen_1584_ = lean_ctor_get(v___x_1580_, 2);
v_auxDeclNGen_1585_ = lean_ctor_get(v___x_1580_, 3);
v_cache_1586_ = lean_ctor_get(v___x_1580_, 5);
v_messages_1587_ = lean_ctor_get(v___x_1580_, 6);
v_infoState_1588_ = lean_ctor_get(v___x_1580_, 7);
v_snapshotTasks_1589_ = lean_ctor_get(v___x_1580_, 8);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1591_ = v___x_1580_;
v_isShared_1592_ = v_isSharedCheck_1626_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_snapshotTasks_1589_);
lean_inc(v_infoState_1588_);
lean_inc(v_messages_1587_);
lean_inc(v_cache_1586_);
lean_inc(v_traceState_1581_);
lean_inc(v_auxDeclNGen_1585_);
lean_inc(v_ngen_1584_);
lean_inc(v_nextMacroScope_1583_);
lean_inc(v_env_1582_);
lean_dec(v___x_1580_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1626_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
uint64_t v_tid_1593_; lean_object* v_traces_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1625_; 
v_tid_1593_ = lean_ctor_get_uint64(v_traceState_1581_, sizeof(void*)*1);
v_traces_1594_ = lean_ctor_get(v_traceState_1581_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_traceState_1581_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1596_ = v_traceState_1581_;
v_isShared_1597_ = v_isSharedCheck_1625_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_traces_1594_);
lean_dec(v_traceState_1581_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1625_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1598_ = lean_unbox(v_a_1570_);
lean_dec(v_a_1570_);
v___x_1599_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1575_, v___x_1598_);
lean_dec_ref(v_lctx_1575_);
lean_inc_ref(v_options_1565_);
v___x_1600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1600_, 0, v_env_1574_);
lean_ctor_set(v___x_1600_, 1, v___x_1579_);
lean_ctor_set(v___x_1600_, 2, v___x_1599_);
lean_ctor_set(v___x_1600_, 3, v_options_1565_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 3);
lean_ctor_set(v___x_1577_, 1, v_msg_1558_);
lean_ctor_set(v___x_1577_, 0, v___x_1600_);
v___x_1602_ = v___x_1577_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_msg_1558_);
v___x_1602_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; double v___x_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_1605_ = 0;
v___x_1606_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1607_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1607_, 0, v_cls_1557_);
lean_ctor_set(v___x_1607_, 1, v___x_1603_);
lean_ctor_set(v___x_1607_, 2, v___x_1606_);
lean_ctor_set_float(v___x_1607_, sizeof(void*)*3, v___x_1604_);
lean_ctor_set_float(v___x_1607_, sizeof(void*)*3 + 8, v___x_1604_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*3 + 16, v___x_1605_);
v___x_1608_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_1609_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1602_);
lean_ctor_set(v___x_1609_, 2, v___x_1608_);
lean_inc(v_ref_1566_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_ref_1566_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_PersistentArray_push___redArg(v_traces_1594_, v___x_1610_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1611_);
v___x_1613_ = v___x_1596_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1611_);
lean_ctor_set_uint64(v_reuseFailAlloc_1623_, sizeof(void*)*1, v_tid_1593_);
v___x_1613_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 4, v___x_1613_);
v___x_1615_ = v___x_1591_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_env_1582_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_nextMacroScope_1583_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_ngen_1584_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_auxDeclNGen_1585_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1622_, 5, v_cache_1586_);
lean_ctor_set(v_reuseFailAlloc_1622_, 6, v_messages_1587_);
lean_ctor_set(v_reuseFailAlloc_1622_, 7, v_infoState_1588_);
lean_ctor_set(v_reuseFailAlloc_1622_, 8, v_snapshotTasks_1589_);
v___x_1615_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1616_ = lean_st_ref_set(v___y_1563_, v___x_1615_);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___y_1559_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1618_);
v___x_1620_ = v___x_1572_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
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
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v___x_1568_);
lean_dec(v___x_1567_);
lean_dec(v___y_1559_);
lean_dec_ref(v_msg_1558_);
lean_dec(v_cls_1557_);
v_a_1630_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1569_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1569_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6___boxed(lean_object* v_cls_1638_, lean_object* v_msg_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(v_cls_1638_, v_msg_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_keys_1647_, lean_object* v_i_1648_, lean_object* v_k_1649_){
_start:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_array_get_size(v_keys_1647_);
v___x_1651_ = lean_nat_dec_lt(v_i_1648_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec(v_i_1648_);
return v___x_1651_;
}
else
{
lean_object* v_k_x27_1652_; uint8_t v___x_1653_; 
v_k_x27_1652_ = lean_array_fget_borrowed(v_keys_1647_, v_i_1648_);
v___x_1653_ = l_Lean_instBEqExtraModUse_beq(v_k_1649_, v_k_x27_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_add(v_i_1648_, v___x_1654_);
lean_dec(v_i_1648_);
v_i_1648_ = v___x_1655_;
goto _start;
}
else
{
lean_dec(v_i_1648_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1657_, lean_object* v_i_1658_, lean_object* v_k_1659_){
_start:
{
uint8_t v_res_1660_; lean_object* v_r_1661_; 
v_res_1660_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(v_keys_1657_, v_i_1658_, v_k_1659_);
lean_dec_ref(v_k_1659_);
lean_dec_ref(v_keys_1657_);
v_r_1661_ = lean_box(v_res_1660_);
return v_r_1661_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_x_1662_, size_t v_x_1663_, lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v_es_1665_; lean_object* v___x_1666_; size_t v___x_1667_; size_t v___x_1668_; lean_object* v_j_1669_; lean_object* v___x_1670_; 
v_es_1665_ = lean_ctor_get(v_x_1662_, 0);
v___x_1666_ = lean_box(2);
v___x_1667_ = ((size_t)31ULL);
v___x_1668_ = lean_usize_land(v_x_1663_, v___x_1667_);
v_j_1669_ = lean_usize_to_nat(v___x_1668_);
v___x_1670_ = lean_array_get_borrowed(v___x_1666_, v_es_1665_, v_j_1669_);
lean_dec(v_j_1669_);
switch(lean_obj_tag(v___x_1670_))
{
case 0:
{
lean_object* v_key_1671_; uint8_t v___x_1672_; 
v_key_1671_ = lean_ctor_get(v___x_1670_, 0);
v___x_1672_ = l_Lean_instBEqExtraModUse_beq(v_x_1664_, v_key_1671_);
return v___x_1672_;
}
case 1:
{
lean_object* v_node_1673_; size_t v___x_1674_; size_t v___x_1675_; 
v_node_1673_ = lean_ctor_get(v___x_1670_, 0);
v___x_1674_ = ((size_t)5ULL);
v___x_1675_ = lean_usize_shift_right(v_x_1663_, v___x_1674_);
v_x_1662_ = v_node_1673_;
v_x_1663_ = v___x_1675_;
goto _start;
}
default: 
{
uint8_t v___x_1677_; 
v___x_1677_ = 0;
return v___x_1677_;
}
}
}
else
{
lean_object* v_ks_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_ks_1678_ = lean_ctor_get(v_x_1662_, 0);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(v_ks_1678_, v___x_1679_, v_x_1664_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_x_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_){
_start:
{
size_t v_x_29544__boxed_1684_; uint8_t v_res_1685_; lean_object* v_r_1686_; 
v_x_29544__boxed_1684_ = lean_unbox_usize(v_x_1682_);
lean_dec(v_x_1682_);
v_res_1685_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(v_x_1681_, v_x_29544__boxed_1684_, v_x_1683_);
lean_dec_ref(v_x_1683_);
lean_dec_ref(v_x_1681_);
v_r_1686_ = lean_box(v_res_1685_);
return v_r_1686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
uint64_t v___x_1689_; size_t v___x_1690_; uint8_t v___x_1691_; 
v___x_1689_ = l_Lean_instHashableExtraModUse_hash(v_x_1688_);
v___x_1690_ = lean_uint64_to_usize(v___x_1689_);
v___x_1691_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(v_x_1687_, v___x_1690_, v_x_1688_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_1692_, lean_object* v_x_1693_){
_start:
{
uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_res_1694_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(v_x_1692_, v_x_1693_);
lean_dec_ref(v_x_1693_);
lean_dec_ref(v_x_1692_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__1));
v___x_1699_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__0));
v___x_1700_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1699_, v___x_1698_);
return v___x_1700_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__5));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__7));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1711_ = l_Lean_stringToMessageData(v___x_1710_);
return v___x_1711_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10(void){
_start:
{
lean_object* v_cls_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_cls_1712_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4));
v___x_1713_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1714_ = l_Lean_Name_append(v___x_1713_, v_cls_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__11));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__13));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(lean_object* v_mod_1725_, uint8_t v_isMeta_1726_, lean_object* v_hint_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v_env_1735_; uint8_t v_isExporting_1736_; lean_object* v___x_1737_; lean_object* v_env_1738_; lean_object* v___x_1739_; lean_object* v_entry_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___x_1772_; uint8_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1734_ = lean_st_ref_get(v___y_1732_);
v_env_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_env_1735_);
lean_dec(v___x_1734_);
v_isExporting_1736_ = lean_ctor_get_uint8(v_env_1735_, sizeof(void*)*8);
lean_dec_ref(v_env_1735_);
v___x_1737_ = lean_st_ref_get(v___y_1732_);
v_env_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_env_1738_);
lean_dec(v___x_1737_);
v___x_1739_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__2);
lean_inc(v_mod_1725_);
v_entry_1740_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1740_, 0, v_mod_1725_);
lean_ctor_set_uint8(v_entry_1740_, sizeof(void*)*1, v_isExporting_1736_);
lean_ctor_set_uint8(v_entry_1740_, sizeof(void*)*1 + 1, v_isMeta_1726_);
v___x_1741_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1742_ = lean_box(1);
v___x_1743_ = lean_box(0);
v___x_1772_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1739_, v___x_1741_, v_env_1738_, v___x_1742_, v___x_1743_);
v___x_1773_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(v___x_1772_, v_entry_1740_);
lean_dec(v___x_1772_);
v___x_1774_ = lean_bool_not(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec_ref_known(v_entry_1740_, 1);
lean_dec(v_hint_1727_);
lean_dec(v_mod_1725_);
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___y_1728_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
else
{
lean_object* v_options_1778_; uint8_t v_hasTrace_1779_; 
v_options_1778_ = lean_ctor_get(v___y_1731_, 2);
v_hasTrace_1779_ = lean_ctor_get_uint8(v_options_1778_, sizeof(void*)*1);
if (v_hasTrace_1779_ == 0)
{
lean_dec(v_hint_1727_);
lean_dec(v_mod_1725_);
v___y_1745_ = v___y_1728_;
v___y_1746_ = v___y_1732_;
goto v___jp_1744_;
}
else
{
lean_object* v_inheritedTraceOptions_1780_; lean_object* v_cls_1781_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_inheritedTraceOptions_1780_ = lean_ctor_get(v___y_1731_, 13);
v_cls_1781_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__4));
v___x_1803_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__10);
v___x_1804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1780_, v_options_1778_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec(v_hint_1727_);
lean_dec(v_mod_1725_);
v___y_1745_ = v___y_1728_;
v___y_1746_ = v___y_1732_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1805_; lean_object* v___y_1807_; 
v___x_1805_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__12);
if (v_isExporting_1736_ == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__17));
v___y_1807_ = v___x_1814_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__18));
v___y_1807_ = v___x_1815_;
goto v___jp_1806_;
}
v___jp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_inc_ref(v___y_1807_);
v___x_1808_ = l_Lean_stringToMessageData(v___y_1807_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1805_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__14);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
if (v_isMeta_1726_ == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__15));
v___y_1790_ = v___x_1811_;
v___y_1791_ = v___x_1812_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__16));
v___y_1790_ = v___x_1811_;
v___y_1791_ = v___x_1813_;
goto v___jp_1789_;
}
}
}
v___jp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___y_1783_);
lean_ctor_set(v___x_1785_, 1, v___y_1784_);
v___x_1786_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__6(v_cls_1781_, v___x_1785_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v_snd_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v_snd_1788_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_snd_1788_);
lean_dec(v_a_1787_);
v___y_1745_ = v_snd_1788_;
v___y_1746_ = v___y_1732_;
goto v___jp_1744_;
}
else
{
lean_dec_ref_known(v_entry_1740_, 1);
return v___x_1786_;
}
}
v___jp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_inc_ref(v___y_1791_);
v___x_1792_ = l_Lean_stringToMessageData(v___y_1791_);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___y_1790_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__6);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = l_Lean_MessageData_ofName(v_mod_1725_);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_Name_isAnonymous(v_hint_1727_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__8);
v___x_1800_ = l_Lean_MessageData_ofName(v_hint_1727_);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___y_1783_ = v___x_1797_;
v___y_1784_ = v___x_1801_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1802_; 
lean_dec(v_hint_1727_);
v___x_1802_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___closed__9);
v___y_1783_ = v___x_1797_;
v___y_1784_ = v___x_1802_;
goto v___jp_1782_;
}
}
}
}
v___jp_1744_:
{
lean_object* v___x_1747_; lean_object* v_toEnvExtension_1748_; lean_object* v_env_1749_; lean_object* v_nextMacroScope_1750_; lean_object* v_ngen_1751_; lean_object* v_auxDeclNGen_1752_; lean_object* v_traceState_1753_; lean_object* v_messages_1754_; lean_object* v_infoState_1755_; lean_object* v_snapshotTasks_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1770_; 
v___x_1747_ = lean_st_ref_take(v___y_1746_);
v_toEnvExtension_1748_ = lean_ctor_get(v___x_1741_, 0);
v_env_1749_ = lean_ctor_get(v___x_1747_, 0);
v_nextMacroScope_1750_ = lean_ctor_get(v___x_1747_, 1);
v_ngen_1751_ = lean_ctor_get(v___x_1747_, 2);
v_auxDeclNGen_1752_ = lean_ctor_get(v___x_1747_, 3);
v_traceState_1753_ = lean_ctor_get(v___x_1747_, 4);
v_messages_1754_ = lean_ctor_get(v___x_1747_, 6);
v_infoState_1755_ = lean_ctor_get(v___x_1747_, 7);
v_snapshotTasks_1756_ = lean_ctor_get(v___x_1747_, 8);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1747_, 5);
lean_dec(v_unused_1771_);
v___x_1758_ = v___x_1747_;
v_isShared_1759_ = v_isSharedCheck_1770_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snapshotTasks_1756_);
lean_inc(v_infoState_1755_);
lean_inc(v_messages_1754_);
lean_inc(v_traceState_1753_);
lean_inc(v_auxDeclNGen_1752_);
lean_inc(v_ngen_1751_);
lean_inc(v_nextMacroScope_1750_);
lean_inc(v_env_1749_);
lean_dec(v___x_1747_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1770_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_asyncMode_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v_asyncMode_1760_ = lean_ctor_get(v_toEnvExtension_1748_, 2);
v___x_1761_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1741_, v_env_1749_, v_entry_1740_, v_asyncMode_1760_, v___x_1743_);
v___x_1762_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 5, v___x_1762_);
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1764_ = v___x_1758_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_nextMacroScope_1750_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_ngen_1751_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_auxDeclNGen_1752_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v_traceState_1753_);
lean_ctor_set(v_reuseFailAlloc_1769_, 5, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 6, v_messages_1754_);
lean_ctor_set(v_reuseFailAlloc_1769_, 7, v_infoState_1755_);
lean_ctor_set(v_reuseFailAlloc_1769_, 8, v_snapshotTasks_1756_);
v___x_1764_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1765_ = lean_st_ref_set(v___y_1746_, v___x_1764_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___y_1745_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2___boxed(lean_object* v_mod_1816_, lean_object* v_isMeta_1817_, lean_object* v_hint_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_isMeta_boxed_1825_; lean_object* v_res_1826_; 
v_isMeta_boxed_1825_ = lean_unbox(v_isMeta_1817_);
v_res_1826_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(v_mod_1816_, v_isMeta_boxed_1825_, v_hint_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(lean_object* v___x_1827_, lean_object* v_declName_1828_, lean_object* v_as_1829_, size_t v_sz_1830_, size_t v_i_1831_, lean_object* v_b_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1831_, v_sz_1830_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_declName_1828_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_b_1832_);
lean_ctor_set(v___x_1840_, 1, v___y_1833_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v_modules_1843_; lean_object* v___x_1844_; lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v_toImport_1847_; lean_object* v_module_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1842_ = l_Lean_Environment_header(v___x_1827_);
v_modules_1843_ = lean_ctor_get(v___x_1842_, 3);
lean_inc_ref(v_modules_1843_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1845_ = lean_array_uget_borrowed(v_as_1829_, v_i_1831_);
v___x_1846_ = lean_array_get(v___x_1844_, v_modules_1843_, v_a_1845_);
lean_dec_ref(v_modules_1843_);
v_toImport_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc_ref(v_toImport_1847_);
lean_dec(v___x_1846_);
v_module_1848_ = lean_ctor_get(v_toImport_1847_, 0);
lean_inc(v_module_1848_);
lean_dec_ref(v_toImport_1847_);
v___x_1849_ = 0;
lean_inc(v_declName_1828_);
v___x_1850_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(v_module_1848_, v___x_1849_, v_declName_1828_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v_snd_1852_; lean_object* v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v_snd_1852_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_snd_1852_);
lean_dec(v_a_1851_);
v___x_1853_ = lean_box(0);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1831_, v___x_1854_);
v_i_1831_ = v___x_1855_;
v_b_1832_ = v___x_1853_;
v___y_1833_ = v_snd_1852_;
goto _start;
}
else
{
lean_dec(v_declName_1828_);
return v___x_1850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3___boxed(lean_object* v___x_1857_, lean_object* v_declName_1858_, lean_object* v_as_1859_, lean_object* v_sz_1860_, lean_object* v_i_1861_, lean_object* v_b_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
size_t v_sz_boxed_1869_; size_t v_i_boxed_1870_; lean_object* v_res_1871_; 
v_sz_boxed_1869_ = lean_unbox_usize(v_sz_1860_);
lean_dec(v_sz_1860_);
v_i_boxed_1870_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_res_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(v___x_1857_, v_declName_1858_, v_as_1859_, v_sz_boxed_1869_, v_i_boxed_1870_, v_b_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_as_1859_);
lean_dec_ref(v___x_1857_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1));
v___x_1875_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0));
v___x_1876_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1875_, v___x_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_declName_1879_, uint8_t v_isMeta_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_env_1892_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___x_1917_; 
v___x_1887_ = lean_st_ref_get(v___y_1885_);
v_env_1892_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_env_1892_);
lean_dec(v___x_1887_);
v___x_1917_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1892_, v_declName_1879_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_dec_ref(v_env_1892_);
lean_dec(v_declName_1879_);
goto v___jp_1888_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1919_; lean_object* v_modules_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_val_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l_Lean_Environment_header(v_env_1892_);
v_modules_1920_ = lean_ctor_get(v___x_1919_, 3);
lean_inc_ref(v_modules_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = lean_array_get_size(v_modules_1920_);
v___x_1922_ = lean_nat_dec_lt(v_val_1918_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_modules_1920_);
lean_dec(v_val_1918_);
lean_dec_ref(v_env_1892_);
lean_dec(v_declName_1879_);
goto v___jp_1888_;
}
else
{
lean_object* v___x_1923_; lean_object* v_env_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___y_1928_; 
v___x_1923_ = lean_st_ref_get(v___y_1885_);
v_env_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc_ref(v_env_1924_);
lean_dec(v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__2);
v___x_1926_ = lean_array_fget(v_modules_1920_, v_val_1918_);
lean_dec(v_val_1918_);
lean_dec_ref(v_modules_1920_);
if (v_isMeta_1880_ == 0)
{
lean_dec_ref(v_env_1924_);
v___y_1928_ = v_isMeta_1880_;
goto v___jp_1927_;
}
else
{
uint8_t v___x_1941_; uint8_t v___x_1942_; 
lean_inc(v_declName_1879_);
v___x_1941_ = l_Lean_isMarkedMeta(v_env_1924_, v_declName_1879_);
v___x_1942_ = lean_bool_not(v___x_1941_);
v___y_1928_ = v___x_1942_;
goto v___jp_1927_;
}
v___jp_1927_:
{
lean_object* v_toImport_1929_; lean_object* v_module_1930_; lean_object* v___x_1931_; 
v_toImport_1929_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_ref(v_toImport_1929_);
lean_dec(v___x_1926_);
v_module_1930_ = lean_ctor_get(v_toImport_1929_, 0);
lean_inc(v_module_1930_);
lean_dec_ref(v_toImport_1929_);
lean_inc(v_declName_1879_);
v___x_1931_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2(v_module_1930_, v___y_1928_, v_declName_1879_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v_snd_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v_snd_1933_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1933_);
lean_dec(v_a_1932_);
v___x_1934_ = l_Lean_indirectModUseExt;
v___x_1935_ = lean_box(1);
v___x_1936_ = lean_box(0);
lean_inc_ref(v_env_1892_);
v___x_1937_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1925_, v___x_1934_, v_env_1892_, v___x_1935_, v___x_1936_);
v___x_1938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(v___x_1937_, v_declName_1879_);
lean_dec(v___x_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__3));
v___y_1894_ = v_snd_1933_;
v___y_1895_ = v___x_1939_;
goto v___jp_1893_;
}
else
{
lean_object* v_val_1940_; 
v_val_1940_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_val_1940_);
lean_dec_ref_known(v___x_1938_, 1);
v___y_1894_ = v_snd_1933_;
v___y_1895_ = v_val_1940_;
goto v___jp_1893_;
}
}
else
{
lean_dec_ref(v_env_1892_);
lean_dec(v_declName_1879_);
return v___x_1931_;
}
}
}
}
v___jp_1888_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___y_1881_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
v___jp_1893_:
{
lean_object* v___x_1896_; size_t v_sz_1897_; size_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1896_ = lean_box(0);
v_sz_1897_ = lean_array_size(v___y_1895_);
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__3(v_env_1892_, v_declName_1879_, v___y_1895_, v_sz_1897_, v___x_1898_, v___x_1896_, v___y_1894_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v_env_1892_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1916_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_snd_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1914_; 
v_snd_1904_ = lean_ctor_get(v_a_1900_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_a_1900_, 0);
lean_dec(v_unused_1915_);
v___x_1906_ = v_a_1900_;
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_snd_1904_);
lean_dec(v_a_1900_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1896_);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_snd_1904_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1909_);
v___x_1911_ = v___x_1902_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
return v___x_1899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_declName_1943_, lean_object* v_isMeta_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v_isMeta_boxed_1951_; lean_object* v_res_1952_; 
v_isMeta_boxed_1951_ = lean_unbox(v_isMeta_1944_);
v_res_1952_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_declName_1943_, v_isMeta_boxed_1951_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1953_, lean_object* v_vals_1954_, lean_object* v_i_1955_, lean_object* v_k_1956_){
_start:
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = lean_array_get_size(v_keys_1953_);
v___x_1958_ = lean_nat_dec_lt(v_i_1955_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec(v_i_1955_);
v___x_1959_ = lean_box(0);
return v___x_1959_;
}
else
{
lean_object* v_k_x27_1960_; uint8_t v___x_1961_; 
v_k_x27_1960_ = lean_array_fget_borrowed(v_keys_1953_, v_i_1955_);
v___x_1961_ = lean_name_eq(v_k_1956_, v_k_x27_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_add(v_i_1955_, v___x_1962_);
lean_dec(v_i_1955_);
v_i_1955_ = v___x_1963_;
goto _start;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_array_fget_borrowed(v_vals_1954_, v_i_1955_);
lean_dec(v_i_1955_);
lean_inc(v___x_1965_);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1967_, lean_object* v_vals_1968_, lean_object* v_i_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_1967_, v_vals_1968_, v_i_1969_, v_k_1970_);
lean_dec(v_k_1970_);
lean_dec_ref(v_vals_1968_);
lean_dec_ref(v_keys_1967_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_1972_, size_t v_x_1973_, lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1972_) == 0)
{
lean_object* v_es_1975_; lean_object* v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; lean_object* v_j_1979_; lean_object* v___x_1980_; 
v_es_1975_ = lean_ctor_get(v_x_1972_, 0);
v___x_1976_ = lean_box(2);
v___x_1977_ = ((size_t)31ULL);
v___x_1978_ = lean_usize_land(v_x_1973_, v___x_1977_);
v_j_1979_ = lean_usize_to_nat(v___x_1978_);
v___x_1980_ = lean_array_get_borrowed(v___x_1976_, v_es_1975_, v_j_1979_);
lean_dec(v_j_1979_);
switch(lean_obj_tag(v___x_1980_))
{
case 0:
{
lean_object* v_key_1981_; lean_object* v_val_1982_; uint8_t v___x_1983_; 
v_key_1981_ = lean_ctor_get(v___x_1980_, 0);
v_val_1982_ = lean_ctor_get(v___x_1980_, 1);
v___x_1983_ = lean_name_eq(v_x_1974_, v_key_1981_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; 
lean_inc(v_val_1982_);
v___x_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_val_1982_);
return v___x_1985_;
}
}
case 1:
{
lean_object* v_node_1986_; size_t v___x_1987_; size_t v___x_1988_; 
v_node_1986_ = lean_ctor_get(v___x_1980_, 0);
v___x_1987_ = ((size_t)5ULL);
v___x_1988_ = lean_usize_shift_right(v_x_1973_, v___x_1987_);
v_x_1972_ = v_node_1986_;
v_x_1973_ = v___x_1988_;
goto _start;
}
default: 
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_box(0);
return v___x_1990_;
}
}
}
else
{
lean_object* v_ks_1991_; lean_object* v_vs_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_ks_1991_ = lean_ctor_get(v_x_1972_, 0);
v_vs_1992_ = lean_ctor_get(v_x_1972_, 1);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_1991_, v_vs_1992_, v___x_1993_, v_x_1974_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
size_t v_x_30056__boxed_1998_; lean_object* v_res_1999_; 
v_x_30056__boxed_1998_ = lean_unbox_usize(v_x_1996_);
lean_dec(v_x_1996_);
v_res_1999_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_1995_, v_x_30056__boxed_1998_, v_x_1997_);
lean_dec(v_x_1997_);
lean_dec_ref(v_x_1995_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
uint64_t v___y_2003_; 
if (lean_obj_tag(v_x_2001_) == 0)
{
uint64_t v___x_2006_; 
v___x_2006_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg___closed__0);
v___y_2003_ = v___x_2006_;
goto v___jp_2002_;
}
else
{
uint64_t v_hash_2007_; 
v_hash_2007_ = lean_ctor_get_uint64(v_x_2001_, sizeof(void*)*2);
v___y_2003_ = v_hash_2007_;
goto v___jp_2002_;
}
v___jp_2002_:
{
size_t v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_uint64_to_usize(v___y_2003_);
v___x_2005_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2000_, v___x_2004_, v_x_2001_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_2008_, lean_object* v_x_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2008_, v_x_2009_);
lean_dec(v_x_2009_);
lean_dec_ref(v_x_2008_);
return v_res_2010_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__1));
v___x_2012_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___closed__0));
v___x_2013_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2012_, v___x_2011_);
return v___x_2013_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2022_ = l_Lean_stringToMessageData(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2026_, lean_object* v_init_2027_, lean_object* v_x_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
lean_object* v_k_2035_; lean_object* v_l_2036_; lean_object* v_r_2037_; lean_object* v___x_2038_; 
v_k_2035_ = lean_ctor_get(v_x_2028_, 1);
lean_inc(v_k_2035_);
v_l_2036_ = lean_ctor_get(v_x_2028_, 3);
lean_inc(v_l_2036_);
v_r_2037_ = lean_ctor_get(v_x_2028_, 4);
lean_inc(v_r_2037_);
lean_dec_ref_known(v_x_2028_, 5);
lean_inc_ref(v_origDecl_2026_);
v___x_2038_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2026_, v_init_2027_, v_l_2036_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_snd_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2169_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v_snd_2040_ = lean_ctor_get(v_a_2039_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v_a_2039_, 0);
lean_dec(v_unused_2170_);
v___x_2042_ = v_a_2039_;
v_isShared_2043_ = v_isSharedCheck_2169_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_snd_2040_);
lean_dec(v_a_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2169_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_NameSet_contains(v_snd_2040_, v_k_2035_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v_env_2047_; lean_object* v___x_2048_; lean_object* v_toEnvExtension_2049_; lean_object* v_asyncMode_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2046_ = lean_st_ref_get(v___y_2033_);
v_env_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2046_);
v___x_2048_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2049_ = lean_ctor_get(v___x_2048_, 0);
v_asyncMode_2050_ = lean_ctor_get(v_toEnvExtension_2049_, 2);
lean_inc(v_k_2035_);
v___x_2051_ = l_Lean_NameSet_insert(v_snd_2040_, v_k_2035_);
v___x_2052_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
v___x_2053_ = lean_box(0);
v___x_2054_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2052_, v___x_2048_, v_env_2047_, v_asyncMode_2050_, v___x_2053_);
v___x_2055_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2054_, v_k_2035_);
lean_dec(v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_val_2056_; lean_object* v___x_2057_; 
lean_del_object(v___x_2042_);
lean_dec(v_k_2035_);
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_n(v_val_2056_, 2);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2056_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; uint8_t v___y_2060_; lean_object* v_toSignature_2074_; lean_object* v_name_2075_; uint8_t v___x_2076_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v_toSignature_2074_ = lean_ctor_get(v_val_2056_, 0);
v_name_2075_ = lean_ctor_get(v_toSignature_2074_, 0);
v___x_2076_ = l_Lean_isPrivateName(v_name_2075_);
if (v___x_2076_ == 0)
{
lean_dec(v_a_2058_);
v___y_2060_ = v___x_2076_;
goto v___jp_2059_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_unbox(v_a_2058_);
lean_dec(v_a_2058_);
v___y_2060_ = v___x_2077_;
goto v___jp_2059_;
}
v___jp_2059_:
{
if (v___y_2060_ == 0)
{
lean_dec(v_val_2056_);
v_init_2027_ = v___x_2044_;
v_x_2028_ = v_r_2037_;
v___y_2029_ = v___x_2051_;
goto _start;
}
else
{
lean_object* v___x_2062_; 
lean_inc_ref(v_origDecl_2026_);
v___x_2062_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2026_, v_val_2056_, v___x_2051_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v_snd_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v_snd_2064_ = lean_ctor_get(v_a_2063_, 1);
lean_inc(v_snd_2064_);
lean_dec(v_a_2063_);
v_init_2027_ = v___x_2044_;
v_x_2028_ = v_r_2037_;
v___y_2029_ = v_snd_2064_;
goto _start;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_r_2037_);
lean_dec_ref(v_origDecl_2026_);
v_a_2066_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2062_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2062_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_val_2056_);
lean_dec(v___x_2051_);
lean_dec(v_r_2037_);
lean_dec_ref(v_origDecl_2026_);
v_a_2078_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2057_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2057_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v_env_2087_; lean_object* v___x_2088_; 
lean_dec(v___x_2055_);
v___x_2086_ = lean_st_ref_get(v___y_2033_);
v_env_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc_ref(v_env_2087_);
lean_dec(v___x_2086_);
v___x_2088_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2087_, v_k_2035_);
lean_dec_ref(v_env_2087_);
if (lean_obj_tag(v___x_2088_) == 1)
{
lean_object* v_val_2089_; lean_object* v___x_2090_; lean_object* v_env_2091_; lean_object* v___x_2092_; lean_object* v_modules_2093_; uint8_t v___x_2094_; uint8_t v___y_2096_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_val_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = lean_st_ref_get(v___y_2033_);
v_env_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc_ref(v_env_2091_);
lean_dec(v___x_2090_);
v___x_2092_ = l_Lean_Environment_header(v_env_2091_);
lean_dec_ref(v_env_2091_);
v_modules_2093_ = lean_ctor_get(v___x_2092_, 3);
lean_inc_ref(v_modules_2093_);
lean_dec_ref(v___x_2092_);
v___x_2094_ = 1;
v___x_2161_ = lean_array_get_size(v_modules_2093_);
v___x_2162_ = lean_nat_dec_lt(v_val_2089_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_dec_ref(v_modules_2093_);
v___y_2096_ = v___x_2045_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2163_; lean_object* v_toImport_2164_; uint8_t v_isExported_2165_; uint8_t v___x_2166_; 
v___x_2163_ = lean_array_fget(v_modules_2093_, v_val_2089_);
lean_dec_ref(v_modules_2093_);
v_toImport_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_ref(v_toImport_2164_);
lean_dec(v___x_2163_);
v_isExported_2165_ = lean_ctor_get_uint8(v_toImport_2164_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2164_);
v___x_2166_ = lean_bool_not(v_isExported_2165_);
v___y_2096_ = v___x_2166_;
goto v___jp_2095_;
}
v___jp_2095_:
{
if (v___y_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v_env_2098_; uint8_t v___x_2099_; uint8_t v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec(v_val_2089_);
lean_del_object(v___x_2042_);
v___x_2097_ = lean_st_ref_get(v___y_2033_);
v_env_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc_ref(v_env_2098_);
lean_dec(v___x_2097_);
lean_inc(v_k_2035_);
v___x_2099_ = l_Lean_getIRPhases(v_env_2098_, v_k_2035_);
v___x_2100_ = 1;
v___x_2101_ = l_Lean_instBEqIRPhases_beq(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_box(v___x_2101_);
v___x_2103_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed), 8, 2);
lean_closure_set(v___x_2103_, 0, v_k_2035_);
lean_closure_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___redArg(v___x_2103_, v___x_2094_, v___x_2051_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v_snd_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v_snd_2106_ = lean_ctor_get(v_a_2105_, 1);
lean_inc(v_snd_2106_);
lean_dec(v_a_2105_);
v_init_2027_ = v___x_2044_;
v_x_2028_ = v_r_2037_;
v___y_2029_ = v_snd_2106_;
goto _start;
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_r_2037_);
lean_dec_ref(v_origDecl_2026_);
v_a_2108_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2104_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2104_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v_a_2118_; lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2160_; 
v___x_2116_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2117_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2116_, v___x_2051_, v___y_2032_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v_fst_2119_ = lean_ctor_get(v_a_2118_, 0);
v_snd_2120_ = lean_ctor_get(v_a_2118_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_a_2118_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2122_ = v_a_2118_;
v_isShared_2123_ = v_isSharedCheck_2160_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_snd_2120_);
lean_inc(v_fst_2119_);
lean_dec(v_a_2118_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2160_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint8_t v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_unbox(v_fst_2119_);
lean_dec(v_fst_2119_);
v___x_2125_ = lean_bool_not(v___x_2124_);
if (v___x_2125_ == 0)
{
lean_del_object(v___x_2122_);
lean_dec(v_val_2089_);
lean_del_object(v___x_2042_);
lean_dec(v_k_2035_);
v_init_2027_ = v___x_2044_;
v_x_2028_ = v_r_2037_;
v___y_2029_ = v_snd_2120_;
goto _start;
}
else
{
lean_object* v___x_2127_; lean_object* v_toSignature_2128_; lean_object* v_env_2129_; lean_object* v_name_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_dec(v_snd_2120_);
lean_dec(v_r_2037_);
v___x_2127_ = lean_st_ref_get(v___y_2033_);
v_toSignature_2128_ = lean_ctor_get(v_origDecl_2026_, 0);
lean_inc_ref(v_toSignature_2128_);
lean_dec_ref(v_origDecl_2026_);
v_env_2129_ = lean_ctor_get(v___x_2127_, 0);
lean_inc_ref(v_env_2129_);
lean_dec(v___x_2127_);
v_name_2130_ = lean_ctor_get(v_toSignature_2128_, 0);
lean_inc(v_name_2130_);
lean_dec_ref(v_toSignature_2128_);
v___x_2131_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
v___x_2132_ = l_Lean_MessageData_ofConstName(v_name_2130_, v___x_2045_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 7);
lean_ctor_set(v___x_2122_, 1, v___x_2132_);
lean_ctor_set(v___x_2122_, 0, v___x_2131_);
v___x_2134_ = v___x_2122_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 7);
lean_ctor_set(v___x_2042_, 1, v___x_2135_);
lean_ctor_set(v___x_2042_, 0, v___x_2134_);
v___x_2137_ = v___x_2042_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v___x_2138_ = l_Lean_MessageData_ofConstName(v_k_2035_, v___x_2045_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_Environment_header(v_env_2129_);
lean_dec_ref(v_env_2129_);
v___x_2143_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2142_);
v___x_2144_ = lean_array_get(v___x_2053_, v___x_2143_, v_val_2089_);
lean_dec(v_val_2089_);
lean_dec_ref(v___x_2143_);
v___x_2145_ = l_Lean_MessageData_ofName(v___x_2144_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2141_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2148_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
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
lean_dec(v___x_2088_);
lean_del_object(v___x_2042_);
lean_dec(v_k_2035_);
v_init_2027_ = v___x_2044_;
v_x_2028_ = v_r_2037_;
v___y_2029_ = v___x_2051_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2042_);
lean_dec(v_k_2035_);
v_init_2027_ = v___x_2044_;
v_x_2028_ = v_r_2037_;
v___y_2029_ = v_snd_2040_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2037_);
lean_dec(v_k_2035_);
lean_dec_ref(v_origDecl_2026_);
return v___x_2038_;
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_origDecl_2026_);
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_init_2027_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___y_2029_);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2174_, lean_object* v_origDecl_2175_, lean_object* v_code_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = l_Lean_NameSet_empty;
v___x_2184_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2174_, v_code_2176_, v___x_2183_);
v___x_2185_ = lean_box(0);
v___x_2186_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2175_, v___x_2185_, v___x_2184_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2203_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2203_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2203_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_snd_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2201_; 
v_snd_2191_ = lean_ctor_get(v_a_2187_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_a_2187_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v_a_2187_, 0);
lean_dec(v_unused_2202_);
v___x_2193_ = v_a_2187_;
v_isShared_2194_ = v_isSharedCheck_2201_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_snd_2191_);
lean_dec(v_a_2187_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2201_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2185_);
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_snd_2191_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2196_);
v___x_2198_ = v___x_2189_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2186_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2186_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2212_, lean_object* v_origDecl_2213_, lean_object* v_code_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_30143__boxed_2221_; lean_object* v_res_2222_; 
v___x_30143__boxed_2221_ = lean_unbox(v___x_2212_);
v_res_2222_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_30143__boxed_2221_, v_origDecl_2213_, v_code_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2223_, lean_object* v_decl_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_value_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; 
v_value_2231_ = lean_ctor_get(v_decl_2224_, 1);
lean_inc_ref(v_value_2231_);
lean_dec_ref(v_decl_2224_);
v___x_2232_ = 0;
v___x_2233_ = lean_box(v___x_2232_);
v___f_2234_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2234_, 0, v___x_2233_);
lean_closure_set(v___f_2234_, 1, v_origDecl_2223_);
v___x_2235_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2234_, v_value_2231_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2236_, lean_object* v_decl_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2236_, v_decl_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2245_, lean_object* v_init_2246_, lean_object* v_x_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2245_, v_init_2246_, v_x_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2256_, v_x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2259_, v_x_2260_, v_x_2261_);
lean_dec(v_x_2261_);
lean_dec_ref(v_x_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_opt_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_opt_2263_, v___y_2264_, v___y_2267_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_opt_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_opt_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_opt_2271_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2279_, lean_object* v_x_2280_, size_t v_x_2281_, lean_object* v_x_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2280_, v_x_2281_, v_x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
size_t v_x_30572__boxed_2288_; lean_object* v_res_2289_; 
v_x_30572__boxed_2288_ = lean_unbox_usize(v_x_2286_);
lean_dec(v_x_2286_);
v_res_2289_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2284_, v_x_2285_, v_x_30572__boxed_2288_, v_x_2287_);
lean_dec(v_x_2287_);
lean_dec_ref(v_x_2285_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4(lean_object* v_00_u03b2_2290_, lean_object* v_m_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___redArg(v_m_2291_, v_a_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2294_, lean_object* v_m_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4(v_00_u03b2_2294_, v_m_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_m_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2298_, lean_object* v_keys_2299_, lean_object* v_vals_2300_, lean_object* v_heq_2301_, lean_object* v_i_2302_, lean_object* v_k_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2299_, v_vals_2300_, v_i_2302_, v_k_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2305_, lean_object* v_keys_2306_, lean_object* v_vals_2307_, lean_object* v_heq_2308_, lean_object* v_i_2309_, lean_object* v_k_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2305_, v_keys_2306_, v_vals_2307_, v_heq_2308_, v_i_2309_, v_k_2310_);
lean_dec(v_k_2310_);
lean_dec_ref(v_vals_2307_);
lean_dec_ref(v_keys_2306_);
return v_res_2311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___redArg(v_x_2313_, v_x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5(v_00_u03b2_2316_, v_x_2317_, v_x_2318_);
lean_dec_ref(v_x_2318_);
lean_dec_ref(v_x_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_2321_, lean_object* v_a_2322_, lean_object* v_x_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___redArg(v_a_2322_, v_x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2325_, lean_object* v_a_2326_, lean_object* v_x_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__4_spec__9(v_00_u03b2_2325_, v_a_2326_, v_x_2327_);
lean_dec(v_x_2327_);
lean_dec(v_a_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2329_, lean_object* v_x_2330_, size_t v_x_2331_, lean_object* v_x_2332_){
_start:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___redArg(v_x_2330_, v_x_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
size_t v_x_30600__boxed_2338_; uint8_t v_res_2339_; lean_object* v_r_2340_; 
v_x_30600__boxed_2338_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_res_2339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_2334_, v_x_2335_, v_x_30600__boxed_2338_, v_x_2337_);
lean_dec_ref(v_x_2337_);
lean_dec_ref(v_x_2335_);
v_r_2340_ = lean_box(v_res_2339_);
return v_r_2340_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2341_, lean_object* v_keys_2342_, lean_object* v_vals_2343_, lean_object* v_heq_2344_, lean_object* v_i_2345_, lean_object* v_k_2346_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___redArg(v_keys_2342_, v_i_2345_, v_k_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2348_, lean_object* v_keys_2349_, lean_object* v_vals_2350_, lean_object* v_heq_2351_, lean_object* v_i_2352_, lean_object* v_k_2353_){
_start:
{
uint8_t v_res_2354_; lean_object* v_r_2355_; 
v_res_2354_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1_spec__2_spec__5_spec__8_spec__12(v_00_u03b2_2348_, v_keys_2349_, v_vals_2350_, v_heq_2351_, v_i_2352_, v_k_2353_);
lean_dec_ref(v_k_2353_);
lean_dec_ref(v_vals_2350_);
lean_dec_ref(v_keys_2349_);
v_r_2355_ = lean_box(v_res_2354_);
return v_r_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2356_, size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_b_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_a_2366_; uint8_t v___x_2370_; 
v___x_2370_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v_b_2359_);
return v___x_2371_;
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_a_2372_ = lean_array_uget_borrowed(v_as_2356_, v_i_2358_);
lean_inc(v_a_2372_);
v___x_2373_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2372_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_toSignature_2374_; lean_object* v_a_2375_; lean_object* v_name_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; uint8_t v___x_2379_; 
v_toSignature_2374_ = lean_ctor_get(v_a_2372_, 0);
v_a_2375_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2373_, 1);
v_name_2376_ = lean_ctor_get(v_toSignature_2374_, 0);
v___x_2377_ = lean_box(0);
v___x_2378_ = l_Lean_isPrivateName(v_name_2376_);
v___x_2379_ = lean_bool_not(v___x_2378_);
if (v___x_2379_ == 0)
{
lean_dec(v_a_2375_);
v_a_2366_ = v___x_2377_;
goto v___jp_2365_;
}
else
{
uint8_t v___x_2380_; 
v___x_2380_ = lean_unbox(v_a_2375_);
lean_dec(v_a_2375_);
if (v___x_2380_ == 0)
{
v_a_2366_ = v___x_2377_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_st_ref_get(v___y_2363_);
lean_dec(v___x_2381_);
v___x_2382_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2372_, 2);
v___x_2383_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2372_, v_a_2372_, v___x_2382_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_dec_ref_known(v___x_2383_, 1);
v_a_2366_ = v___x_2377_;
goto v___jp_2365_;
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2373_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2373_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
v___jp_2365_:
{
size_t v___x_2367_; size_t v___x_2368_; 
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2358_, v___x_2367_);
v_i_2358_ = v___x_2368_;
v_b_2359_ = v_a_2366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2400_, lean_object* v_sz_2401_, lean_object* v_i_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
size_t v_sz_boxed_2409_; size_t v_i_boxed_2410_; lean_object* v_res_2411_; 
v_sz_boxed_2409_ = lean_unbox_usize(v_sz_2401_);
lean_dec(v_sz_2401_);
v_i_boxed_2410_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2400_, v_sz_boxed_2409_, v_i_boxed_2410_, v_b_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_as_2400_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; lean_object* v_env_2419_; lean_object* v___x_2420_; uint8_t v_isModule_2421_; 
v___x_2418_ = lean_st_ref_get(v___y_2416_);
v_env_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc_ref(v_env_2419_);
lean_dec(v___x_2418_);
v___x_2420_ = l_Lean_Environment_header(v_env_2419_);
lean_dec_ref(v_env_2419_);
v_isModule_2421_ = lean_ctor_get_uint8(v___x_2420_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2420_);
if (v_isModule_2421_ == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_decls_2412_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; size_t v_sz_2424_; size_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2423_ = lean_box(0);
v_sz_2424_ = lean_array_size(v_decls_2412_);
v___x_2425_ = ((size_t)0ULL);
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2412_, v_sz_2424_, v___x_2425_, v___x_2423_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v___x_2426_, 0);
lean_dec(v_unused_2434_);
v___x_2428_ = v___x_2426_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_dec(v___x_2426_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_decls_2412_);
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_decls_2412_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v_decls_2412_);
v_a_2435_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2426_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2426_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2449_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2463_ = l_Lean_stringToMessageData(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2464_, uint8_t v___x_2465_, lean_object* v_as_2466_, size_t v_sz_2467_, size_t v_i_2468_, lean_object* v_b_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_a_2476_; uint8_t v___x_2480_; 
v___x_2480_ = lean_usize_dec_lt(v_i_2468_, v_sz_2467_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_b_2469_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; lean_object* v_env_2483_; lean_object* v_a_2484_; lean_object* v_toSignature_2485_; lean_object* v_name_2486_; lean_object* v___x_2487_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2482_ = lean_st_ref_get(v___y_2473_);
v_env_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc_ref(v_env_2483_);
lean_dec(v___x_2482_);
v_a_2484_ = lean_array_uget_borrowed(v_as_2466_, v_i_2468_);
v_toSignature_2485_ = lean_ctor_get(v_a_2484_, 0);
v_name_2486_ = lean_ctor_get(v_toSignature_2485_, 0);
v___x_2487_ = lean_box(0);
v___x_2495_ = l_Lean_Environment_setExporting(v_env_2483_, v___x_2465_);
lean_inc(v_name_2486_);
v___x_2496_ = l_Lean_Environment_contains(v___x_2495_, v_name_2486_, v___x_2465_);
if (v___x_2496_ == 0)
{
v_a_2476_ = v___x_2487_;
goto v___jp_2475_;
}
else
{
lean_object* v_options_2497_; uint8_t v_hasTrace_2498_; 
v_options_2497_ = lean_ctor_get(v___y_2472_, 2);
v_hasTrace_2498_ = lean_ctor_get_uint8(v_options_2497_, sizeof(void*)*1);
if (v_hasTrace_2498_ == 0)
{
v___y_2489_ = v___y_2470_;
v___y_2490_ = v___y_2471_;
v___y_2491_ = v___y_2472_;
v___y_2492_ = v___y_2473_;
goto v___jp_2488_;
}
else
{
lean_object* v_inheritedTraceOptions_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v_inheritedTraceOptions_2499_ = lean_ctor_get(v___y_2472_, 13);
v___x_2500_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2501_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2502_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2499_, v_options_2497_, v___x_2501_);
if (v___x_2502_ == 0)
{
v___y_2489_ = v___y_2470_;
v___y_2490_ = v___y_2471_;
v___y_2491_ = v___y_2472_;
v___y_2492_ = v___y_2473_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2503_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2486_);
v___x_2504_ = l_Lean_MessageData_ofName(v_name_2486_);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2500_, v___x_2507_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_dec_ref_known(v___x_2508_, 1);
v___y_2489_ = v___y_2470_;
v___y_2490_ = v___y_2471_;
v___y_2491_ = v___y_2472_;
v___y_2492_ = v___y_2473_;
goto v___jp_2488_;
}
else
{
return v___x_2508_;
}
}
}
}
v___jp_2488_:
{
uint8_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2464_);
lean_inc(v_a_2484_);
v___x_2494_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2493_, v_phase_2464_, v_a_2484_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_dec_ref_known(v___x_2494_, 1);
v_a_2476_ = v___x_2487_;
goto v___jp_2475_;
}
else
{
return v___x_2494_;
}
}
}
v___jp_2475_:
{
size_t v___x_2477_; size_t v___x_2478_; 
v___x_2477_ = ((size_t)1ULL);
v___x_2478_ = lean_usize_add(v_i_2468_, v___x_2477_);
v_i_2468_ = v___x_2478_;
v_b_2469_ = v_a_2476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2509_, lean_object* v___x_2510_, lean_object* v_as_2511_, lean_object* v_sz_2512_, lean_object* v_i_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v_phase_boxed_2520_; uint8_t v___x_2836__boxed_2521_; size_t v_sz_boxed_2522_; size_t v_i_boxed_2523_; lean_object* v_res_2524_; 
v_phase_boxed_2520_ = lean_unbox(v_phase_2509_);
v___x_2836__boxed_2521_ = lean_unbox(v___x_2510_);
v_sz_boxed_2522_ = lean_unbox_usize(v_sz_2512_);
lean_dec(v_sz_2512_);
v_i_boxed_2523_ = lean_unbox_usize(v_i_2513_);
lean_dec(v_i_2513_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2520_, v___x_2836__boxed_2521_, v_as_2511_, v_sz_boxed_2522_, v_i_boxed_2523_, v_b_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v_as_2511_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2525_, lean_object* v_decls_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; lean_object* v_env_2533_; lean_object* v___x_2534_; uint8_t v_isModule_2535_; 
v___x_2532_ = lean_st_ref_get(v___y_2530_);
v_env_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_ref(v_env_2533_);
lean_dec(v___x_2532_);
v___x_2534_ = l_Lean_Environment_header(v_env_2533_);
lean_dec_ref(v_env_2533_);
v_isModule_2535_ = lean_ctor_get_uint8(v___x_2534_, sizeof(void*)*7 + 4);
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
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2525_, v_isModule_2535_, v_decls_2526_, v_sz_2538_, v___x_2539_, v___x_2537_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2557_, lean_object* v_decls_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v_phase_boxed_2564_; lean_object* v_res_2565_; 
v_phase_boxed_2564_ = lean_unbox(v_phase_2557_);
v_res_2565_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2564_, v_decls_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = lean_box(v_phase_2568_);
v___f_2570_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2570_, 0, v___x_2569_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = 0;
v___x_2573_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2574_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2574_, 0, v___x_2571_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
lean_ctor_set(v___x_2574_, 2, v___f_2570_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3, v_phase_2568_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3 + 1, v_phase_2568_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3 + 2, v___x_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2575_){
_start:
{
uint8_t v_phase_boxed_2576_; lean_object* v_res_2577_; 
v_phase_boxed_2576_ = lean_unbox(v_phase_2575_);
v_res_2577_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2576_);
return v_res_2577_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_unsigned_to_nat(3356661454u);
v___x_2630_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2631_ = l_Lean_Name_num___override(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2635_ = l_Lean_Name_str___override(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2638_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2639_ = l_Lean_Name_str___override(v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_unsigned_to_nat(2u);
v___x_2641_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2642_ = l_Lean_Name_num___override(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2645_ = 0;
v___x_2646_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2647_ = l_Lean_registerTraceClass(v___x_2644_, v___x_2645_, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2649_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Visibility(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
