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
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_baseExt;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3_value;
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
lean_object* v_val_500_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___x_517_; lean_object* v_env_518_; uint8_t v___x_519_; 
v_val_500_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_a_498_, 1);
v___x_517_ = lean_st_ref_get(v___y_491_);
v_env_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_env_518_);
lean_dec(v___x_517_);
v___x_519_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_518_, v_k_493_);
if (v___x_519_ == 0)
{
lean_object* v_options_520_; uint8_t v_hasTrace_521_; 
v_options_520_ = lean_ctor_get(v___y_490_, 2);
v_hasTrace_521_ = lean_ctor_get_uint8(v_options_520_, sizeof(void*)*1);
if (v_hasTrace_521_ == 0)
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
lean_object* v_inheritedTraceOptions_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_inheritedTraceOptions_522_ = lean_ctor_get(v___y_490_, 13);
v___x_523_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_524_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_525_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_522_, v_options_520_, v___x_524_);
if (v___x_525_ == 0)
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
lean_object* v_toSignature_526_; lean_object* v_name_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_toSignature_526_ = lean_ctor_get(v_decl_485_, 0);
v_name_527_ = lean_ctor_get(v_toSignature_526_, 0);
v___x_528_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
v___x_529_ = l_Lean_MessageData_ofName(v_k_493_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_inc(v_name_527_);
v___x_533_ = l_Lean_MessageData_ofName(v_name_527_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_523_, v___x_534_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_dec_ref_known(v___x_535_, 1);
v___y_502_ = v___y_488_;
v___y_503_ = v___y_489_;
v___y_504_ = v___y_490_;
v___y_505_ = v___y_491_;
goto v___jp_501_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_val_500_);
lean_dec(v_r_495_);
lean_dec_ref(v_decl_485_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
else
{
lean_dec(v_val_500_);
lean_dec(v_k_493_);
v_init_486_ = v___x_499_;
v_x_487_ = v_r_495_;
goto _start;
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
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_r_495_);
lean_dec(v_k_493_);
lean_dec_ref(v_decl_485_);
v_a_546_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_497_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_497_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
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
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_decl_485_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_init_486_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t v_pu_556_, uint8_t v_phase_557_, lean_object* v_decl_558_, lean_object* v_code_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = l_Lean_NameSet_empty;
v___x_566_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_556_, v_code_559_, v___x_565_);
v___x_567_ = lean_box(0);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_557_, v_decl_558_, v___x_567_, v___x_566_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v___x_568_, 0);
lean_dec(v_unused_576_);
v___x_570_ = v___x_568_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_dec(v___x_568_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_567_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_567_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_568_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object* v_phase_585_, lean_object* v_decl_586_, lean_object* v_init_587_, lean_object* v_x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v_phase_boxed_594_; lean_object* v_res_595_; 
v_phase_boxed_594_ = lean_unbox(v_phase_585_);
v_res_595_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_594_, v_decl_586_, v_init_587_, v_x_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object* v_pu_596_, lean_object* v_phase_597_, lean_object* v_decl_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
uint8_t v_pu_boxed_604_; uint8_t v_phase_boxed_605_; lean_object* v_res_606_; 
v_pu_boxed_604_ = lean_unbox(v_pu_596_);
v_phase_boxed_605_ = lean_unbox(v_phase_597_);
v_res_606_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_boxed_604_, v_phase_boxed_605_, v_decl_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_options_613_; lean_object* v_ref_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_options_613_ = lean_ctor_get(v___y_610_, 2);
v_ref_614_ = lean_ctor_get(v___y_610_, 5);
v___x_615_ = lean_st_ref_get(v___y_611_);
v___x_616_ = lean_st_ref_get(v___y_609_);
v___x_617_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_608_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_640_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_640_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_640_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_640_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_env_622_; lean_object* v_lctx_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_638_; 
v_env_622_ = lean_ctor_get(v___x_615_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_615_);
v_lctx_623_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v___x_616_, 1);
lean_dec(v_unused_639_);
v___x_625_ = v___x_616_;
v_isShared_626_ = v_isSharedCheck_638_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_lctx_623_);
lean_dec(v___x_616_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_638_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_627_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
v___x_628_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_623_, v___x_627_);
lean_dec_ref(v_lctx_623_);
v___x_629_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
lean_inc_ref(v_options_613_);
v___x_630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_630_, 0, v_env_622_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_ctor_set(v___x_630_, 2, v___x_628_);
lean_ctor_set(v___x_630_, 3, v_options_613_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 3);
lean_ctor_set(v___x_625_, 1, v_msg_607_);
lean_ctor_set(v___x_625_, 0, v___x_630_);
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_msg_607_);
v___x_632_ = v_reuseFailAlloc_637_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_inc(v_ref_614_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_ref_614_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 1);
lean_ctor_set(v___x_620_, 0, v___x_633_);
v___x_635_ = v___x_620_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_616_);
lean_dec(v___x_615_);
lean_dec_ref(v_msg_607_);
v_a_641_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_617_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_617_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_656_, lean_object* v_msg_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_657_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_665_, v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
return v_res_673_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_674_, lean_object* v_opt_675_){
_start:
{
lean_object* v_name_676_; lean_object* v_defValue_677_; lean_object* v_map_678_; lean_object* v___x_679_; 
v_name_676_ = lean_ctor_get(v_opt_675_, 0);
v_defValue_677_ = lean_ctor_get(v_opt_675_, 1);
v_map_678_ = lean_ctor_get(v_opts_674_, 0);
v___x_679_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_678_, v_name_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
uint8_t v___x_680_; 
v___x_680_ = lean_unbox(v_defValue_677_);
return v___x_680_;
}
else
{
lean_object* v_val_681_; 
v_val_681_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v___x_679_, 1);
if (lean_obj_tag(v_val_681_) == 1)
{
uint8_t v_v_682_; 
v_v_682_ = lean_ctor_get_uint8(v_val_681_, 0);
lean_dec_ref_known(v_val_681_, 0);
return v_v_682_;
}
else
{
uint8_t v___x_683_; 
lean_dec(v_val_681_);
v___x_683_ = lean_unbox(v_defValue_677_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_684_, lean_object* v_opt_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_684_, v_opt_685_);
lean_dec_ref(v_opt_685_);
lean_dec_ref(v_opts_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_688_, lean_object* v_v_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
if (lean_obj_tag(v_v_689_) == 0)
{
lean_object* v_code_696_; lean_object* v___x_697_; 
v_code_696_ = lean_ctor_get(v_v_689_, 0);
lean_inc_ref(v_code_696_);
lean_dec_ref_known(v_v_689_, 1);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
v___x_697_ = lean_apply_7(v_f_688_, v_code_696_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, lean_box(0));
return v___x_697_;
}
else
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_f_688_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_v_689_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_v_689_, 0);
lean_dec(v_unused_707_);
v___x_699_ = v_v_689_;
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
else
{
lean_dec(v_v_689_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = lean_box(0);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___y_690_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
lean_ctor_set(v___x_699_, 0, v___x_702_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_708_, lean_object* v_v_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_708_, v_v_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_717_, lean_object* v_f_718_, lean_object* v_v_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_718_, v_v_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_727_, lean_object* v_f_728_, lean_object* v_v_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v_pu_boxed_736_; lean_object* v_res_737_; 
v_pu_boxed_736_ = lean_unbox(v_pu_727_);
v_res_737_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_736_, v_f_728_, v_v_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_737_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_771_, lean_object* v_origDecl_772_, uint8_t v_isMeta_773_, uint8_t v_isPublic_774_, lean_object* v_init_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v_k_783_; lean_object* v_l_784_; lean_object* v_r_785_; lean_object* v___x_786_; 
v_k_783_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_k_783_);
v_l_784_ = lean_ctor_get(v_x_776_, 3);
lean_inc(v_l_784_);
v_r_785_ = lean_ctor_get(v_x_776_, 4);
lean_inc(v_r_785_);
lean_dec_ref_known(v_x_776_, 5);
lean_inc_ref(v_origDecl_772_);
v___x_786_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_771_, v_origDecl_772_, v_isMeta_773_, v_isPublic_774_, v_init_775_, v_l_784_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v_snd_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_1104_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v_snd_788_ = lean_ctor_get(v_a_787_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v_a_787_, 0);
lean_dec(v_unused_1105_);
v___x_790_ = v_a_787_;
v_isShared_791_ = v_isSharedCheck_1104_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snd_788_);
lean_dec(v_a_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_1104_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; uint8_t v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; uint8_t v___x_849_; uint8_t v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; 
v___x_792_ = lean_box(0);
v___x_849_ = l_Lean_NameSet_contains(v_snd_788_, v_k_783_);
if (v___x_849_ == 0)
{
lean_object* v___x_878_; lean_object* v_env_879_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_916_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; uint8_t v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; uint8_t v___y_941_; uint8_t v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_949_; lean_object* v___y_950_; uint8_t v___y_951_; uint8_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___x_1026_; 
v___x_878_ = lean_st_ref_get(v___y_781_);
v_env_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc_ref(v_env_879_);
lean_dec(v___x_878_);
lean_inc(v_k_783_);
v___x_1026_ = l_Lean_NameSet_insert(v_snd_788_, v_k_783_);
if (v_isMeta_773_ == 0)
{
v___y_1017_ = v___x_1026_;
v___y_1018_ = v___y_778_;
v___y_1019_ = v___y_779_;
v___y_1020_ = v___y_780_;
v___y_1021_ = v___y_781_;
goto v___jp_1016_;
}
else
{
if (v_isPublic_774_ == 0)
{
v___y_1017_ = v___x_1026_;
v___y_1018_ = v___y_778_;
v___y_1019_ = v___y_779_;
v___y_1020_ = v___y_780_;
v___y_1021_ = v___y_781_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_879_, v_k_783_);
if (lean_obj_tag(v___x_1027_) == 1)
{
lean_object* v_val_1028_; uint8_t v___x_1029_; 
v_val_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1028_);
lean_dec_ref_known(v___x_1027_, 1);
lean_inc(v_k_783_);
lean_inc_ref(v_env_879_);
v___x_1029_ = l_Lean_isMarkedMeta(v_env_879_, v_k_783_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; uint8_t v___y_1060_; lean_object* v_modules_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1030_ = l_Lean_Environment_header(v_env_879_);
v_modules_1061_ = lean_ctor_get(v___x_1030_, 3);
lean_inc_ref(v_modules_1061_);
v___x_1062_ = lean_array_get_size(v_modules_1061_);
v___x_1063_ = lean_nat_dec_lt(v_val_1028_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v_modules_1061_);
v___y_1060_ = v___x_1029_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1064_; lean_object* v_toImport_1065_; uint8_t v_isExported_1066_; 
v___x_1064_ = lean_array_fget(v_modules_1061_, v_val_1028_);
lean_dec_ref(v_modules_1061_);
v_toImport_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_toImport_1065_);
lean_dec(v___x_1064_);
v_isExported_1066_ = lean_ctor_get_uint8(v_toImport_1065_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1065_);
if (v_isExported_1066_ == 0)
{
lean_dec(v___x_1026_);
lean_dec_ref(v_env_879_);
lean_del_object(v___x_790_);
lean_dec(v_r_785_);
goto v___jp_1031_;
}
else
{
v___y_1060_ = v___x_1029_;
goto v___jp_1059_;
}
}
v___jp_1031_:
{
lean_object* v_toSignature_1032_; lean_object* v_name_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_toSignature_1032_ = lean_ctor_get(v_origDecl_772_, 0);
lean_inc_ref(v_toSignature_1032_);
lean_dec_ref(v_origDecl_772_);
v_name_1033_ = lean_ctor_get(v_toSignature_1032_, 0);
lean_inc(v_name_1033_);
lean_dec_ref(v_toSignature_1032_);
v___x_1034_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1035_ = l_Lean_MessageData_ofConstName(v_name_1033_, v___x_1029_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_MessageData_ofConstName(v_k_783_, v___x_1029_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_box(0);
v___x_1044_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1030_);
v___x_1045_ = lean_array_get(v___x_1043_, v___x_1044_, v_val_1028_);
lean_dec(v_val_1028_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_MessageData_ofName(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1042_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1049_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
v___jp_1059_:
{
if (v___y_1060_ == 0)
{
lean_dec_ref(v___x_1030_);
lean_dec(v_val_1028_);
v___y_1017_ = v___x_1026_;
v___y_1018_ = v___y_778_;
v___y_1019_ = v___y_779_;
v___y_1020_ = v___y_780_;
v___y_1021_ = v___y_781_;
goto v___jp_1016_;
}
else
{
lean_dec(v___x_1026_);
lean_dec_ref(v_env_879_);
lean_del_object(v___x_790_);
lean_dec(v_r_785_);
goto v___jp_1031_;
}
}
}
else
{
lean_object* v___x_1067_; uint8_t v___y_1069_; lean_object* v_modules_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1067_ = l_Lean_Environment_header(v_env_879_);
v_modules_1097_ = lean_ctor_get(v___x_1067_, 3);
lean_inc_ref(v_modules_1097_);
v___x_1098_ = lean_array_get_size(v_modules_1097_);
v___x_1099_ = lean_nat_dec_lt(v_val_1028_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v_modules_1097_);
v___y_1069_ = v___x_849_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1100_; lean_object* v_toImport_1101_; uint8_t v_isExported_1102_; 
v___x_1100_ = lean_array_fget(v_modules_1097_, v_val_1028_);
lean_dec_ref(v_modules_1097_);
v_toImport_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_toImport_1101_);
lean_dec(v___x_1100_);
v_isExported_1102_ = lean_ctor_get_uint8(v_toImport_1101_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1101_);
if (v_isExported_1102_ == 0)
{
v___y_1069_ = v___x_1029_;
goto v___jp_1068_;
}
else
{
v___y_1069_ = v___x_849_;
goto v___jp_1068_;
}
}
v___jp_1068_:
{
if (v___y_1069_ == 0)
{
lean_dec_ref(v___x_1067_);
lean_dec(v_val_1028_);
v___y_1017_ = v___x_1026_;
v___y_1018_ = v___y_778_;
v___y_1019_ = v___y_779_;
v___y_1020_ = v___y_780_;
v___y_1021_ = v___y_781_;
goto v___jp_1016_;
}
else
{
lean_object* v_toSignature_1070_; lean_object* v_name_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v___x_1026_);
lean_dec_ref(v_env_879_);
lean_del_object(v___x_790_);
lean_dec(v_r_785_);
v_toSignature_1070_ = lean_ctor_get(v_origDecl_772_, 0);
lean_inc_ref(v_toSignature_1070_);
lean_dec_ref(v_origDecl_772_);
v_name_1071_ = lean_ctor_get(v_toSignature_1070_, 0);
lean_inc(v_name_1071_);
lean_dec_ref(v_toSignature_1070_);
v___x_1072_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1073_ = l_Lean_MessageData_ofConstName(v_name_1071_, v___x_849_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_MessageData_ofConstName(v_k_783_, v___x_849_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1067_);
v___x_1083_ = lean_array_get(v___x_1081_, v___x_1082_, v_val_1028_);
lean_dec(v_val_1028_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l_Lean_MessageData_ofName(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1080_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1087_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1027_);
v___y_1017_ = v___x_1026_;
v___y_1018_ = v___y_778_;
v___y_1019_ = v___y_779_;
v___y_1020_ = v___y_780_;
v___y_1021_ = v___y_781_;
goto v___jp_1016_;
}
}
}
v___jp_880_:
{
lean_object* v_toSignature_887_; lean_object* v_name_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_toSignature_887_ = lean_ctor_get(v_origDecl_772_, 0);
lean_inc_ref(v_toSignature_887_);
lean_dec_ref(v_origDecl_772_);
v_name_888_ = lean_ctor_get(v_toSignature_887_, 0);
lean_inc(v_name_888_);
lean_dec_ref(v_toSignature_887_);
v___x_889_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_890_ = l_Lean_MessageData_ofConstName(v_name_888_, v___x_849_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Lean_MessageData_ofConstName(v_k_783_, v___x_849_);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_box(0);
v___x_899_ = l_Lean_Environment_header(v_env_879_);
lean_dec_ref(v_env_879_);
v___x_900_ = l_Lean_EnvironmentHeader_moduleNames(v___x_899_);
v___x_901_ = lean_array_get(v___x_898_, v___x_900_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___x_900_);
v___x_902_ = l_Lean_MessageData_ofName(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_897_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_905_, v___y_882_, v___y_881_, v___y_886_, v___y_885_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
v___jp_915_:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_879_, v_k_783_);
if (lean_obj_tag(v___x_921_) == 1)
{
lean_object* v_val_922_; uint8_t v___x_923_; 
v_val_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v___x_921_, 1);
lean_inc(v_k_783_);
lean_inc_ref(v_env_879_);
v___x_923_ = l_Lean_isMarkedMeta(v_env_879_, v_k_783_);
if (v___x_923_ == 0)
{
lean_del_object(v___x_790_);
v___y_881_ = v___y_917_;
v___y_882_ = v___y_916_;
v___y_883_ = v___y_918_;
v___y_884_ = v_val_922_;
v___y_885_ = v___y_919_;
v___y_886_ = v___y_920_;
goto v___jp_880_;
}
else
{
if (v___x_849_ == 0)
{
lean_dec(v_val_922_);
lean_dec_ref(v_env_879_);
v___y_851_ = v___y_918_;
v___y_852_ = v___y_916_;
v___y_853_ = v___y_917_;
v___y_854_ = v___y_920_;
v___y_855_ = v___y_919_;
goto v___jp_850_;
}
else
{
lean_del_object(v___x_790_);
v___y_881_ = v___y_917_;
v___y_882_ = v___y_916_;
v___y_883_ = v___y_918_;
v___y_884_ = v_val_922_;
v___y_885_ = v___y_919_;
v___y_886_ = v___y_920_;
goto v___jp_880_;
}
}
}
else
{
lean_dec(v___x_921_);
lean_dec_ref(v_env_879_);
v___y_851_ = v___y_918_;
v___y_852_ = v___y_916_;
v___y_853_ = v___y_917_;
v___y_854_ = v___y_920_;
v___y_855_ = v___y_919_;
goto v___jp_850_;
}
}
v___jp_924_:
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = 1;
v___x_932_ = l_Lean_instBEqIRPhases_beq(v___y_928_, v___x_931_);
if (v___x_932_ == 0)
{
lean_dec_ref(v_env_879_);
lean_del_object(v___x_790_);
v___y_838_ = v___y_928_;
v___y_839_ = v___y_927_;
v___y_840_ = v___y_926_;
v___y_841_ = v___y_925_;
v___y_842_ = v___y_930_;
v___y_843_ = v___y_929_;
goto v___jp_837_;
}
else
{
if (v_isMeta_773_ == 0)
{
lean_dec(v___y_927_);
lean_dec(v_r_785_);
v___y_916_ = v___y_926_;
v___y_917_ = v___y_925_;
v___y_918_ = v___y_928_;
v___y_919_ = v___y_929_;
v___y_920_ = v___y_930_;
goto v___jp_915_;
}
else
{
if (v___x_849_ == 0)
{
lean_dec_ref(v_env_879_);
lean_del_object(v___x_790_);
v___y_838_ = v___y_928_;
v___y_839_ = v___y_927_;
v___y_840_ = v___y_926_;
v___y_841_ = v___y_925_;
v___y_842_ = v___y_930_;
v___y_843_ = v___y_929_;
goto v___jp_837_;
}
else
{
lean_dec(v___y_927_);
lean_dec(v_r_785_);
v___y_916_ = v___y_926_;
v___y_917_ = v___y_925_;
v___y_918_ = v___y_928_;
v___y_919_ = v___y_929_;
v___y_920_ = v___y_930_;
goto v___jp_915_;
}
}
}
}
v___jp_933_:
{
if (v___x_849_ == 0)
{
lean_dec_ref(v_env_879_);
lean_del_object(v___x_790_);
v___y_838_ = v___y_934_;
v___y_839_ = v___y_935_;
v___y_840_ = v___y_936_;
v___y_841_ = v___y_937_;
v___y_842_ = v___y_938_;
v___y_843_ = v___y_939_;
goto v___jp_837_;
}
else
{
v___y_925_ = v___y_937_;
v___y_926_ = v___y_936_;
v___y_927_ = v___y_935_;
v___y_928_ = v___y_934_;
v___y_929_ = v___y_939_;
v___y_930_ = v___y_938_;
goto v___jp_924_;
}
}
v___jp_940_:
{
if (v___y_941_ == 0)
{
v___y_925_ = v___y_945_;
v___y_926_ = v___y_944_;
v___y_927_ = v___y_943_;
v___y_928_ = v___y_942_;
v___y_929_ = v___y_947_;
v___y_930_ = v___y_946_;
goto v___jp_924_;
}
else
{
v___y_934_ = v___y_942_;
v___y_935_ = v___y_943_;
v___y_936_ = v___y_944_;
v___y_937_ = v___y_945_;
v___y_938_ = v___y_946_;
v___y_939_ = v___y_947_;
goto v___jp_933_;
}
}
v___jp_948_:
{
uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = 0;
v___x_957_ = l_Lean_instBEqIRPhases_beq(v___y_952_, v___x_956_);
if (v___x_957_ == 0)
{
v___y_941_ = v___y_951_;
v___y_942_ = v___y_952_;
v___y_943_ = v___y_953_;
v___y_944_ = v___y_955_;
v___y_945_ = v___y_954_;
v___y_946_ = v___y_949_;
v___y_947_ = v___y_950_;
goto v___jp_940_;
}
else
{
if (v_isMeta_773_ == 0)
{
v___y_941_ = v___y_951_;
v___y_942_ = v___y_952_;
v___y_943_ = v___y_953_;
v___y_944_ = v___y_955_;
v___y_945_ = v___y_954_;
v___y_946_ = v___y_949_;
v___y_947_ = v___y_950_;
goto v___jp_940_;
}
else
{
lean_object* v___x_958_; 
lean_dec(v___y_953_);
lean_del_object(v___x_790_);
lean_dec(v_r_785_);
v___x_958_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_879_, v_k_783_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v_toSignature_959_; lean_object* v_val_960_; lean_object* v_name_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_toSignature_959_ = lean_ctor_get(v_origDecl_772_, 0);
lean_inc_ref(v_toSignature_959_);
lean_dec_ref(v_origDecl_772_);
v_val_960_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v___x_958_, 1);
v_name_961_ = lean_ctor_get(v_toSignature_959_, 0);
lean_inc(v_name_961_);
lean_dec_ref(v_toSignature_959_);
v___x_962_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_963_ = l_Lean_MessageData_ofConstName(v_name_961_, v___x_849_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_MessageData_ofConstName(v_k_783_, v___x_849_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_box(0);
v___x_972_ = l_Lean_Environment_header(v_env_879_);
lean_dec_ref(v_env_879_);
v___x_973_ = l_Lean_EnvironmentHeader_moduleNames(v___x_972_);
v___x_974_ = lean_array_get(v___x_971_, v___x_973_, v_val_960_);
lean_dec(v_val_960_);
lean_dec_ref(v___x_973_);
v___x_975_ = l_Lean_MessageData_ofName(v___x_974_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_970_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_978_, v___y_955_, v___y_954_, v___y_949_, v___y_950_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_toSignature_988_; lean_object* v_name_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v___x_958_);
lean_dec_ref(v_env_879_);
v_toSignature_988_ = lean_ctor_get(v_origDecl_772_, 0);
lean_inc_ref(v_toSignature_988_);
lean_dec_ref(v_origDecl_772_);
v_name_989_ = lean_ctor_get(v_toSignature_988_, 0);
lean_inc(v_name_989_);
lean_dec_ref(v_toSignature_988_);
v___x_990_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_991_ = l_Lean_MessageData_ofConstName(v_name_989_, v___x_849_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_MessageData_ofConstName(v_k_783_, v___x_849_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_998_, v___y_955_, v___y_954_, v___y_949_, v___y_950_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
v___jp_1008_:
{
uint8_t v___x_1015_; 
lean_inc(v_k_783_);
lean_inc_ref(v_env_879_);
v___x_1015_ = l_Lean_getIRPhases(v_env_879_, v_k_783_);
if (v___y_1014_ == 0)
{
v___y_949_ = v___y_1009_;
v___y_950_ = v___y_1010_;
v___y_951_ = v___y_1014_;
v___y_952_ = v___x_1015_;
v___y_953_ = v___y_1011_;
v___y_954_ = v___y_1012_;
v___y_955_ = v___y_1013_;
goto v___jp_948_;
}
else
{
if (v___x_849_ == 0)
{
v___y_934_ = v___x_1015_;
v___y_935_ = v___y_1011_;
v___y_936_ = v___y_1013_;
v___y_937_ = v___y_1012_;
v___y_938_ = v___y_1009_;
v___y_939_ = v___y_1010_;
goto v___jp_933_;
}
else
{
v___y_949_ = v___y_1009_;
v___y_950_ = v___y_1010_;
v___y_951_ = v___y_1014_;
v___y_952_ = v___x_1015_;
v___y_953_ = v___y_1011_;
v___y_954_ = v___y_1012_;
v___y_955_ = v___y_1013_;
goto v___jp_948_;
}
}
}
v___jp_1016_:
{
lean_object* v_options_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_options_1022_ = lean_ctor_get(v___y_1020_, 2);
v___x_1023_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_1024_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
v___y_1009_ = v___y_1020_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v___y_1017_;
v___y_1012_ = v___y_1019_;
v___y_1013_ = v___y_1018_;
v___y_1014_ = v___x_1024_;
goto v___jp_1008_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Lean_Environment_isImportedConst(v_env_879_, v_k_783_);
if (v___x_1025_ == 0)
{
v___y_1009_ = v___y_1020_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v___y_1017_;
v___y_1012_ = v___y_1019_;
v___y_1013_ = v___y_1018_;
v___y_1014_ = v___x_1024_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v___y_1020_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v___y_1017_;
v___y_1012_ = v___y_1019_;
v___y_1013_ = v___y_1018_;
v___y_1014_ = v___x_849_;
goto v___jp_1008_;
}
}
}
}
else
{
lean_del_object(v___x_790_);
lean_dec(v_k_783_);
v_init_775_ = v___x_792_;
v_x_776_ = v_r_785_;
v___y_777_ = v_snd_788_;
goto _start;
}
v___jp_793_:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; uint8_t v___x_801_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = lean_unbox(v_a_800_);
v___x_802_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_783_, v___x_801_, v___y_797_);
lean_dec(v_k_783_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
if (lean_obj_tag(v_a_803_) == 1)
{
lean_object* v_val_804_; uint8_t v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_val_804_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_a_803_, 1);
v___x_805_ = lean_unbox(v_a_800_);
lean_dec(v_a_800_);
v___x_806_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_805_);
v___x_807_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_806_, v_val_804_, v_pu_771_);
lean_dec(v_val_804_);
lean_inc_ref(v_origDecl_772_);
v___x_808_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_771_, v_origDecl_772_, v_isMeta_773_, v_isPublic_774_, v___x_807_, v___y_796_, v___y_798_, v___y_795_, v___y_794_, v___y_797_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_snd_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_snd_810_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_810_);
lean_dec(v_a_809_);
v_init_775_ = v___x_792_;
v_x_776_ = v_r_785_;
v___y_777_ = v_snd_810_;
goto _start;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_r_785_);
lean_dec_ref(v_origDecl_772_);
v_a_812_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_808_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_dec(v_a_803_);
lean_dec(v_a_800_);
v_init_775_ = v___x_792_;
v_x_776_ = v_r_785_;
v___y_777_ = v___y_796_;
goto _start;
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_800_);
lean_dec(v___y_796_);
lean_dec(v_r_785_);
lean_dec_ref(v_origDecl_772_);
v_a_821_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_802_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_802_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v___y_796_);
lean_dec(v_r_785_);
lean_dec(v_k_783_);
lean_dec_ref(v_origDecl_772_);
v_a_829_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_799_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_799_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
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
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
v___jp_837_:
{
uint8_t v___x_844_; uint8_t v___x_845_; 
v___x_844_ = 2;
v___x_845_ = l_Lean_instBEqIRPhases_beq(v___y_838_, v___x_844_);
if (v___x_845_ == 0)
{
if (v_isPublic_774_ == 0)
{
lean_dec(v_k_783_);
v_init_775_ = v___x_792_;
v_x_776_ = v_r_785_;
v___y_777_ = v___y_839_;
goto _start;
}
else
{
uint8_t v___x_847_; 
v___x_847_ = l_Lean_isPrivateName(v_k_783_);
if (v___x_847_ == 0)
{
lean_dec(v_k_783_);
v_init_775_ = v___x_792_;
v_x_776_ = v_r_785_;
v___y_777_ = v___y_839_;
goto _start;
}
else
{
v___y_794_ = v___y_842_;
v___y_795_ = v___y_841_;
v___y_796_ = v___y_839_;
v___y_797_ = v___y_843_;
v___y_798_ = v___y_840_;
goto v___jp_793_;
}
}
}
else
{
v___y_794_ = v___y_842_;
v___y_795_ = v___y_841_;
v___y_796_ = v___y_839_;
v___y_797_ = v___y_843_;
v___y_798_ = v___y_840_;
goto v___jp_793_;
}
}
v___jp_850_:
{
lean_object* v_toSignature_856_; lean_object* v_name_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v_toSignature_856_ = lean_ctor_get(v_origDecl_772_, 0);
lean_inc_ref(v_toSignature_856_);
lean_dec_ref(v_origDecl_772_);
v_name_857_ = lean_ctor_get(v_toSignature_856_, 0);
lean_inc(v_name_857_);
lean_dec_ref(v_toSignature_856_);
v___x_858_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_859_ = l_Lean_MessageData_ofConstName(v_name_857_, v___x_849_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 7);
lean_ctor_set(v___x_790_, 1, v___x_859_);
lean_ctor_set(v___x_790_, 0, v___x_858_);
v___x_861_ = v___x_790_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_877_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v___x_862_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_MessageData_ofConstName(v_k_783_, v___x_849_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_867_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
else
{
lean_dec(v_r_785_);
lean_dec(v_k_783_);
lean_dec_ref(v_origDecl_772_);
return v___x_786_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_origDecl_772_);
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_init_775_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___y_777_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t v_pu_1109_, lean_object* v_origDecl_1110_, uint8_t v_isMeta_1111_, uint8_t v_isPublic_1112_, lean_object* v_code_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = l_Lean_NameSet_empty;
v___x_1121_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_1109_, v_code_1113_, v___x_1120_);
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_1109_, v_origDecl_1110_, v_isMeta_1111_, v_isPublic_1112_, v___x_1122_, v___x_1121_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1140_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1140_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1140_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1138_; 
v_snd_1128_ = lean_ctor_get(v_a_1124_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v_a_1124_, 0);
lean_dec(v_unused_1139_);
v___x_1130_ = v_a_1124_;
v_isShared_1131_ = v_isSharedCheck_1138_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_dec(v_a_1124_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1138_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1122_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_snd_1128_);
v___x_1133_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1133_);
v___x_1135_ = v___x_1126_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1123_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1123_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object* v_pu_1149_, lean_object* v_origDecl_1150_, lean_object* v_isMeta_1151_, lean_object* v_isPublic_1152_, lean_object* v_code_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
uint8_t v_pu_boxed_1160_; uint8_t v_isMeta_boxed_1161_; uint8_t v_isPublic_boxed_1162_; lean_object* v_res_1163_; 
v_pu_boxed_1160_ = lean_unbox(v_pu_1149_);
v_isMeta_boxed_1161_ = lean_unbox(v_isMeta_1151_);
v_isPublic_boxed_1162_ = lean_unbox(v_isPublic_1152_);
v_res_1163_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_boxed_1160_, v_origDecl_1150_, v_isMeta_boxed_1161_, v_isPublic_boxed_1162_, v_code_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t v_pu_1164_, lean_object* v_origDecl_1165_, uint8_t v_isMeta_1166_, uint8_t v_isPublic_1167_, lean_object* v_decl_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_value_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
v_value_1175_ = lean_ctor_get(v_decl_1168_, 1);
lean_inc_ref(v_value_1175_);
lean_dec_ref(v_decl_1168_);
v___x_1176_ = lean_box(v_pu_1164_);
v___x_1177_ = lean_box(v_isMeta_1166_);
v___x_1178_ = lean_box(v_isPublic_1167_);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1179_, 0, v___x_1176_);
lean_closure_set(v___f_1179_, 1, v_origDecl_1165_);
lean_closure_set(v___f_1179_, 2, v___x_1177_);
lean_closure_set(v___f_1179_, 3, v___x_1178_);
v___x_1180_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_1179_, v_value_1175_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object* v_pu_1181_, lean_object* v_origDecl_1182_, lean_object* v_isMeta_1183_, lean_object* v_isPublic_1184_, lean_object* v_decl_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_pu_boxed_1192_; uint8_t v_isMeta_boxed_1193_; uint8_t v_isPublic_boxed_1194_; lean_object* v_res_1195_; 
v_pu_boxed_1192_ = lean_unbox(v_pu_1181_);
v_isMeta_boxed_1193_ = lean_unbox(v_isMeta_1183_);
v_isPublic_boxed_1194_ = lean_unbox(v_isPublic_1184_);
v_res_1195_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_boxed_1192_, v_origDecl_1182_, v_isMeta_boxed_1193_, v_isPublic_boxed_1194_, v_decl_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object* v_pu_1196_, lean_object* v_origDecl_1197_, lean_object* v_isMeta_1198_, lean_object* v_isPublic_1199_, lean_object* v_init_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v_pu_boxed_1208_; uint8_t v_isMeta_boxed_1209_; uint8_t v_isPublic_boxed_1210_; lean_object* v_res_1211_; 
v_pu_boxed_1208_ = lean_unbox(v_pu_1196_);
v_isMeta_boxed_1209_ = lean_unbox(v_isMeta_1198_);
v_isPublic_boxed_1210_ = lean_unbox(v_isPublic_1199_);
v_res_1211_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_1208_, v_origDecl_1197_, v_isMeta_boxed_1209_, v_isPublic_boxed_1210_, v_init_1200_, v_x_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object* v_opt_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_options_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_options_1215_ = lean_ctor_get(v___y_1213_, 2);
v___x_1216_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1215_, v_opt_1212_);
v___x_1217_ = lean_box(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1219_, v___y_1220_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v_opt_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1223_, lean_object* v_origDecl_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1290_; 
v___x_1230_ = lean_st_ref_get(v_a_1228_);
v___x_1231_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1232_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1231_, v_a_1227_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1290_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1290_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1289_; 
v___x_1237_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1238_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1237_, v_a_1227_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1289_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1289_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_env_1248_; lean_object* v___x_1249_; uint8_t v_isModule_1250_; 
v_env_1248_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1248_);
lean_dec(v___x_1230_);
v___x_1249_ = l_Lean_Environment_header(v_env_1248_);
lean_dec_ref(v_env_1248_);
v_isModule_1250_ = lean_ctor_get_uint8(v___x_1249_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1249_);
if (v_isModule_1250_ == 0)
{
lean_dec(v_a_1239_);
lean_del_object(v___x_1235_);
lean_dec(v_a_1233_);
lean_dec_ref(v_origDecl_1224_);
goto v___jp_1243_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_unbox(v_a_1233_);
lean_dec(v_a_1233_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_unbox(v_a_1239_);
if (v___x_1252_ == 0)
{
lean_dec(v_a_1239_);
lean_del_object(v___x_1235_);
lean_dec_ref(v_origDecl_1224_);
goto v___jp_1243_;
}
else
{
lean_object* v___x_1253_; lean_object* v_toSignature_1254_; lean_object* v_env_1255_; lean_object* v_name_1256_; uint8_t v___x_1257_; uint8_t v___y_1259_; uint8_t v___x_1281_; uint8_t v___x_1282_; 
lean_del_object(v___x_1241_);
v___x_1253_ = lean_st_ref_get(v_a_1228_);
v_toSignature_1254_ = lean_ctor_get(v_origDecl_1224_, 0);
v_env_1255_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref(v_env_1255_);
lean_dec(v___x_1253_);
v_name_1256_ = lean_ctor_get(v_toSignature_1254_, 0);
lean_inc(v_name_1256_);
v___x_1257_ = l_Lean_getIRPhases(v_env_1255_, v_name_1256_);
v___x_1281_ = 2;
v___x_1282_ = l_Lean_instBEqIRPhases_beq(v___x_1257_, v___x_1281_);
if (v___x_1282_ == 0)
{
uint8_t v___x_1283_; 
lean_del_object(v___x_1235_);
v___x_1283_ = l_Lean_isPrivateName(v_name_1256_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_unbox(v_a_1239_);
lean_dec(v_a_1239_);
v___y_1259_ = v___x_1284_;
goto v___jp_1258_;
}
else
{
lean_dec(v_a_1239_);
v___y_1259_ = v___x_1282_;
goto v___jp_1258_;
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_dec(v_a_1239_);
lean_dec_ref(v_origDecl_1224_);
v___x_1285_ = lean_box(0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1285_);
v___x_1287_ = v___x_1235_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
v___jp_1258_:
{
uint8_t v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = 1;
v___x_1261_ = l_Lean_instBEqIRPhases_beq(v___x_1257_, v___x_1260_);
v___x_1262_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1224_);
v___x_1263_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1223_, v_origDecl_1224_, v___x_1261_, v___y_1259_, v_origDecl_1224_, v___x_1262_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1272_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_fst_1268_; lean_object* v___x_1270_; 
v_fst_1268_ = lean_ctor_get(v_a_1264_, 0);
lean_inc(v_fst_1268_);
lean_dec(v_a_1264_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_fst_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1273_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1263_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1263_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1239_);
lean_del_object(v___x_1235_);
lean_dec_ref(v_origDecl_1224_);
goto v___jp_1243_;
}
}
v___jp_1243_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = lean_box(0);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1291_, lean_object* v_origDecl_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
uint8_t v_pu_boxed_1298_; lean_object* v_res_1299_; 
v_pu_boxed_1298_ = lean_unbox(v_pu_1291_);
v_res_1299_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1298_, v_origDecl_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1300_, v___y_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v_opt_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(uint8_t v_isExporting_1314_, lean_object* v___x_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; lean_object* v_env_1324_; lean_object* v_nextMacroScope_1325_; lean_object* v_ngen_1326_; lean_object* v_auxDeclNGen_1327_; lean_object* v_traceState_1328_; lean_object* v_messages_1329_; lean_object* v_infoState_1330_; lean_object* v_snapshotTasks_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1343_; 
v___x_1323_ = lean_st_ref_take(v___y_1321_);
v_env_1324_ = lean_ctor_get(v___x_1323_, 0);
v_nextMacroScope_1325_ = lean_ctor_get(v___x_1323_, 1);
v_ngen_1326_ = lean_ctor_get(v___x_1323_, 2);
v_auxDeclNGen_1327_ = lean_ctor_get(v___x_1323_, 3);
v_traceState_1328_ = lean_ctor_get(v___x_1323_, 4);
v_messages_1329_ = lean_ctor_get(v___x_1323_, 6);
v_infoState_1330_ = lean_ctor_get(v___x_1323_, 7);
v_snapshotTasks_1331_ = lean_ctor_get(v___x_1323_, 8);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1323_, 5);
lean_dec(v_unused_1344_);
v___x_1333_ = v___x_1323_;
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_snapshotTasks_1331_);
lean_inc(v_infoState_1330_);
lean_inc(v_messages_1329_);
lean_inc(v_traceState_1328_);
lean_inc(v_auxDeclNGen_1327_);
lean_inc(v_ngen_1326_);
lean_inc(v_nextMacroScope_1325_);
lean_inc(v_env_1324_);
lean_dec(v___x_1323_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = l_Lean_Environment_setExporting(v_env_1324_, v_isExporting_1314_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 5, v___x_1315_);
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_nextMacroScope_1325_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_ngen_1326_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_auxDeclNGen_1327_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_traceState_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 5, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1342_, 6, v_messages_1329_);
lean_ctor_set(v_reuseFailAlloc_1342_, 7, v_infoState_1330_);
lean_ctor_set(v_reuseFailAlloc_1342_, 8, v_snapshotTasks_1331_);
v___x_1337_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1338_ = lean_st_ref_set(v___y_1321_, v___x_1337_);
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___y_1317_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(lean_object* v_isExporting_1345_, lean_object* v___x_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v_isExporting_boxed_1354_; lean_object* v_res_1355_; 
v_isExporting_boxed_1354_ = lean_unbox(v_isExporting_1345_);
v_res_1355_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_boxed_1354_, v___x_1346_, v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v_x_1347_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(lean_object* v___f_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v_a_x3f_1362_){
_start:
{
if (lean_obj_tag(v_a_x3f_1362_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_box(0);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
v___x_1365_ = lean_apply_7(v___f_1356_, v___x_1364_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, lean_box(0));
return v___x_1365_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v___y_1357_);
v_val_1366_ = lean_ctor_get(v_a_x3f_1362_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_a_x3f_1362_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1368_ = v_a_x3f_1362_;
v_isShared_1369_ = v_isSharedCheck_1376_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v_a_x3f_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1376_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; 
v_fst_1370_ = lean_ctor_get(v_val_1366_, 0);
lean_inc(v_fst_1370_);
v_snd_1371_ = lean_ctor_get(v_val_1366_, 1);
lean_inc(v_snd_1371_);
lean_dec(v_val_1366_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_fst_1370_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_fst_1370_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
v___x_1374_ = lean_apply_7(v___f_1356_, v___x_1373_, v_snd_1371_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, lean_box(0));
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(lean_object* v___f_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v_a_x3f_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v_a_x3f_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object* v_x_1386_, uint8_t v_isExporting_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v_env_1395_; uint8_t v_isExporting_1396_; lean_object* v___x_1475_; uint8_t v_isModule_1476_; 
v___x_1394_ = lean_st_ref_get(v___y_1392_);
v_env_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_env_1395_);
lean_dec(v___x_1394_);
v_isExporting_1396_ = lean_ctor_get_uint8(v_env_1395_, sizeof(void*)*8);
v___x_1475_ = l_Lean_Environment_header(v_env_1395_);
lean_dec_ref(v_env_1395_);
v_isModule_1476_ = lean_ctor_get_uint8(v___x_1475_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1475_);
if (v_isModule_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
v___x_1477_ = lean_apply_6(v_x_1386_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, lean_box(0));
return v___x_1477_;
}
else
{
if (v_isExporting_1396_ == 0)
{
if (v_isExporting_1387_ == 0)
{
lean_object* v___x_1478_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
v___x_1478_ = lean_apply_6(v_x_1386_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, lean_box(0));
return v___x_1478_;
}
else
{
goto v___jp_1397_;
}
}
else
{
if (v_isExporting_1387_ == 0)
{
goto v___jp_1397_;
}
else
{
lean_object* v___x_1479_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
v___x_1479_ = lean_apply_6(v_x_1386_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, lean_box(0));
return v___x_1479_;
}
}
}
v___jp_1397_:
{
lean_object* v___x_1398_; lean_object* v_env_1399_; lean_object* v_nextMacroScope_1400_; lean_object* v_ngen_1401_; lean_object* v_auxDeclNGen_1402_; lean_object* v_traceState_1403_; lean_object* v_messages_1404_; lean_object* v_infoState_1405_; lean_object* v_snapshotTasks_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1473_; 
v___x_1398_ = lean_st_ref_take(v___y_1392_);
v_env_1399_ = lean_ctor_get(v___x_1398_, 0);
v_nextMacroScope_1400_ = lean_ctor_get(v___x_1398_, 1);
v_ngen_1401_ = lean_ctor_get(v___x_1398_, 2);
v_auxDeclNGen_1402_ = lean_ctor_get(v___x_1398_, 3);
v_traceState_1403_ = lean_ctor_get(v___x_1398_, 4);
v_messages_1404_ = lean_ctor_get(v___x_1398_, 6);
v_infoState_1405_ = lean_ctor_get(v___x_1398_, 7);
v_snapshotTasks_1406_ = lean_ctor_get(v___x_1398_, 8);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v___x_1398_, 5);
lean_dec(v_unused_1474_);
v___x_1408_ = v___x_1398_;
v_isShared_1409_ = v_isSharedCheck_1473_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_snapshotTasks_1406_);
lean_inc(v_infoState_1405_);
lean_inc(v_messages_1404_);
lean_inc(v_traceState_1403_);
lean_inc(v_auxDeclNGen_1402_);
lean_inc(v_ngen_1401_);
lean_inc(v_nextMacroScope_1400_);
lean_inc(v_env_1399_);
lean_dec(v___x_1398_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1473_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1410_ = l_Lean_Environment_setExporting(v_env_1399_, v_isExporting_1387_);
v___x_1411_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 5, v___x_1411_);
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_nextMacroScope_1400_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_ngen_1401_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_auxDeclNGen_1402_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_traceState_1403_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_messages_1404_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_infoState_1405_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v_snapshotTasks_1406_);
v___x_1413_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v_r_1417_; 
v___x_1414_ = lean_st_ref_set(v___y_1392_, v___x_1413_);
v___x_1415_ = lean_box(v_isExporting_1396_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1416_, 0, v___x_1415_);
lean_closure_set(v___f_1416_, 1, v___x_1411_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1388_);
v_r_1417_ = lean_apply_6(v_x_1386_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, lean_box(0));
if (lean_obj_tag(v_r_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1452_; 
v_a_1418_ = lean_ctor_get(v_r_1417_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_r_1417_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1420_ = v_r_1417_;
v_isShared_1421_ = v_isSharedCheck_1452_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v_r_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1452_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
lean_inc(v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 1);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1416_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___x_1423_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1442_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1442_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1442_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1440_; 
v_fst_1429_ = lean_ctor_get(v_a_1418_, 0);
lean_inc(v_fst_1429_);
lean_dec(v_a_1418_);
v_snd_1430_ = lean_ctor_get(v_a_1425_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_a_1425_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_a_1425_, 0);
lean_dec(v_unused_1441_);
v___x_1432_ = v_a_1425_;
v_isShared_1433_ = v_isSharedCheck_1440_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_dec(v_a_1425_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1440_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_fst_1429_);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_snd_1430_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1435_);
v___x_1437_ = v___x_1427_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1418_);
v_a_1443_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1424_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1424_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_a_1453_ = lean_ctor_get(v_r_1417_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v_r_1417_, 1);
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1416_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___x_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1455_, 0);
lean_dec(v_unused_1463_);
v___x_1457_ = v___x_1455_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v___x_1455_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 1);
lean_ctor_set(v___x_1457_, 0, v_a_1453_);
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1453_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1453_);
v_a_1464_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1455_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1455_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_x_1480_, lean_object* v_isExporting_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_isExporting_boxed_1488_; lean_object* v_res_1489_; 
v_isExporting_boxed_1488_ = lean_unbox(v_isExporting_1481_);
v_res_1489_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1480_, v_isExporting_boxed_1488_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_00_u03b1_1490_, lean_object* v_x_1491_, uint8_t v_isExporting_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1491_, v_isExporting_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_x_1501_, lean_object* v_isExporting_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_isExporting_boxed_1509_; lean_object* v_res_1510_; 
v_isExporting_boxed_1509_ = lean_unbox(v_isExporting_1502_);
v_res_1510_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_1500_, v_x_1501_, v_isExporting_boxed_1509_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(lean_object* v_opt_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_options_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_options_1515_ = lean_ctor_get(v___y_1513_, 2);
v___x_1516_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1515_, v_opt_1511_);
v___x_1517_ = lean_box(v___x_1516_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___y_1512_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(lean_object* v_opt_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v_opt_1520_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(lean_object* v_cls_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_options_1533_; lean_object* v_ref_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_options_1533_ = lean_ctor_get(v___y_1530_, 2);
v_ref_1534_ = lean_ctor_get(v___y_1530_, 5);
v___x_1535_ = lean_st_ref_get(v___y_1531_);
v___x_1536_ = lean_st_ref_get(v___y_1529_);
v___x_1537_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1597_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1597_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1597_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_env_1542_; lean_object* v_lctx_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1595_; 
v_env_1542_ = lean_ctor_get(v___x_1535_, 0);
lean_inc_ref(v_env_1542_);
lean_dec(v___x_1535_);
v_lctx_1543_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1536_, 1);
lean_dec(v_unused_1596_);
v___x_1545_ = v___x_1536_;
v_isShared_1546_ = v_isSharedCheck_1595_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_lctx_1543_);
lean_dec(v___x_1536_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1595_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v_traceState_1549_; lean_object* v_env_1550_; lean_object* v_nextMacroScope_1551_; lean_object* v_ngen_1552_; lean_object* v_auxDeclNGen_1553_; lean_object* v_cache_1554_; lean_object* v_messages_1555_; lean_object* v_infoState_1556_; lean_object* v_snapshotTasks_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1594_; 
v___x_1547_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_1548_ = lean_st_ref_take(v___y_1531_);
v_traceState_1549_ = lean_ctor_get(v___x_1548_, 4);
v_env_1550_ = lean_ctor_get(v___x_1548_, 0);
v_nextMacroScope_1551_ = lean_ctor_get(v___x_1548_, 1);
v_ngen_1552_ = lean_ctor_get(v___x_1548_, 2);
v_auxDeclNGen_1553_ = lean_ctor_get(v___x_1548_, 3);
v_cache_1554_ = lean_ctor_get(v___x_1548_, 5);
v_messages_1555_ = lean_ctor_get(v___x_1548_, 6);
v_infoState_1556_ = lean_ctor_get(v___x_1548_, 7);
v_snapshotTasks_1557_ = lean_ctor_get(v___x_1548_, 8);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1559_ = v___x_1548_;
v_isShared_1560_ = v_isSharedCheck_1594_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snapshotTasks_1557_);
lean_inc(v_infoState_1556_);
lean_inc(v_messages_1555_);
lean_inc(v_cache_1554_);
lean_inc(v_traceState_1549_);
lean_inc(v_auxDeclNGen_1553_);
lean_inc(v_ngen_1552_);
lean_inc(v_nextMacroScope_1551_);
lean_inc(v_env_1550_);
lean_dec(v___x_1548_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1594_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
uint64_t v_tid_1561_; lean_object* v_traces_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1593_; 
v_tid_1561_ = lean_ctor_get_uint64(v_traceState_1549_, sizeof(void*)*1);
v_traces_1562_ = lean_ctor_get(v_traceState_1549_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_traceState_1549_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1564_ = v_traceState_1549_;
v_isShared_1565_ = v_isSharedCheck_1593_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_traces_1562_);
lean_dec(v_traceState_1549_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1593_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1566_ = lean_unbox(v_a_1538_);
lean_dec(v_a_1538_);
v___x_1567_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1543_, v___x_1566_);
lean_dec_ref(v_lctx_1543_);
lean_inc_ref(v_options_1533_);
v___x_1568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1568_, 0, v_env_1542_);
lean_ctor_set(v___x_1568_, 1, v___x_1547_);
lean_ctor_set(v___x_1568_, 2, v___x_1567_);
lean_ctor_set(v___x_1568_, 3, v_options_1533_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 3);
lean_ctor_set(v___x_1545_, 1, v_msg_1526_);
lean_ctor_set(v___x_1545_, 0, v___x_1568_);
v___x_1570_ = v___x_1545_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_msg_1526_);
v___x_1570_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1571_; double v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_1573_ = 0;
v___x_1574_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1575_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1575_, 0, v_cls_1525_);
lean_ctor_set(v___x_1575_, 1, v___x_1571_);
lean_ctor_set(v___x_1575_, 2, v___x_1574_);
lean_ctor_set_float(v___x_1575_, sizeof(void*)*3, v___x_1572_);
lean_ctor_set_float(v___x_1575_, sizeof(void*)*3 + 8, v___x_1572_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*3 + 16, v___x_1573_);
v___x_1576_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_1577_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1570_);
lean_ctor_set(v___x_1577_, 2, v___x_1576_);
lean_inc(v_ref_1534_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_ref_1534_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_PersistentArray_push___redArg(v_traces_1562_, v___x_1578_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1579_);
v___x_1581_ = v___x_1564_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1579_);
lean_ctor_set_uint64(v_reuseFailAlloc_1591_, sizeof(void*)*1, v_tid_1561_);
v___x_1581_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v___x_1581_);
v___x_1583_ = v___x_1559_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_env_1550_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_nextMacroScope_1551_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_ngen_1552_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_auxDeclNGen_1553_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 5, v_cache_1554_);
lean_ctor_set(v_reuseFailAlloc_1590_, 6, v_messages_1555_);
lean_ctor_set(v_reuseFailAlloc_1590_, 7, v_infoState_1556_);
lean_ctor_set(v_reuseFailAlloc_1590_, 8, v_snapshotTasks_1557_);
v___x_1583_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1584_ = lean_st_ref_set(v___y_1531_, v___x_1583_);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v___y_1527_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1586_);
v___x_1588_ = v___x_1540_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
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
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v___x_1536_);
lean_dec(v___x_1535_);
lean_dec(v___y_1527_);
lean_dec_ref(v_msg_1526_);
lean_dec(v_cls_1525_);
v_a_1598_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1537_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1537_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7___boxed(lean_object* v_cls_1606_, lean_object* v_msg_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1606_, v_msg_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object* v_keys_1615_, lean_object* v_i_1616_, lean_object* v_k_1617_){
_start:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = lean_array_get_size(v_keys_1615_);
v___x_1619_ = lean_nat_dec_lt(v_i_1616_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_dec(v_i_1616_);
return v___x_1619_;
}
else
{
lean_object* v_k_x27_1620_; uint8_t v___x_1621_; 
v_k_x27_1620_ = lean_array_fget_borrowed(v_keys_1615_, v_i_1616_);
v___x_1621_ = l_Lean_instBEqExtraModUse_beq(v_k_1617_, v_k_x27_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_add(v_i_1616_, v___x_1622_);
lean_dec(v_i_1616_);
v_i_1616_ = v___x_1623_;
goto _start;
}
else
{
lean_dec(v_i_1616_);
return v___x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1625_, lean_object* v_i_1626_, lean_object* v_k_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_1625_, v_i_1626_, v_k_1627_);
lean_dec_ref(v_k_1627_);
lean_dec_ref(v_keys_1625_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1630_, size_t v_x_1631_, lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1630_) == 0)
{
lean_object* v_es_1633_; lean_object* v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; lean_object* v_j_1637_; lean_object* v___x_1638_; 
v_es_1633_ = lean_ctor_get(v_x_1630_, 0);
v___x_1634_ = lean_box(2);
v___x_1635_ = ((size_t)31ULL);
v___x_1636_ = lean_usize_land(v_x_1631_, v___x_1635_);
v_j_1637_ = lean_usize_to_nat(v___x_1636_);
v___x_1638_ = lean_array_get_borrowed(v___x_1634_, v_es_1633_, v_j_1637_);
lean_dec(v_j_1637_);
switch(lean_obj_tag(v___x_1638_))
{
case 0:
{
lean_object* v_key_1639_; uint8_t v___x_1640_; 
v_key_1639_ = lean_ctor_get(v___x_1638_, 0);
v___x_1640_ = l_Lean_instBEqExtraModUse_beq(v_x_1632_, v_key_1639_);
return v___x_1640_;
}
case 1:
{
lean_object* v_node_1641_; size_t v___x_1642_; size_t v___x_1643_; 
v_node_1641_ = lean_ctor_get(v___x_1638_, 0);
v___x_1642_ = ((size_t)5ULL);
v___x_1643_ = lean_usize_shift_right(v_x_1631_, v___x_1642_);
v_x_1630_ = v_node_1641_;
v_x_1631_ = v___x_1643_;
goto _start;
}
default: 
{
uint8_t v___x_1645_; 
v___x_1645_ = 0;
return v___x_1645_;
}
}
}
else
{
lean_object* v_ks_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_ks_1646_ = lean_ctor_get(v_x_1630_, 0);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_1646_, v___x_1647_, v_x_1632_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
size_t v_x_29724__boxed_1652_; uint8_t v_res_1653_; lean_object* v_r_1654_; 
v_x_29724__boxed_1652_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_res_1653_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1649_, v_x_29724__boxed_1652_, v_x_1651_);
lean_dec_ref(v_x_1651_);
lean_dec_ref(v_x_1649_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
uint64_t v___x_1657_; size_t v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = l_Lean_instHashableExtraModUse_hash(v_x_1656_);
v___x_1658_ = lean_uint64_to_usize(v___x_1657_);
v___x_1659_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1655_, v___x_1658_, v_x_1656_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
uint8_t v_res_1662_; lean_object* v_r_1663_; 
v_res_1662_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_1660_, v_x_1661_);
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_x_1660_);
v_r_1663_ = lean_box(v_res_1662_);
return v_r_1663_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1));
v___x_1667_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0));
v___x_1668_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_cls_1680_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4));
v___x_1681_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1682_ = l_Lean_Name_append(v___x_1681_, v_cls_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13));
v___x_1688_ = l_Lean_stringToMessageData(v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object* v_mod_1693_, uint8_t v_isMeta_1694_, lean_object* v_hint_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v_env_1703_; uint8_t v_isExporting_1704_; lean_object* v___x_1705_; lean_object* v_env_1706_; lean_object* v___x_1707_; lean_object* v_entry_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1702_ = lean_st_ref_get(v___y_1700_);
v_env_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_env_1703_);
lean_dec(v___x_1702_);
v_isExporting_1704_ = lean_ctor_get_uint8(v_env_1703_, sizeof(void*)*8);
lean_dec_ref(v_env_1703_);
v___x_1705_ = lean_st_ref_get(v___y_1700_);
v_env_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_ref(v_env_1706_);
lean_dec(v___x_1705_);
v___x_1707_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2);
lean_inc(v_mod_1693_);
v_entry_1708_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1708_, 0, v_mod_1693_);
lean_ctor_set_uint8(v_entry_1708_, sizeof(void*)*1, v_isExporting_1704_);
lean_ctor_set_uint8(v_entry_1708_, sizeof(void*)*1 + 1, v_isMeta_1694_);
v___x_1709_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1710_ = lean_box(1);
v___x_1711_ = lean_box(0);
v___x_1740_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1707_, v___x_1709_, v_env_1706_, v___x_1710_, v___x_1711_);
v___x_1741_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_1740_, v_entry_1708_);
lean_dec(v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v_options_1742_; uint8_t v_hasTrace_1743_; 
v_options_1742_ = lean_ctor_get(v___y_1699_, 2);
v_hasTrace_1743_ = lean_ctor_get_uint8(v_options_1742_, sizeof(void*)*1);
if (v_hasTrace_1743_ == 0)
{
lean_dec(v_hint_1695_);
lean_dec(v_mod_1693_);
v___y_1713_ = v___y_1696_;
v___y_1714_ = v___y_1700_;
goto v___jp_1712_;
}
else
{
lean_object* v_inheritedTraceOptions_1744_; lean_object* v_cls_1745_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_inheritedTraceOptions_1744_ = lean_ctor_get(v___y_1699_, 13);
v_cls_1745_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4));
v___x_1767_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
v___x_1768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1744_, v_options_1742_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec(v_hint_1695_);
lean_dec(v_mod_1693_);
v___y_1713_ = v___y_1696_;
v___y_1714_ = v___y_1700_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1769_; lean_object* v___y_1771_; 
v___x_1769_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
if (v_isExporting_1704_ == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17));
v___y_1771_ = v___x_1778_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18));
v___y_1771_ = v___x_1779_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc_ref(v___y_1771_);
v___x_1772_ = l_Lean_stringToMessageData(v___y_1771_);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1769_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
if (v_isMeta_1694_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15));
v___y_1754_ = v___x_1775_;
v___y_1755_ = v___x_1776_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16));
v___y_1754_ = v___x_1775_;
v___y_1755_ = v___x_1777_;
goto v___jp_1753_;
}
}
}
v___jp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___y_1747_);
lean_ctor_set(v___x_1749_, 1, v___y_1748_);
v___x_1750_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1745_, v___x_1749_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v_snd_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v_snd_1752_ = lean_ctor_get(v_a_1751_, 1);
lean_inc(v_snd_1752_);
lean_dec(v_a_1751_);
v___y_1713_ = v_snd_1752_;
v___y_1714_ = v___y_1700_;
goto v___jp_1712_;
}
else
{
lean_dec_ref_known(v_entry_1708_, 1);
return v___x_1750_;
}
}
v___jp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
lean_inc_ref(v___y_1755_);
v___x_1756_ = l_Lean_stringToMessageData(v___y_1755_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1754_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = l_Lean_MessageData_ofName(v_mod_1693_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Name_isAnonymous(v_hint_1695_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
v___x_1764_ = l_Lean_MessageData_ofName(v_hint_1695_);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___y_1747_ = v___x_1761_;
v___y_1748_ = v___x_1765_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1766_; 
lean_dec(v_hint_1695_);
v___x_1766_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9);
v___y_1747_ = v___x_1761_;
v___y_1748_ = v___x_1766_;
goto v___jp_1746_;
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref_known(v_entry_1708_, 1);
lean_dec(v_hint_1695_);
lean_dec(v_mod_1693_);
v___x_1780_ = lean_box(0);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___y_1696_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
v___jp_1712_:
{
lean_object* v___x_1715_; lean_object* v_toEnvExtension_1716_; lean_object* v_env_1717_; lean_object* v_nextMacroScope_1718_; lean_object* v_ngen_1719_; lean_object* v_auxDeclNGen_1720_; lean_object* v_traceState_1721_; lean_object* v_messages_1722_; lean_object* v_infoState_1723_; lean_object* v_snapshotTasks_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1738_; 
v___x_1715_ = lean_st_ref_take(v___y_1714_);
v_toEnvExtension_1716_ = lean_ctor_get(v___x_1709_, 0);
v_env_1717_ = lean_ctor_get(v___x_1715_, 0);
v_nextMacroScope_1718_ = lean_ctor_get(v___x_1715_, 1);
v_ngen_1719_ = lean_ctor_get(v___x_1715_, 2);
v_auxDeclNGen_1720_ = lean_ctor_get(v___x_1715_, 3);
v_traceState_1721_ = lean_ctor_get(v___x_1715_, 4);
v_messages_1722_ = lean_ctor_get(v___x_1715_, 6);
v_infoState_1723_ = lean_ctor_get(v___x_1715_, 7);
v_snapshotTasks_1724_ = lean_ctor_get(v___x_1715_, 8);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v___x_1715_, 5);
lean_dec(v_unused_1739_);
v___x_1726_ = v___x_1715_;
v_isShared_1727_ = v_isSharedCheck_1738_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snapshotTasks_1724_);
lean_inc(v_infoState_1723_);
lean_inc(v_messages_1722_);
lean_inc(v_traceState_1721_);
lean_inc(v_auxDeclNGen_1720_);
lean_inc(v_ngen_1719_);
lean_inc(v_nextMacroScope_1718_);
lean_inc(v_env_1717_);
lean_dec(v___x_1715_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1738_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_asyncMode_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v_asyncMode_1728_ = lean_ctor_get(v_toEnvExtension_1716_, 2);
v___x_1729_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1709_, v_env_1717_, v_entry_1708_, v_asyncMode_1728_, v___x_1711_);
v___x_1730_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 5, v___x_1730_);
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1732_ = v___x_1726_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_nextMacroScope_1718_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_ngen_1719_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_auxDeclNGen_1720_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_traceState_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 5, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1737_, 6, v_messages_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 7, v_infoState_1723_);
lean_ctor_set(v_reuseFailAlloc_1737_, 8, v_snapshotTasks_1724_);
v___x_1732_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = lean_st_ref_set(v___y_1714_, v___x_1732_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v___y_1713_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object* v_mod_1783_, lean_object* v_isMeta_1784_, lean_object* v_hint_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_isMeta_boxed_1792_; lean_object* v_res_1793_; 
v_isMeta_boxed_1792_ = lean_unbox(v_isMeta_1784_);
v_res_1793_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_1783_, v_isMeta_boxed_1792_, v_hint_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object* v_a_1794_, lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_box(0);
return v___x_1796_;
}
else
{
lean_object* v_key_1797_; lean_object* v_value_1798_; lean_object* v_tail_1799_; uint8_t v___x_1800_; 
v_key_1797_ = lean_ctor_get(v_x_1795_, 0);
v_value_1798_ = lean_ctor_get(v_x_1795_, 1);
v_tail_1799_ = lean_ctor_get(v_x_1795_, 2);
v___x_1800_ = lean_name_eq(v_key_1797_, v_a_1794_);
if (v___x_1800_ == 0)
{
v_x_1795_ = v_tail_1799_;
goto _start;
}
else
{
lean_object* v___x_1802_; 
lean_inc(v_value_1798_);
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_value_1798_);
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1803_, v_x_1804_);
lean_dec(v_x_1804_);
lean_dec(v_a_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object* v_m_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_buckets_1808_; lean_object* v___x_1809_; uint64_t v___y_1811_; 
v_buckets_1808_ = lean_ctor_get(v_m_1806_, 1);
v___x_1809_ = lean_array_get_size(v_buckets_1808_);
if (lean_obj_tag(v_a_1807_) == 0)
{
uint64_t v___x_1825_; 
v___x_1825_ = 1723ULL;
v___y_1811_ = v___x_1825_;
goto v___jp_1810_;
}
else
{
uint64_t v_hash_1826_; 
v_hash_1826_ = lean_ctor_get_uint64(v_a_1807_, sizeof(void*)*2);
v___y_1811_ = v_hash_1826_;
goto v___jp_1810_;
}
v___jp_1810_:
{
uint64_t v___x_1812_; uint64_t v___x_1813_; uint64_t v_fold_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; uint64_t v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1812_ = 32ULL;
v___x_1813_ = lean_uint64_shift_right(v___y_1811_, v___x_1812_);
v_fold_1814_ = lean_uint64_xor(v___y_1811_, v___x_1813_);
v___x_1815_ = 16ULL;
v___x_1816_ = lean_uint64_shift_right(v_fold_1814_, v___x_1815_);
v___x_1817_ = lean_uint64_xor(v_fold_1814_, v___x_1816_);
v___x_1818_ = lean_uint64_to_usize(v___x_1817_);
v___x_1819_ = lean_usize_of_nat(v___x_1809_);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_sub(v___x_1819_, v___x_1820_);
v___x_1822_ = lean_usize_land(v___x_1818_, v___x_1821_);
v___x_1823_ = lean_array_uget_borrowed(v_buckets_1808_, v___x_1822_);
v___x_1824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1807_, v___x_1823_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object* v_m_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_m_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object* v___x_1830_, lean_object* v_declName_1831_, lean_object* v_as_1832_, size_t v_sz_1833_, size_t v_i_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_lt(v_i_1834_, v_sz_1833_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v_declName_1831_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1835_);
lean_ctor_set(v___x_1843_, 1, v___y_1836_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v_modules_1846_; lean_object* v___x_1847_; lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v_toImport_1850_; lean_object* v_module_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1845_ = l_Lean_Environment_header(v___x_1830_);
v_modules_1846_ = lean_ctor_get(v___x_1845_, 3);
lean_inc_ref(v_modules_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1848_ = lean_array_uget_borrowed(v_as_1832_, v_i_1834_);
v___x_1849_ = lean_array_get(v___x_1847_, v_modules_1846_, v_a_1848_);
lean_dec_ref(v_modules_1846_);
v_toImport_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_toImport_1850_);
lean_dec(v___x_1849_);
v_module_1851_ = lean_ctor_get(v_toImport_1850_, 0);
lean_inc(v_module_1851_);
lean_dec_ref(v_toImport_1850_);
v___x_1852_ = 0;
lean_inc(v_declName_1831_);
v___x_1853_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1851_, v___x_1852_, v_declName_1831_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v_snd_1855_ = lean_ctor_get(v_a_1854_, 1);
lean_inc(v_snd_1855_);
lean_dec(v_a_1854_);
v___x_1856_ = lean_box(0);
v___x_1857_ = ((size_t)1ULL);
v___x_1858_ = lean_usize_add(v_i_1834_, v___x_1857_);
v_i_1834_ = v___x_1858_;
v_b_1835_ = v___x_1856_;
v___y_1836_ = v_snd_1855_;
goto _start;
}
else
{
lean_dec(v_declName_1831_);
return v___x_1853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object* v___x_1860_, lean_object* v_declName_1861_, lean_object* v_as_1862_, lean_object* v_sz_1863_, lean_object* v_i_1864_, lean_object* v_b_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1863_);
lean_dec(v_sz_1863_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1864_);
lean_dec(v_i_1864_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_1860_, v_declName_1861_, v_as_1862_, v_sz_boxed_1872_, v_i_boxed_1873_, v_b_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_as_1862_);
lean_dec_ref(v___x_1860_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___x_1878_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0));
v___x_1879_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1878_, v___x_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_declName_1882_, uint8_t v_isMeta_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_env_1895_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___x_1920_; 
v___x_1890_ = lean_st_ref_get(v___y_1888_);
v_env_1895_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_env_1895_);
lean_dec(v___x_1890_);
v___x_1920_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1895_, v_declName_1882_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_dec_ref(v_env_1895_);
lean_dec(v_declName_1882_);
goto v___jp_1891_;
}
else
{
lean_object* v_val_1921_; lean_object* v___x_1922_; lean_object* v_modules_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_val_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_Environment_header(v_env_1895_);
v_modules_1923_ = lean_ctor_get(v___x_1922_, 3);
lean_inc_ref(v_modules_1923_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = lean_array_get_size(v_modules_1923_);
v___x_1925_ = lean_nat_dec_lt(v_val_1921_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_modules_1923_);
lean_dec(v_val_1921_);
lean_dec_ref(v_env_1895_);
lean_dec(v_declName_1882_);
goto v___jp_1891_;
}
else
{
lean_object* v___x_1926_; lean_object* v_env_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___y_1931_; 
v___x_1926_ = lean_st_ref_get(v___y_1888_);
v_env_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_ref(v_env_1927_);
lean_dec(v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2);
v___x_1929_ = lean_array_fget(v_modules_1923_, v_val_1921_);
lean_dec(v_val_1921_);
lean_dec_ref(v_modules_1923_);
if (v_isMeta_1883_ == 0)
{
lean_dec_ref(v_env_1927_);
v___y_1931_ = v_isMeta_1883_;
goto v___jp_1930_;
}
else
{
uint8_t v___x_1944_; 
lean_inc(v_declName_1882_);
v___x_1944_ = l_Lean_isMarkedMeta(v_env_1927_, v_declName_1882_);
if (v___x_1944_ == 0)
{
v___y_1931_ = v_isMeta_1883_;
goto v___jp_1930_;
}
else
{
uint8_t v___x_1945_; 
v___x_1945_ = 0;
v___y_1931_ = v___x_1945_;
goto v___jp_1930_;
}
}
v___jp_1930_:
{
lean_object* v_toImport_1932_; lean_object* v_module_1933_; lean_object* v___x_1934_; 
v_toImport_1932_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_ref(v_toImport_1932_);
lean_dec(v___x_1929_);
v_module_1933_ = lean_ctor_get(v_toImport_1932_, 0);
lean_inc(v_module_1933_);
lean_dec_ref(v_toImport_1932_);
lean_inc(v_declName_1882_);
v___x_1934_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1933_, v___y_1931_, v_declName_1882_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_snd_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v_snd_1936_ = lean_ctor_get(v_a_1935_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_a_1935_);
v___x_1937_ = l_Lean_indirectModUseExt;
v___x_1938_ = lean_box(1);
v___x_1939_ = lean_box(0);
lean_inc_ref(v_env_1895_);
v___x_1940_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1928_, v___x_1937_, v_env_1895_, v___x_1938_, v___x_1939_);
v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_1940_, v_declName_1882_);
lean_dec(v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3));
v___y_1897_ = v_snd_1936_;
v___y_1898_ = v___x_1942_;
goto v___jp_1896_;
}
else
{
lean_object* v_val_1943_; 
v_val_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v___x_1941_, 1);
v___y_1897_ = v_snd_1936_;
v___y_1898_ = v_val_1943_;
goto v___jp_1896_;
}
}
else
{
lean_dec_ref(v_env_1895_);
lean_dec(v_declName_1882_);
return v___x_1934_;
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___y_1884_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
v___jp_1896_:
{
lean_object* v___x_1899_; size_t v_sz_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = lean_box(0);
v_sz_1900_ = lean_array_size(v___y_1898_);
v___x_1901_ = ((size_t)0ULL);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_1895_, v_declName_1882_, v___y_1898_, v_sz_1900_, v___x_1901_, v___x_1899_, v___y_1897_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v_env_1895_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1919_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1919_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1919_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1917_; 
v_snd_1907_ = lean_ctor_get(v_a_1903_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_a_1903_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_a_1903_, 0);
lean_dec(v_unused_1918_);
v___x_1909_ = v_a_1903_;
v_isShared_1910_ = v_isSharedCheck_1917_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_dec(v_a_1903_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1917_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1899_);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_snd_1907_);
v___x_1912_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1914_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1912_);
v___x_1914_ = v___x_1905_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
else
{
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_declName_1946_, lean_object* v_isMeta_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v_isMeta_boxed_1954_; lean_object* v_res_1955_; 
v_isMeta_boxed_1954_ = lean_unbox(v_isMeta_1947_);
v_res_1955_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_1946_, v_isMeta_boxed_1954_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1956_, lean_object* v_vals_1957_, lean_object* v_i_1958_, lean_object* v_k_1959_){
_start:
{
lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1960_ = lean_array_get_size(v_keys_1956_);
v___x_1961_ = lean_nat_dec_lt(v_i_1958_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec(v_i_1958_);
v___x_1962_ = lean_box(0);
return v___x_1962_;
}
else
{
lean_object* v_k_x27_1963_; uint8_t v___x_1964_; 
v_k_x27_1963_ = lean_array_fget_borrowed(v_keys_1956_, v_i_1958_);
v___x_1964_ = lean_name_eq(v_k_1959_, v_k_x27_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_add(v_i_1958_, v___x_1965_);
lean_dec(v_i_1958_);
v_i_1958_ = v___x_1966_;
goto _start;
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_array_fget_borrowed(v_vals_1957_, v_i_1958_);
lean_dec(v_i_1958_);
lean_inc(v___x_1968_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1970_, lean_object* v_vals_1971_, lean_object* v_i_1972_, lean_object* v_k_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_1970_, v_vals_1971_, v_i_1972_, v_k_1973_);
lean_dec(v_k_1973_);
lean_dec_ref(v_vals_1971_);
lean_dec_ref(v_keys_1970_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_1975_, size_t v_x_1976_, lean_object* v_x_1977_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 0)
{
lean_object* v_es_1978_; lean_object* v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v_j_1982_; lean_object* v___x_1983_; 
v_es_1978_ = lean_ctor_get(v_x_1975_, 0);
v___x_1979_ = lean_box(2);
v___x_1980_ = ((size_t)31ULL);
v___x_1981_ = lean_usize_land(v_x_1976_, v___x_1980_);
v_j_1982_ = lean_usize_to_nat(v___x_1981_);
v___x_1983_ = lean_array_get_borrowed(v___x_1979_, v_es_1978_, v_j_1982_);
lean_dec(v_j_1982_);
switch(lean_obj_tag(v___x_1983_))
{
case 0:
{
lean_object* v_key_1984_; lean_object* v_val_1985_; uint8_t v___x_1986_; 
v_key_1984_ = lean_ctor_get(v___x_1983_, 0);
v_val_1985_ = lean_ctor_get(v___x_1983_, 1);
v___x_1986_ = lean_name_eq(v_x_1977_, v_key_1984_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
lean_inc(v_val_1985_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_val_1985_);
return v___x_1988_;
}
}
case 1:
{
lean_object* v_node_1989_; size_t v___x_1990_; size_t v___x_1991_; 
v_node_1989_ = lean_ctor_get(v___x_1983_, 0);
v___x_1990_ = ((size_t)5ULL);
v___x_1991_ = lean_usize_shift_right(v_x_1976_, v___x_1990_);
v_x_1975_ = v_node_1989_;
v_x_1976_ = v___x_1991_;
goto _start;
}
default: 
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_box(0);
return v___x_1993_;
}
}
}
else
{
lean_object* v_ks_1994_; lean_object* v_vs_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_ks_1994_ = lean_ctor_get(v_x_1975_, 0);
v_vs_1995_ = lean_ctor_get(v_x_1975_, 1);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_1994_, v_vs_1995_, v___x_1996_, v_x_1977_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
size_t v_x_30286__boxed_2001_; lean_object* v_res_2002_; 
v_x_30286__boxed_2001_ = lean_unbox_usize(v_x_1999_);
lean_dec(v_x_1999_);
v_res_2002_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_1998_, v_x_30286__boxed_2001_, v_x_2000_);
lean_dec(v_x_2000_);
lean_dec_ref(v_x_1998_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
uint64_t v___y_2006_; 
if (lean_obj_tag(v_x_2004_) == 0)
{
uint64_t v___x_2009_; 
v___x_2009_ = 1723ULL;
v___y_2006_ = v___x_2009_;
goto v___jp_2005_;
}
else
{
uint64_t v_hash_2010_; 
v_hash_2010_ = lean_ctor_get_uint64(v_x_2004_, sizeof(void*)*2);
v___y_2006_ = v_hash_2010_;
goto v___jp_2005_;
}
v___jp_2005_:
{
size_t v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_uint64_to_usize(v___y_2006_);
v___x_2008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2003_, v___x_2007_, v_x_2004_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_2011_, lean_object* v_x_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2011_, v_x_2012_);
lean_dec(v_x_2012_);
lean_dec_ref(v_x_2011_);
return v_res_2013_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___x_2015_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0));
v___x_2016_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2015_, v___x_2014_);
return v___x_2016_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2022_ = l_Lean_stringToMessageData(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2029_, lean_object* v_init_2030_, lean_object* v_x_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
if (lean_obj_tag(v_x_2031_) == 0)
{
lean_object* v_k_2038_; lean_object* v_l_2039_; lean_object* v_r_2040_; lean_object* v___x_2041_; 
v_k_2038_ = lean_ctor_get(v_x_2031_, 1);
lean_inc(v_k_2038_);
v_l_2039_ = lean_ctor_get(v_x_2031_, 3);
lean_inc(v_l_2039_);
v_r_2040_ = lean_ctor_get(v_x_2031_, 4);
lean_inc(v_r_2040_);
lean_dec_ref_known(v_x_2031_, 5);
lean_inc_ref(v_origDecl_2029_);
v___x_2041_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2029_, v_init_2030_, v_l_2039_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v_snd_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2166_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v_snd_2043_ = lean_ctor_get(v_a_2042_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2042_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v_a_2042_, 0);
lean_dec(v_unused_2167_);
v___x_2045_ = v_a_2042_;
v_isShared_2046_ = v_isSharedCheck_2166_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_snd_2043_);
lean_dec(v_a_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2166_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_NameSet_contains(v_snd_2043_, v_k_2038_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v_env_2050_; lean_object* v___x_2051_; lean_object* v_toEnvExtension_2052_; lean_object* v_asyncMode_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2049_ = lean_st_ref_get(v___y_2036_);
v_env_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_ref(v_env_2050_);
lean_dec(v___x_2049_);
v___x_2051_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2052_ = lean_ctor_get(v___x_2051_, 0);
v_asyncMode_2053_ = lean_ctor_get(v_toEnvExtension_2052_, 2);
lean_inc(v_k_2038_);
v___x_2054_ = l_Lean_NameSet_insert(v_snd_2043_, v_k_2038_);
v___x_2055_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2055_, v___x_2051_, v_env_2050_, v_asyncMode_2053_, v___x_2056_);
v___x_2058_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2057_, v_k_2038_);
lean_dec(v___x_2057_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_val_2059_; lean_object* v___x_2060_; 
lean_del_object(v___x_2045_);
lean_dec(v_k_2038_);
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc_n(v_val_2059_, 2);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2059_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; uint8_t v___y_2063_; lean_object* v_toSignature_2077_; lean_object* v_name_2078_; uint8_t v___x_2079_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v_toSignature_2077_ = lean_ctor_get(v_val_2059_, 0);
v_name_2078_ = lean_ctor_get(v_toSignature_2077_, 0);
v___x_2079_ = l_Lean_isPrivateName(v_name_2078_);
if (v___x_2079_ == 0)
{
lean_dec(v_a_2061_);
v___y_2063_ = v___x_2079_;
goto v___jp_2062_;
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_unbox(v_a_2061_);
lean_dec(v_a_2061_);
v___y_2063_ = v___x_2080_;
goto v___jp_2062_;
}
v___jp_2062_:
{
if (v___y_2063_ == 0)
{
lean_dec(v_val_2059_);
v_init_2030_ = v___x_2047_;
v_x_2031_ = v_r_2040_;
v___y_2032_ = v___x_2054_;
goto _start;
}
else
{
lean_object* v___x_2065_; 
lean_inc_ref(v_origDecl_2029_);
v___x_2065_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2029_, v_val_2059_, v___x_2054_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v_snd_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v_snd_2067_ = lean_ctor_get(v_a_2066_, 1);
lean_inc(v_snd_2067_);
lean_dec(v_a_2066_);
v_init_2030_ = v___x_2047_;
v_x_2031_ = v_r_2040_;
v___y_2032_ = v_snd_2067_;
goto _start;
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_r_2040_);
lean_dec_ref(v_origDecl_2029_);
v_a_2069_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2065_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2065_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_val_2059_);
lean_dec(v___x_2054_);
lean_dec(v_r_2040_);
lean_dec_ref(v_origDecl_2029_);
v_a_2081_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2060_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2060_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v_env_2090_; lean_object* v___x_2091_; 
lean_dec(v___x_2058_);
v___x_2089_ = lean_st_ref_get(v___y_2036_);
v_env_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc_ref(v_env_2090_);
lean_dec(v___x_2089_);
v___x_2091_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2090_, v_k_2038_);
lean_dec_ref(v_env_2090_);
if (lean_obj_tag(v___x_2091_) == 1)
{
lean_object* v_val_2092_; lean_object* v___x_2125_; lean_object* v_env_2134_; lean_object* v___x_2135_; lean_object* v_modules_2136_; uint8_t v___x_2137_; uint8_t v___y_2139_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_val_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_val_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2125_ = lean_st_ref_get(v___y_2036_);
v_env_2134_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_ref(v_env_2134_);
lean_dec(v___x_2125_);
v___x_2135_ = l_Lean_Environment_header(v_env_2134_);
lean_dec_ref(v_env_2134_);
v_modules_2136_ = lean_ctor_get(v___x_2135_, 3);
lean_inc_ref(v_modules_2136_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = 1;
v___x_2159_ = lean_array_get_size(v_modules_2136_);
v___x_2160_ = lean_nat_dec_lt(v_val_2092_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_dec_ref(v_modules_2136_);
v___y_2139_ = v___x_2048_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2161_; lean_object* v_toImport_2162_; uint8_t v_isExported_2163_; 
v___x_2161_ = lean_array_fget(v_modules_2136_, v_val_2092_);
lean_dec_ref(v_modules_2136_);
v_toImport_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_ref(v_toImport_2162_);
lean_dec(v___x_2161_);
v_isExported_2163_ = lean_ctor_get_uint8(v_toImport_2162_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2162_);
if (v_isExported_2163_ == 0)
{
goto v___jp_2126_;
}
else
{
v___y_2139_ = v___x_2048_;
goto v___jp_2138_;
}
}
v___jp_2093_:
{
lean_object* v___x_2094_; lean_object* v_toSignature_2095_; lean_object* v_env_2096_; lean_object* v_name_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2094_ = lean_st_ref_get(v___y_2036_);
v_toSignature_2095_ = lean_ctor_get(v_origDecl_2029_, 0);
lean_inc_ref(v_toSignature_2095_);
lean_dec_ref(v_origDecl_2029_);
v_env_2096_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_ref(v_env_2096_);
lean_dec(v___x_2094_);
v_name_2097_ = lean_ctor_get(v_toSignature_2095_, 0);
lean_inc(v_name_2097_);
lean_dec_ref(v_toSignature_2095_);
v___x_2098_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
v___x_2099_ = l_Lean_MessageData_ofConstName(v_name_2097_, v___x_2048_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 7);
lean_ctor_set(v___x_2045_, 1, v___x_2099_);
lean_ctor_set(v___x_2045_, 0, v___x_2098_);
v___x_2101_ = v___x_2045_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v___x_2102_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_MessageData_ofConstName(v_k_2038_, v___x_2048_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = l_Lean_Environment_header(v_env_2096_);
lean_dec_ref(v_env_2096_);
v___x_2109_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2108_);
v___x_2110_ = lean_array_get(v___x_2056_, v___x_2109_, v_val_2092_);
lean_dec(v_val_2092_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = l_Lean_MessageData_ofName(v___x_2110_);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2107_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2114_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
v___jp_2126_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v_fst_2130_; uint8_t v___x_2131_; 
v___x_2127_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2128_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v___x_2127_, v___x_2054_, v___y_2035_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v_fst_2130_ = lean_ctor_get(v_a_2129_, 0);
v___x_2131_ = lean_unbox(v_fst_2130_);
if (v___x_2131_ == 0)
{
lean_dec(v_a_2129_);
lean_dec(v_r_2040_);
goto v___jp_2093_;
}
else
{
if (v___x_2048_ == 0)
{
lean_object* v_snd_2132_; 
lean_dec(v_val_2092_);
lean_del_object(v___x_2045_);
lean_dec(v_k_2038_);
v_snd_2132_ = lean_ctor_get(v_a_2129_, 1);
lean_inc(v_snd_2132_);
lean_dec(v_a_2129_);
v_init_2030_ = v___x_2047_;
v_x_2031_ = v_r_2040_;
v___y_2032_ = v_snd_2132_;
goto _start;
}
else
{
lean_dec(v_a_2129_);
lean_dec(v_r_2040_);
goto v___jp_2093_;
}
}
}
v___jp_2138_:
{
if (v___y_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v_env_2141_; uint8_t v___x_2142_; uint8_t v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec(v_val_2092_);
lean_del_object(v___x_2045_);
v___x_2140_ = lean_st_ref_get(v___y_2036_);
v_env_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_ref(v_env_2141_);
lean_dec(v___x_2140_);
lean_inc(v_k_2038_);
v___x_2142_ = l_Lean_getIRPhases(v_env_2141_, v_k_2038_);
v___x_2143_ = 1;
v___x_2144_ = l_Lean_instBEqIRPhases_beq(v___x_2142_, v___x_2143_);
v___x_2145_ = lean_box(v___x_2144_);
v___x_2146_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed), 8, 2);
lean_closure_set(v___x_2146_, 0, v_k_2038_);
lean_closure_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2146_, v___x_2137_, v___x_2054_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v_snd_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v_snd_2149_ = lean_ctor_get(v_a_2148_, 1);
lean_inc(v_snd_2149_);
lean_dec(v_a_2148_);
v_init_2030_ = v___x_2047_;
v_x_2031_ = v_r_2040_;
v___y_2032_ = v_snd_2149_;
goto _start;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_r_2040_);
lean_dec_ref(v_origDecl_2029_);
v_a_2151_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2147_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2147_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
goto v___jp_2126_;
}
}
}
else
{
lean_dec(v___x_2091_);
lean_del_object(v___x_2045_);
lean_dec(v_k_2038_);
v_init_2030_ = v___x_2047_;
v_x_2031_ = v_r_2040_;
v___y_2032_ = v___x_2054_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2045_);
lean_dec(v_k_2038_);
v_init_2030_ = v___x_2047_;
v_x_2031_ = v_r_2040_;
v___y_2032_ = v_snd_2043_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2040_);
lean_dec(v_k_2038_);
lean_dec_ref(v_origDecl_2029_);
return v___x_2041_;
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec_ref(v_origDecl_2029_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_init_2030_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___y_2032_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2171_, lean_object* v_origDecl_2172_, lean_object* v_code_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = l_Lean_NameSet_empty;
v___x_2181_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2171_, v_code_2173_, v___x_2180_);
v___x_2182_ = lean_box(0);
v___x_2183_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2172_, v___x_2182_, v___x_2181_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2200_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2200_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2200_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_snd_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2198_; 
v_snd_2188_ = lean_ctor_get(v_a_2184_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2184_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v_a_2184_, 0);
lean_dec(v_unused_2199_);
v___x_2190_ = v_a_2184_;
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_snd_2188_);
lean_dec(v_a_2184_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2182_);
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_snd_2188_);
v___x_2193_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2195_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2193_);
v___x_2195_ = v___x_2186_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_a_2201_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2183_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2183_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2209_, lean_object* v_origDecl_2210_, lean_object* v_code_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v___x_30370__boxed_2218_; lean_object* v_res_2219_; 
v___x_30370__boxed_2218_ = lean_unbox(v___x_2209_);
v_res_2219_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_30370__boxed_2218_, v_origDecl_2210_, v_code_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2220_, lean_object* v_decl_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_value_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___f_2231_; lean_object* v___x_2232_; 
v_value_2228_ = lean_ctor_get(v_decl_2221_, 1);
lean_inc_ref(v_value_2228_);
lean_dec_ref(v_decl_2221_);
v___x_2229_ = 0;
v___x_2230_ = lean_box(v___x_2229_);
v___f_2231_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2231_, 0, v___x_2230_);
lean_closure_set(v___f_2231_, 1, v_origDecl_2220_);
v___x_2232_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2231_, v_value_2228_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2233_, lean_object* v_decl_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2233_, v_decl_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2242_, lean_object* v_init_2243_, lean_object* v_x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2242_, v_init_2243_, v_x_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2253_, v_x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2256_, v_x_2257_, v_x_2258_);
lean_dec(v_x_2258_);
lean_dec_ref(v_x_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_opt_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_2260_, v___y_2261_, v___y_2264_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_opt_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_opt_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2276_, lean_object* v_x_2277_, size_t v_x_2278_, lean_object* v_x_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2277_, v_x_2278_, v_x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
size_t v_x_30787__boxed_2285_; lean_object* v_res_2286_; 
v_x_30787__boxed_2285_ = lean_unbox_usize(v_x_2283_);
lean_dec(v_x_2283_);
v_res_2286_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2281_, v_x_2282_, v_x_30787__boxed_2285_, v_x_2284_);
lean_dec(v_x_2284_);
lean_dec_ref(v_x_2282_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(lean_object* v_00_u03b2_2287_, lean_object* v_m_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_2288_, v_a_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2291_, lean_object* v_m_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_2291_, v_m_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_m_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2295_, lean_object* v_keys_2296_, lean_object* v_vals_2297_, lean_object* v_heq_2298_, lean_object* v_i_2299_, lean_object* v_k_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2296_, v_vals_2297_, v_i_2299_, v_k_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2302_, lean_object* v_keys_2303_, lean_object* v_vals_2304_, lean_object* v_heq_2305_, lean_object* v_i_2306_, lean_object* v_k_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2302_, v_keys_2303_, v_vals_2304_, v_heq_2305_, v_i_2306_, v_k_2307_);
lean_dec(v_k_2307_);
lean_dec_ref(v_vals_2304_);
lean_dec_ref(v_keys_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
uint8_t v___x_2312_; 
v___x_2312_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_2310_, v_x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_res_2316_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_2313_, v_x_2314_, v_x_2315_);
lean_dec_ref(v_x_2315_);
lean_dec_ref(v_x_2314_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_2318_, lean_object* v_a_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_2319_, v_x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2322_, lean_object* v_a_2323_, lean_object* v_x_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_2322_, v_a_2323_, v_x_2324_);
lean_dec(v_x_2324_);
lean_dec(v_a_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, size_t v_x_2328_, lean_object* v_x_2329_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_2327_, v_x_2328_, v_x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
size_t v_x_30815__boxed_2335_; uint8_t v_res_2336_; lean_object* v_r_2337_; 
v_x_30815__boxed_2335_ = lean_unbox_usize(v_x_2333_);
lean_dec(v_x_2333_);
v_res_2336_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_2331_, v_x_2332_, v_x_30815__boxed_2335_, v_x_2334_);
lean_dec_ref(v_x_2334_);
lean_dec_ref(v_x_2332_);
v_r_2337_ = lean_box(v_res_2336_);
return v_r_2337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_2338_, lean_object* v_keys_2339_, lean_object* v_vals_2340_, lean_object* v_heq_2341_, lean_object* v_i_2342_, lean_object* v_k_2343_){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_2339_, v_i_2342_, v_k_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2345_, lean_object* v_keys_2346_, lean_object* v_vals_2347_, lean_object* v_heq_2348_, lean_object* v_i_2349_, lean_object* v_k_2350_){
_start:
{
uint8_t v_res_2351_; lean_object* v_r_2352_; 
v_res_2351_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_2345_, v_keys_2346_, v_vals_2347_, v_heq_2348_, v_i_2349_, v_k_2350_);
lean_dec_ref(v_k_2350_);
lean_dec_ref(v_vals_2347_);
lean_dec_ref(v_keys_2346_);
v_r_2352_ = lean_box(v_res_2351_);
return v_r_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2353_, size_t v_sz_2354_, size_t v_i_2355_, lean_object* v_b_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_a_2363_; uint8_t v___x_2367_; 
v___x_2367_ = lean_usize_dec_lt(v_i_2355_, v_sz_2354_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_b_2356_);
return v___x_2368_;
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2370_; 
v_a_2369_ = lean_array_uget_borrowed(v_as_2353_, v_i_2355_);
lean_inc(v_a_2369_);
v___x_2370_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2369_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_toSignature_2371_; lean_object* v_a_2372_; lean_object* v_name_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_toSignature_2371_ = lean_ctor_get(v_a_2369_, 0);
v_a_2372_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2370_, 1);
v_name_2373_ = lean_ctor_get(v_toSignature_2371_, 0);
v___x_2374_ = lean_box(0);
v___x_2375_ = l_Lean_isPrivateName(v_name_2373_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
if (v___x_2376_ == 0)
{
v_a_2363_ = v___x_2374_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_st_ref_get(v___y_2360_);
lean_dec(v___x_2377_);
v___x_2378_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2369_, 2);
v___x_2379_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2369_, v_a_2369_, v___x_2378_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_dec_ref_known(v___x_2379_, 1);
v_a_2363_ = v___x_2374_;
goto v___jp_2362_;
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
else
{
lean_dec(v_a_2372_);
v_a_2363_ = v___x_2374_;
goto v___jp_2362_;
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
v_a_2388_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2370_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2370_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
v___jp_2362_:
{
size_t v___x_2364_; size_t v___x_2365_; 
v___x_2364_ = ((size_t)1ULL);
v___x_2365_ = lean_usize_add(v_i_2355_, v___x_2364_);
v_i_2355_ = v___x_2365_;
v_b_2356_ = v_a_2363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2396_, lean_object* v_sz_2397_, lean_object* v_i_2398_, lean_object* v_b_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2397_);
lean_dec(v_sz_2397_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2396_, v_sz_boxed_2405_, v_i_boxed_2406_, v_b_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_as_2396_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v_env_2415_; lean_object* v___x_2416_; uint8_t v_isModule_2417_; 
v___x_2414_ = lean_st_ref_get(v___y_2412_);
v_env_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_env_2415_);
lean_dec(v___x_2414_);
v___x_2416_ = l_Lean_Environment_header(v_env_2415_);
lean_dec_ref(v_env_2415_);
v_isModule_2417_ = lean_ctor_get_uint8(v___x_2416_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2416_);
if (v_isModule_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_decls_2408_);
return v___x_2418_;
}
else
{
lean_object* v___x_2419_; size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2419_ = lean_box(0);
v_sz_2420_ = lean_array_size(v_decls_2408_);
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2408_, v_sz_2420_, v___x_2421_, v___x_2419_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v___x_2422_, 0);
lean_dec(v_unused_2430_);
v___x_2424_ = v___x_2422_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v___x_2422_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_decls_2408_);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_decls_2408_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec_ref(v_decls_2408_);
v_a_2431_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2422_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2422_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2445_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2459_ = l_Lean_stringToMessageData(v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2460_, uint8_t v___x_2461_, lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_a_2472_; uint8_t v___x_2476_; 
v___x_2476_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_b_2465_);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; lean_object* v_env_2479_; lean_object* v_a_2480_; lean_object* v_toSignature_2481_; lean_object* v_name_2482_; lean_object* v___x_2483_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2478_ = lean_st_ref_get(v___y_2469_);
v_env_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc_ref(v_env_2479_);
lean_dec(v___x_2478_);
v_a_2480_ = lean_array_uget_borrowed(v_as_2462_, v_i_2464_);
v_toSignature_2481_ = lean_ctor_get(v_a_2480_, 0);
v_name_2482_ = lean_ctor_get(v_toSignature_2481_, 0);
v___x_2483_ = lean_box(0);
v___x_2491_ = l_Lean_Environment_setExporting(v_env_2479_, v___x_2461_);
lean_inc(v_name_2482_);
v___x_2492_ = l_Lean_Environment_contains(v___x_2491_, v_name_2482_, v___x_2461_);
if (v___x_2492_ == 0)
{
v_a_2472_ = v___x_2483_;
goto v___jp_2471_;
}
else
{
lean_object* v_options_2493_; uint8_t v_hasTrace_2494_; 
v_options_2493_ = lean_ctor_get(v___y_2468_, 2);
v_hasTrace_2494_ = lean_ctor_get_uint8(v_options_2493_, sizeof(void*)*1);
if (v_hasTrace_2494_ == 0)
{
v___y_2485_ = v___y_2466_;
v___y_2486_ = v___y_2467_;
v___y_2487_ = v___y_2468_;
v___y_2488_ = v___y_2469_;
goto v___jp_2484_;
}
else
{
lean_object* v_inheritedTraceOptions_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v_inheritedTraceOptions_2495_ = lean_ctor_get(v___y_2468_, 13);
v___x_2496_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2497_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2495_, v_options_2493_, v___x_2497_);
if (v___x_2498_ == 0)
{
v___y_2485_ = v___y_2466_;
v___y_2486_ = v___y_2467_;
v___y_2487_ = v___y_2468_;
v___y_2488_ = v___y_2469_;
goto v___jp_2484_;
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2499_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2482_);
v___x_2500_ = l_Lean_MessageData_ofName(v_name_2482_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2496_, v___x_2503_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_dec_ref_known(v___x_2504_, 1);
v___y_2485_ = v___y_2466_;
v___y_2486_ = v___y_2467_;
v___y_2487_ = v___y_2468_;
v___y_2488_ = v___y_2469_;
goto v___jp_2484_;
}
else
{
return v___x_2504_;
}
}
}
}
v___jp_2484_:
{
uint8_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2460_);
lean_inc(v_a_2480_);
v___x_2490_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2489_, v_phase_2460_, v_a_2480_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_dec_ref_known(v___x_2490_, 1);
v_a_2472_ = v___x_2483_;
goto v___jp_2471_;
}
else
{
return v___x_2490_;
}
}
}
v___jp_2471_:
{
size_t v___x_2473_; size_t v___x_2474_; 
v___x_2473_ = ((size_t)1ULL);
v___x_2474_ = lean_usize_add(v_i_2464_, v___x_2473_);
v_i_2464_ = v___x_2474_;
v_b_2465_ = v_a_2472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2505_, lean_object* v___x_2506_, lean_object* v_as_2507_, lean_object* v_sz_2508_, lean_object* v_i_2509_, lean_object* v_b_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v_phase_boxed_2516_; uint8_t v___x_2836__boxed_2517_; size_t v_sz_boxed_2518_; size_t v_i_boxed_2519_; lean_object* v_res_2520_; 
v_phase_boxed_2516_ = lean_unbox(v_phase_2505_);
v___x_2836__boxed_2517_ = lean_unbox(v___x_2506_);
v_sz_boxed_2518_ = lean_unbox_usize(v_sz_2508_);
lean_dec(v_sz_2508_);
v_i_boxed_2519_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2516_, v___x_2836__boxed_2517_, v_as_2507_, v_sz_boxed_2518_, v_i_boxed_2519_, v_b_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v_as_2507_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2521_, lean_object* v_decls_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v_env_2529_; lean_object* v___x_2530_; uint8_t v_isModule_2531_; 
v___x_2528_ = lean_st_ref_get(v___y_2526_);
v_env_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc_ref(v_env_2529_);
lean_dec(v___x_2528_);
v___x_2530_ = l_Lean_Environment_header(v_env_2529_);
lean_dec_ref(v_env_2529_);
v_isModule_2531_ = lean_ctor_get_uint8(v___x_2530_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2530_);
if (v_isModule_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_decls_2522_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; size_t v_sz_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_box(0);
v_sz_2534_ = lean_array_size(v_decls_2522_);
v___x_2535_ = ((size_t)0ULL);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2521_, v_isModule_2531_, v_decls_2522_, v_sz_2534_, v___x_2535_, v___x_2533_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2536_, 0);
lean_dec(v_unused_2544_);
v___x_2538_ = v___x_2536_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_dec(v___x_2536_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v_decls_2522_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_decls_2522_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_decls_2522_);
v_a_2545_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2536_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2536_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2553_, lean_object* v_decls_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v_phase_boxed_2560_; lean_object* v_res_2561_; 
v_phase_boxed_2560_ = lean_unbox(v_phase_2553_);
v_res_2561_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2560_, v_decls_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2565_ = lean_box(v_phase_2564_);
v___f_2566_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2566_, 0, v___x_2565_);
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = 0;
v___x_2569_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2570_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2570_, 0, v___x_2567_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
lean_ctor_set(v___x_2570_, 2, v___f_2566_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*3, v_phase_2564_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*3 + 1, v_phase_2564_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*3 + 2, v___x_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2571_){
_start:
{
uint8_t v_phase_boxed_2572_; lean_object* v_res_2573_; 
v_phase_boxed_2572_ = lean_unbox(v_phase_2571_);
v_res_2573_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2572_);
return v_res_2573_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_unsigned_to_nat(3356661454u);
v___x_2626_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2627_ = l_Lean_Name_num___override(v___x_2626_, v___x_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2630_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2631_ = l_Lean_Name_str___override(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2635_ = l_Lean_Name_str___override(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_unsigned_to_nat(2u);
v___x_2637_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2638_ = l_Lean_Name_num___override(v___x_2637_, v___x_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2641_ = 0;
v___x_2642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2643_ = l_Lean_registerTraceClass(v___x_2640_, v___x_2641_, v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2645_;
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
