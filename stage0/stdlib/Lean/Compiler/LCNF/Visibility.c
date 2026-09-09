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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_174_; 
v_val_154_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
v___x_156_ = v___x_151_;
v_isShared_157_ = v_isSharedCheck_174_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_dec(v___x_151_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_174_;
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
lean_object* v_toCold_165_; lean_object* v_options_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v_toCold_165_ = lean_ctor_get(v___y_143_, 0);
v_options_166_ = lean_ctor_get(v_toCold_165_, 2);
v___x_167_ = l_Lean_Compiler_LCNF_compiler_small;
v___x_168_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_options_166_, v___x_167_);
v___x_169_ = l_Lean_Compiler_LCNF_Code_sizeLe(v_pu_139_, v_code_140_, v___x_168_);
lean_dec(v___x_168_);
v___x_170_ = lean_box(v___x_169_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 0);
lean_ctor_set(v___x_156_, 0, v___x_170_);
v___x_172_ = v___x_156_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed(lean_object* v_toSignature_175_, lean_object* v_a_176_, lean_object* v_pu_177_, lean_object* v_code_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_a_953__boxed_184_; uint8_t v_pu_boxed_185_; lean_object* v_res_186_; 
v_a_953__boxed_184_ = lean_unbox(v_a_176_);
v_pu_boxed_185_ = lean_unbox(v_pu_177_);
v_res_186_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_175_, v_a_953__boxed_184_, v_pu_boxed_185_, v_code_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec_ref(v_code_178_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(uint8_t v_pu_187_, lean_object* v_decl_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
lean_inc_ref(v_decl_188_);
v___x_194_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_188_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; uint8_t v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
v___x_196_ = lean_unbox(v_a_195_);
if (v___x_196_ == 0)
{
lean_object* v_toSignature_197_; lean_object* v_value_198_; lean_object* v___x_199_; lean_object* v___f_200_; lean_object* v___x_201_; 
lean_dec_ref_known(v___x_194_, 1);
v_toSignature_197_ = lean_ctor_get(v_decl_188_, 0);
lean_inc_ref(v_toSignature_197_);
v_value_198_ = lean_ctor_get(v_decl_188_, 1);
lean_inc_ref(v_value_198_);
lean_dec_ref(v_decl_188_);
v___x_199_ = lean_box(v_pu_187_);
v___f_200_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed), 9, 3);
lean_closure_set(v___f_200_, 0, v_toSignature_197_);
lean_closure_set(v___f_200_, 1, v_a_195_);
lean_closure_set(v___f_200_, 2, v___x_199_);
v___x_201_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_value_198_, v___f_200_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_201_;
}
else
{
lean_dec(v_a_195_);
lean_dec_ref(v_decl_188_);
return v___x_194_;
}
}
else
{
lean_dec_ref(v_decl_188_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(lean_object* v_pu_202_, lean_object* v_decl_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
uint8_t v_pu_boxed_209_; lean_object* v_res_210_; 
v_pu_boxed_209_ = lean_unbox(v_pu_202_);
v_res_210_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_boxed_209_, v_decl_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_211_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_alloc_ctor(0, 11, 0);
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
lean_object* v_toCold_229_; lean_object* v_ref_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_toCold_229_ = lean_ctor_get(v___y_226_, 0);
v_ref_230_ = lean_ctor_get(v___y_226_, 2);
v___x_231_ = lean_st_ref_get(v___y_227_);
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
lean_object* v_env_238_; lean_object* v_lctx_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_291_; 
v_env_238_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_238_);
lean_dec(v___x_231_);
v_lctx_239_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_232_, 1);
lean_dec(v_unused_292_);
v___x_241_ = v___x_232_;
v_isShared_242_ = v_isSharedCheck_291_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_lctx_239_);
lean_dec(v___x_232_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_291_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_options_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_traceState_246_; lean_object* v_env_247_; lean_object* v_nextMacroScope_248_; lean_object* v_ngen_249_; lean_object* v_auxDeclNGen_250_; lean_object* v_cache_251_; lean_object* v_messages_252_; lean_object* v_infoState_253_; lean_object* v_snapshotTasks_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_290_; 
v_options_243_ = lean_ctor_get(v_toCold_229_, 2);
v___x_244_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_245_ = lean_st_ref_take(v___y_227_);
v_traceState_246_ = lean_ctor_get(v___x_245_, 4);
v_env_247_ = lean_ctor_get(v___x_245_, 0);
v_nextMacroScope_248_ = lean_ctor_get(v___x_245_, 1);
v_ngen_249_ = lean_ctor_get(v___x_245_, 2);
v_auxDeclNGen_250_ = lean_ctor_get(v___x_245_, 3);
v_cache_251_ = lean_ctor_get(v___x_245_, 5);
v_messages_252_ = lean_ctor_get(v___x_245_, 6);
v_infoState_253_ = lean_ctor_get(v___x_245_, 7);
v_snapshotTasks_254_ = lean_ctor_get(v___x_245_, 8);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_290_ == 0)
{
v___x_256_ = v___x_245_;
v_isShared_257_ = v_isSharedCheck_290_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_snapshotTasks_254_);
lean_inc(v_infoState_253_);
lean_inc(v_messages_252_);
lean_inc(v_cache_251_);
lean_inc(v_traceState_246_);
lean_inc(v_auxDeclNGen_250_);
lean_inc(v_ngen_249_);
lean_inc(v_nextMacroScope_248_);
lean_inc(v_env_247_);
lean_dec(v___x_245_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_290_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
uint64_t v_tid_258_; lean_object* v_traces_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_289_; 
v_tid_258_ = lean_ctor_get_uint64(v_traceState_246_, sizeof(void*)*1);
v_traces_259_ = lean_ctor_get(v_traceState_246_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v_traceState_246_);
if (v_isSharedCheck_289_ == 0)
{
v___x_261_ = v_traceState_246_;
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_traces_259_);
lean_dec(v_traceState_246_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_263_ = lean_unbox(v_a_234_);
lean_dec(v_a_234_);
v___x_264_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_239_, v___x_263_);
lean_dec_ref(v_lctx_239_);
lean_inc_ref(v_options_243_);
v___x_265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_265_, 0, v_env_238_);
lean_ctor_set(v___x_265_, 1, v___x_244_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
lean_ctor_set(v___x_265_, 3, v_options_243_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 1, v_msg_223_);
lean_ctor_set(v___x_241_, 0, v___x_265_);
v___x_267_ = v___x_241_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_msg_223_);
v___x_267_ = v_reuseFailAlloc_288_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; double v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_270_ = 0;
v___x_271_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_272_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_272_, 0, v_cls_222_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
lean_ctor_set_float(v___x_272_, sizeof(void*)*3, v___x_269_);
lean_ctor_set_float(v___x_272_, sizeof(void*)*3 + 8, v___x_269_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*3 + 16, v___x_270_);
v___x_273_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_274_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_267_);
lean_ctor_set(v___x_274_, 2, v___x_273_);
lean_inc(v_ref_230_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_ref_230_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = l_Lean_PersistentArray_push___redArg(v_traces_259_, v___x_275_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_276_);
v___x_278_ = v___x_261_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_276_);
lean_ctor_set_uint64(v_reuseFailAlloc_287_, sizeof(void*)*1, v_tid_258_);
v___x_278_ = v_reuseFailAlloc_287_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v___x_278_);
v___x_280_ = v___x_256_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_env_247_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_nextMacroScope_248_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_ngen_249_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_auxDeclNGen_250_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_286_, 5, v_cache_251_);
lean_ctor_set(v_reuseFailAlloc_286_, 6, v_messages_252_);
lean_ctor_set(v_reuseFailAlloc_286_, 7, v_infoState_253_);
lean_ctor_set(v_reuseFailAlloc_286_, 8, v_snapshotTasks_254_);
v___x_280_ = v_reuseFailAlloc_286_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = lean_st_ref_put(v___y_227_, v___x_280_);
v___x_282_ = lean_box(0);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_282_);
v___x_284_ = v___x_236_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
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
lean_dec(v___x_231_);
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
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(lean_object* v_pu_360_, lean_object* v_phase_361_, lean_object* v_decl_362_, lean_object* v_code_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v_pu_boxed_369_; uint8_t v_phase_boxed_370_; lean_object* v_res_371_; 
v_pu_boxed_369_ = lean_unbox(v_pu_360_);
v_phase_boxed_370_ = lean_unbox(v_phase_361_);
v_res_371_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(v_pu_boxed_369_, v_phase_boxed_370_, v_decl_362_, v_code_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_371_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_381_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_382_ = l_Lean_Name_append(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec(uint8_t v_pu_389_, uint8_t v_phase_390_, lean_object* v_decl_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_toSignature_398_; lean_object* v_env_399_; lean_object* v_nextMacroScope_400_; lean_object* v_ngen_401_; lean_object* v_auxDeclNGen_402_; lean_object* v_traceState_403_; lean_object* v_messages_404_; lean_object* v_infoState_405_; lean_object* v_snapshotTasks_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_482_; 
v___x_397_ = lean_st_ref_take(v_a_395_);
v_toSignature_398_ = lean_ctor_get(v_decl_391_, 0);
v_env_399_ = lean_ctor_get(v___x_397_, 0);
v_nextMacroScope_400_ = lean_ctor_get(v___x_397_, 1);
v_ngen_401_ = lean_ctor_get(v___x_397_, 2);
v_auxDeclNGen_402_ = lean_ctor_get(v___x_397_, 3);
v_traceState_403_ = lean_ctor_get(v___x_397_, 4);
v_messages_404_ = lean_ctor_get(v___x_397_, 6);
v_infoState_405_ = lean_ctor_get(v___x_397_, 7);
v_snapshotTasks_406_ = lean_ctor_get(v___x_397_, 8);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_397_, 5);
lean_dec(v_unused_483_);
v___x_408_ = v___x_397_;
v_isShared_409_ = v_isSharedCheck_482_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snapshotTasks_406_);
lean_inc(v_infoState_405_);
lean_inc(v_messages_404_);
lean_inc(v_traceState_403_);
lean_inc(v_auxDeclNGen_402_);
lean_inc(v_ngen_401_);
lean_inc(v_nextMacroScope_400_);
lean_inc(v_env_399_);
lean_dec(v___x_397_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_482_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_value_410_; lean_object* v_name_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_value_410_ = lean_ctor_get(v_decl_391_, 1);
lean_inc_ref(v_value_410_);
v_name_411_ = lean_ctor_get(v_toSignature_398_, 0);
lean_inc_n(v_name_411_, 2);
v___x_412_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_399_, v_name_411_);
v___x_413_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 5, v___x_413_);
lean_ctor_set(v___x_408_, 0, v___x_412_);
v___x_415_ = v___x_408_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_400_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_401_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_402_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_traceState_403_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_messages_404_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_infoState_405_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_snapshotTasks_406_);
v___x_415_ = v_reuseFailAlloc_481_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_st_ref_put(v_a_395_, v___x_415_);
lean_inc_ref(v_decl_391_);
v___x_417_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_389_, v_decl_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_472_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_472_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_472_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_472_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint8_t v___x_422_; 
v___x_422_ = lean_unbox(v_a_418_);
lean_dec(v_a_418_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v_name_411_);
lean_dec_ref(v_value_410_);
lean_dec_ref(v_decl_391_);
v___x_423_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v___x_427_; lean_object* v_env_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; uint8_t v___x_457_; 
lean_del_object(v___x_420_);
v___x_427_ = lean_st_ref_get(v_a_395_);
v_env_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_env_428_);
lean_dec(v___x_427_);
v___x_429_ = lean_box(v_pu_389_);
v___x_430_ = lean_box(v_phase_390_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed), 9, 3);
lean_closure_set(v___f_431_, 0, v___x_429_);
lean_closure_set(v___f_431_, 1, v___x_430_);
lean_closure_set(v___f_431_, 2, v_decl_391_);
v___x_457_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_428_, v_phase_390_, v_name_411_);
if (v___x_457_ == 0)
{
lean_object* v_toCold_458_; lean_object* v_options_459_; uint8_t v_hasTrace_460_; 
v_toCold_458_ = lean_ctor_get(v_a_394_, 0);
v_options_459_ = lean_ctor_get(v_toCold_458_, 2);
v_hasTrace_460_ = lean_ctor_get_uint8(v_options_459_, sizeof(void*)*1);
if (v_hasTrace_460_ == 0)
{
v___y_433_ = v_a_392_;
v___y_434_ = v_a_393_;
v___y_435_ = v_a_394_;
v___y_436_ = v_a_395_;
goto v___jp_432_;
}
else
{
lean_object* v_inheritedTraceOptions_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_inheritedTraceOptions_461_ = lean_ctor_get(v_toCold_458_, 11);
v___x_462_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_463_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_461_, v_options_459_, v___x_463_);
if (v___x_464_ == 0)
{
v___y_433_ = v_a_392_;
v___y_434_ = v_a_393_;
v___y_435_ = v_a_394_;
v___y_436_ = v_a_395_;
goto v___jp_432_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_411_);
v___x_466_ = l_Lean_MessageData_ofName(v_name_411_);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_462_, v___x_469_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_dec_ref_known(v___x_470_, 1);
v___y_433_ = v_a_392_;
v___y_434_ = v_a_393_;
v___y_435_ = v_a_394_;
v___y_436_ = v_a_395_;
goto v___jp_432_;
}
else
{
lean_dec_ref(v___f_431_);
lean_dec(v_name_411_);
lean_dec_ref(v_value_410_);
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_name_411_);
v___x_471_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_431_, v_value_410_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_471_;
}
v___jp_432_:
{
lean_object* v___x_437_; lean_object* v_env_438_; lean_object* v_nextMacroScope_439_; lean_object* v_ngen_440_; lean_object* v_auxDeclNGen_441_; lean_object* v_traceState_442_; lean_object* v_messages_443_; lean_object* v_infoState_444_; lean_object* v_snapshotTasks_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
v___x_437_ = lean_st_ref_take(v___y_436_);
v_env_438_ = lean_ctor_get(v___x_437_, 0);
v_nextMacroScope_439_ = lean_ctor_get(v___x_437_, 1);
v_ngen_440_ = lean_ctor_get(v___x_437_, 2);
v_auxDeclNGen_441_ = lean_ctor_get(v___x_437_, 3);
v_traceState_442_ = lean_ctor_get(v___x_437_, 4);
v_messages_443_ = lean_ctor_get(v___x_437_, 6);
v_infoState_444_ = lean_ctor_get(v___x_437_, 7);
v_snapshotTasks_445_ = lean_ctor_get(v___x_437_, 8);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v___x_437_, 5);
lean_dec(v_unused_456_);
v___x_447_ = v___x_437_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snapshotTasks_445_);
lean_inc(v_infoState_444_);
lean_inc(v_messages_443_);
lean_inc(v_traceState_442_);
lean_inc(v_auxDeclNGen_441_);
lean_inc(v_ngen_440_);
lean_inc(v_nextMacroScope_439_);
lean_inc(v_env_438_);
lean_dec(v___x_437_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_438_, v_phase_390_, v_name_411_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 5, v___x_413_);
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_nextMacroScope_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_ngen_440_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_auxDeclNGen_441_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_traceState_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_messages_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_infoState_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_snapshotTasks_445_);
v___x_451_ = v_reuseFailAlloc_454_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_st_ref_put(v___y_436_, v___x_451_);
v___x_453_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_431_, v_value_410_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
return v___x_453_;
}
}
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_name_411_);
lean_dec_ref(v_value_410_);
lean_dec_ref(v_decl_391_);
v_a_473_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_417_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_417_);
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
lean_object* v_k_496_; lean_object* v_l_497_; lean_object* v_r_498_; lean_object* v___x_499_; 
v_k_496_ = lean_ctor_get(v_x_490_, 1);
lean_inc(v_k_496_);
v_l_497_ = lean_ctor_get(v_x_490_, 3);
lean_inc(v_l_497_);
v_r_498_ = lean_ctor_get(v_x_490_, 4);
lean_inc(v_r_498_);
lean_dec_ref_known(v_x_490_, 5);
lean_inc_ref(v_decl_488_);
v___x_499_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_487_, v_decl_488_, v_init_489_, v_l_497_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; 
lean_dec_ref_known(v___x_499_, 1);
v___x_500_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_496_, v_phase_487_, v___y_494_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = lean_box(0);
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_val_503_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___x_520_; lean_object* v_env_521_; uint8_t v___x_522_; 
v_val_503_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_501_, 1);
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
v_init_489_ = v___x_502_;
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
v_init_489_ = v___x_502_;
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
lean_dec(v_a_501_);
lean_dec(v_k_496_);
v_init_489_ = v___x_502_;
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
v_a_550_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_500_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_500_);
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
return v___x_499_;
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
lean_object* v_toCold_617_; lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_toCold_617_ = lean_ctor_get(v___y_614_, 0);
v_ref_618_ = lean_ctor_get(v___y_614_, 2);
v___x_619_ = lean_st_ref_get(v___y_615_);
v___x_620_ = lean_st_ref_get(v___y_613_);
v___x_621_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_612_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_645_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_645_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_645_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_645_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_env_626_; lean_object* v_lctx_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_643_; 
v_env_626_ = lean_ctor_get(v___x_619_, 0);
lean_inc_ref(v_env_626_);
lean_dec(v___x_619_);
v_lctx_627_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_620_, 1);
lean_dec(v_unused_644_);
v___x_629_ = v___x_620_;
v_isShared_630_ = v_isSharedCheck_643_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_lctx_627_);
lean_dec(v___x_620_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_643_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_options_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v_options_631_ = lean_ctor_get(v_toCold_617_, 2);
v___x_632_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
v___x_633_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_627_, v___x_632_);
lean_dec_ref(v_lctx_627_);
v___x_634_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
lean_inc_ref(v_options_631_);
v___x_635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_635_, 0, v_env_626_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
lean_ctor_set(v___x_635_, 2, v___x_633_);
lean_ctor_set(v___x_635_, 3, v_options_631_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 3);
lean_ctor_set(v___x_629_, 1, v_msg_611_);
lean_ctor_set(v___x_629_, 0, v___x_635_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_msg_611_);
v___x_637_ = v_reuseFailAlloc_642_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
lean_inc(v_ref_618_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_ref_618_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 1);
lean_ctor_set(v___x_624_, 0, v___x_638_);
v___x_640_ = v___x_624_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v___x_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_msg_611_);
v_a_646_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_621_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_621_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_661_, lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_662_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_670_, lean_object* v_msg_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_670_, v_msg_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
return v_res_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_679_, lean_object* v_opt_680_){
_start:
{
lean_object* v_name_681_; lean_object* v_defValue_682_; lean_object* v_map_683_; lean_object* v___x_684_; 
v_name_681_ = lean_ctor_get(v_opt_680_, 0);
v_defValue_682_ = lean_ctor_get(v_opt_680_, 1);
v_map_683_ = lean_ctor_get(v_opts_679_, 0);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_683_, v_name_681_);
if (lean_obj_tag(v___x_684_) == 0)
{
uint8_t v___x_685_; 
v___x_685_ = lean_unbox(v_defValue_682_);
return v___x_685_;
}
else
{
lean_object* v_val_686_; 
v_val_686_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v___x_684_, 1);
if (lean_obj_tag(v_val_686_) == 1)
{
uint8_t v_v_687_; 
v_v_687_ = lean_ctor_get_uint8(v_val_686_, 0);
lean_dec_ref_known(v_val_686_, 0);
return v_v_687_;
}
else
{
uint8_t v___x_688_; 
lean_dec(v_val_686_);
v___x_688_ = lean_unbox(v_defValue_682_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_689_, lean_object* v_opt_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_689_, v_opt_690_);
lean_dec_ref(v_opt_690_);
lean_dec_ref(v_opts_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_693_, lean_object* v_v_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
if (lean_obj_tag(v_v_694_) == 0)
{
lean_object* v_code_701_; lean_object* v___x_702_; 
v_code_701_ = lean_ctor_get(v_v_694_, 0);
lean_inc_ref(v_code_701_);
lean_dec_ref_known(v_v_694_, 1);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
v___x_702_ = lean_apply_7(v_f_693_, v_code_701_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_702_;
}
else
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v_f_693_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_v_694_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v_v_694_, 0);
lean_dec(v_unused_712_);
v___x_704_ = v_v_694_;
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_v_694_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___y_695_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 0);
lean_ctor_set(v___x_704_, 0, v___x_707_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_713_, lean_object* v_v_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_713_, v_v_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_722_, lean_object* v_f_723_, lean_object* v_v_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_723_, v_v_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_732_, lean_object* v_f_733_, lean_object* v_v_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v_pu_boxed_741_; lean_object* v_res_742_; 
v_pu_boxed_741_ = lean_unbox(v_pu_732_);
v_res_742_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_741_, v_f_733_, v_v_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_742_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_754_ = l_Lean_stringToMessageData(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_776_, lean_object* v_origDecl_777_, uint8_t v_isMeta_778_, uint8_t v_isPublic_779_, lean_object* v_init_780_, lean_object* v_x_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v_k_788_; lean_object* v_l_789_; lean_object* v_r_790_; lean_object* v___x_791_; 
v_k_788_ = lean_ctor_get(v_x_781_, 1);
lean_inc(v_k_788_);
v_l_789_ = lean_ctor_get(v_x_781_, 3);
lean_inc(v_l_789_);
v_r_790_ = lean_ctor_get(v_x_781_, 4);
lean_inc(v_r_790_);
lean_dec_ref_known(v_x_781_, 5);
lean_inc_ref(v_origDecl_777_);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_776_, v_origDecl_777_, v_isMeta_778_, v_isPublic_779_, v_init_780_, v_l_789_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_1153_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_snd_793_ = lean_ctor_get(v_a_792_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_a_792_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_a_792_, 0);
lean_dec(v_unused_1154_);
v___x_795_ = v_a_792_;
v_isShared_796_ = v_isSharedCheck_1153_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_dec(v_a_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_1153_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_848_; uint8_t v___x_850_; uint8_t v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; 
v___x_797_ = lean_box(0);
v___x_850_ = l_Lean_NameSet_contains(v_snd_793_, v_k_788_);
if (v___x_850_ == 0)
{
lean_object* v___x_890_; lean_object* v_env_891_; lean_object* v___x_892_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; uint8_t v___y_900_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; uint8_t v___y_934_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; uint8_t v___y_944_; uint8_t v___y_945_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; uint8_t v___y_952_; uint8_t v___y_953_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; uint8_t v___y_964_; uint8_t v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; uint8_t v___y_978_; uint8_t v___y_979_; lean_object* v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; uint8_t v___y_1045_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v___x_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; uint8_t v___y_1101_; uint8_t v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; uint8_t v___y_1132_; uint8_t v___y_1134_; 
v___x_890_ = lean_st_ref_get(v___y_786_);
v_env_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_ref(v_env_891_);
lean_dec(v___x_890_);
v___x_892_ = lean_box(0);
lean_inc(v_k_788_);
v___x_1097_ = l_Lean_NameSet_insert(v_snd_793_, v_k_788_);
if (v_isMeta_778_ == 0)
{
v___y_1134_ = v___x_850_;
goto v___jp_1133_;
}
else
{
v___y_1134_ = v_isPublic_779_;
goto v___jp_1133_;
}
v___jp_893_:
{
lean_object* v_toSignature_901_; lean_object* v_name_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v___y_896_);
v_toSignature_901_ = lean_ctor_get(v_origDecl_777_, 0);
lean_inc_ref(v_toSignature_901_);
lean_dec_ref(v_origDecl_777_);
v_name_902_ = lean_ctor_get(v_toSignature_901_, 0);
lean_inc(v_name_902_);
lean_dec_ref(v_toSignature_901_);
v___x_903_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_904_ = l_Lean_MessageData_ofConstName(v_name_902_, v___x_850_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_MessageData_ofConstName(v_k_788_, v___x_850_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_Environment_header(v_env_891_);
lean_dec_ref(v_env_891_);
v___x_913_ = l_Lean_EnvironmentHeader_moduleNames(v___x_912_);
v___x_914_ = lean_array_get(v___x_892_, v___x_913_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___x_913_);
v___x_915_ = l_Lean_MessageData_ofName(v___x_914_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_911_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_918_, v___y_899_, v___y_898_, v___y_895_, v___y_894_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
v___jp_928_:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_891_, v_k_788_);
if (lean_obj_tag(v___x_935_) == 1)
{
lean_object* v_val_936_; uint8_t v___x_937_; 
v_val_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_935_, 1);
lean_inc(v_k_788_);
lean_inc_ref(v_env_891_);
v___x_937_ = l_Lean_isMarkedMeta(v_env_891_, v_k_788_);
if (v___x_937_ == 0)
{
lean_del_object(v___x_795_);
v___y_894_ = v___y_929_;
v___y_895_ = v___y_930_;
v___y_896_ = v___y_931_;
v___y_897_ = v_val_936_;
v___y_898_ = v___y_933_;
v___y_899_ = v___y_932_;
v___y_900_ = v___y_934_;
goto v___jp_893_;
}
else
{
if (v___x_850_ == 0)
{
lean_dec(v_val_936_);
lean_dec_ref(v_env_891_);
v___y_862_ = v___y_934_;
v___y_863_ = v___y_931_;
v___y_864_ = v___y_932_;
v___y_865_ = v___y_933_;
v___y_866_ = v___y_930_;
v___y_867_ = v___y_929_;
goto v___jp_861_;
}
else
{
lean_del_object(v___x_795_);
v___y_894_ = v___y_929_;
v___y_895_ = v___y_930_;
v___y_896_ = v___y_931_;
v___y_897_ = v_val_936_;
v___y_898_ = v___y_933_;
v___y_899_ = v___y_932_;
v___y_900_ = v___y_934_;
goto v___jp_893_;
}
}
}
else
{
lean_dec(v___x_935_);
lean_dec_ref(v_env_891_);
v___y_862_ = v___y_934_;
v___y_863_ = v___y_931_;
v___y_864_ = v___y_932_;
v___y_865_ = v___y_933_;
v___y_866_ = v___y_930_;
v___y_867_ = v___y_929_;
goto v___jp_861_;
}
}
v___jp_938_:
{
if (v___y_945_ == 0)
{
lean_dec_ref(v_env_891_);
lean_del_object(v___x_795_);
v___y_852_ = v___y_944_;
v___y_853_ = v___y_941_;
v___y_854_ = v___y_943_;
v___y_855_ = v___y_942_;
v___y_856_ = v___y_940_;
v___y_857_ = v___y_939_;
goto v___jp_851_;
}
else
{
lean_dec(v_r_790_);
v___y_929_ = v___y_939_;
v___y_930_ = v___y_940_;
v___y_931_ = v___y_941_;
v___y_932_ = v___y_943_;
v___y_933_ = v___y_942_;
v___y_934_ = v___y_944_;
goto v___jp_928_;
}
}
v___jp_946_:
{
if (v___y_953_ == 0)
{
v___y_939_ = v___y_947_;
v___y_940_ = v___y_948_;
v___y_941_ = v___y_949_;
v___y_942_ = v___y_951_;
v___y_943_ = v___y_950_;
v___y_944_ = v___y_952_;
v___y_945_ = v___x_850_;
goto v___jp_938_;
}
else
{
if (v_isMeta_778_ == 0)
{
lean_dec(v_r_790_);
v___y_929_ = v___y_947_;
v___y_930_ = v___y_948_;
v___y_931_ = v___y_949_;
v___y_932_ = v___y_950_;
v___y_933_ = v___y_951_;
v___y_934_ = v___y_952_;
goto v___jp_928_;
}
else
{
v___y_939_ = v___y_947_;
v___y_940_ = v___y_948_;
v___y_941_ = v___y_949_;
v___y_942_ = v___y_951_;
v___y_943_ = v___y_950_;
v___y_944_ = v___y_952_;
v___y_945_ = v___x_850_;
goto v___jp_938_;
}
}
}
v___jp_954_:
{
uint8_t v___x_961_; uint8_t v___x_962_; 
v___x_961_ = 1;
v___x_962_ = l_Lean_instBEqIRPhases_beq(v___y_960_, v___x_961_);
v___y_947_ = v___y_955_;
v___y_948_ = v___y_956_;
v___y_949_ = v___y_957_;
v___y_950_ = v___y_959_;
v___y_951_ = v___y_958_;
v___y_952_ = v___y_960_;
v___y_953_ = v___x_962_;
goto v___jp_946_;
}
v___jp_963_:
{
if (v___y_964_ == 0)
{
v___y_955_ = v___y_970_;
v___y_956_ = v___y_969_;
v___y_957_ = v___y_966_;
v___y_958_ = v___y_968_;
v___y_959_ = v___y_967_;
v___y_960_ = v___y_965_;
goto v___jp_954_;
}
else
{
if (v___x_850_ == 0)
{
v___y_947_ = v___y_970_;
v___y_948_ = v___y_969_;
v___y_949_ = v___y_966_;
v___y_950_ = v___y_967_;
v___y_951_ = v___y_968_;
v___y_952_ = v___y_965_;
v___y_953_ = v___x_850_;
goto v___jp_946_;
}
else
{
v___y_955_ = v___y_970_;
v___y_956_ = v___y_969_;
v___y_957_ = v___y_966_;
v___y_958_ = v___y_968_;
v___y_959_ = v___y_967_;
v___y_960_ = v___y_965_;
goto v___jp_954_;
}
}
}
v___jp_971_:
{
if (v___y_979_ == 0)
{
v___y_964_ = v___y_973_;
v___y_965_ = v___y_978_;
v___y_966_ = v___y_972_;
v___y_967_ = v___y_975_;
v___y_968_ = v___y_977_;
v___y_969_ = v___y_974_;
v___y_970_ = v___y_976_;
goto v___jp_963_;
}
else
{
lean_object* v___x_980_; 
lean_dec(v___y_972_);
lean_del_object(v___x_795_);
lean_dec(v_r_790_);
v___x_980_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_891_, v_k_788_);
if (lean_obj_tag(v___x_980_) == 1)
{
lean_object* v_toSignature_981_; lean_object* v_val_982_; lean_object* v_name_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_toSignature_981_ = lean_ctor_get(v_origDecl_777_, 0);
lean_inc_ref(v_toSignature_981_);
lean_dec_ref(v_origDecl_777_);
v_val_982_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v___x_980_, 1);
v_name_983_ = lean_ctor_get(v_toSignature_981_, 0);
lean_inc(v_name_983_);
lean_dec_ref(v_toSignature_981_);
v___x_984_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_985_ = l_Lean_MessageData_ofConstName(v_name_983_, v___x_850_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_MessageData_ofConstName(v_k_788_, v___x_850_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Environment_header(v_env_891_);
lean_dec_ref(v_env_891_);
v___x_994_ = l_Lean_EnvironmentHeader_moduleNames(v___x_993_);
v___x_995_ = lean_array_get(v___x_892_, v___x_994_, v_val_982_);
lean_dec(v_val_982_);
lean_dec_ref(v___x_994_);
v___x_996_ = l_Lean_MessageData_ofName(v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_992_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_999_, v___y_975_, v___y_977_, v___y_974_, v___y_976_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_toSignature_1009_; lean_object* v_name_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v___x_980_);
lean_dec_ref(v_env_891_);
v_toSignature_1009_ = lean_ctor_get(v_origDecl_777_, 0);
lean_inc_ref(v_toSignature_1009_);
lean_dec_ref(v_origDecl_777_);
v_name_1010_ = lean_ctor_get(v_toSignature_1009_, 0);
lean_inc(v_name_1010_);
lean_dec_ref(v_toSignature_1009_);
v___x_1011_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_1012_ = l_Lean_MessageData_ofConstName(v_name_1010_, v___x_850_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_ofConstName(v_k_788_, v___x_850_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1019_, v___y_975_, v___y_977_, v___y_974_, v___y_976_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
v___jp_1029_:
{
if (v___y_1037_ == 0)
{
v___y_972_ = v___y_1030_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1031_;
v___y_975_ = v___y_1033_;
v___y_976_ = v___y_1034_;
v___y_977_ = v___y_1035_;
v___y_978_ = v___y_1036_;
v___y_979_ = v___x_850_;
goto v___jp_971_;
}
else
{
v___y_972_ = v___y_1030_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1031_;
v___y_975_ = v___y_1033_;
v___y_976_ = v___y_1034_;
v___y_977_ = v___y_1035_;
v___y_978_ = v___y_1036_;
v___y_979_ = v_isMeta_778_;
goto v___jp_971_;
}
}
v___jp_1038_:
{
uint8_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = 0;
v___x_1047_ = l_Lean_instBEqIRPhases_beq(v___y_1045_, v___x_1046_);
v___y_1030_ = v___y_1039_;
v___y_1031_ = v___y_1041_;
v___y_1032_ = v___y_1040_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1044_;
v___y_1036_ = v___y_1045_;
v___y_1037_ = v___x_1047_;
goto v___jp_1029_;
}
v___jp_1048_:
{
uint8_t v___x_1055_; 
lean_inc(v_k_788_);
lean_inc_ref(v_env_891_);
v___x_1055_ = l_Lean_getIRPhases(v_env_891_, v_k_788_);
if (v___y_1054_ == 0)
{
v___y_1039_ = v___y_1049_;
v___y_1040_ = v___y_1054_;
v___y_1041_ = v___y_1050_;
v___y_1042_ = v___y_1051_;
v___y_1043_ = v___y_1052_;
v___y_1044_ = v___y_1053_;
v___y_1045_ = v___x_1055_;
goto v___jp_1038_;
}
else
{
if (v___x_850_ == 0)
{
v___y_1030_ = v___y_1049_;
v___y_1031_ = v___y_1050_;
v___y_1032_ = v___y_1054_;
v___y_1033_ = v___y_1051_;
v___y_1034_ = v___y_1052_;
v___y_1035_ = v___y_1053_;
v___y_1036_ = v___x_1055_;
v___y_1037_ = v___x_850_;
goto v___jp_1029_;
}
else
{
v___y_1039_ = v___y_1049_;
v___y_1040_ = v___y_1054_;
v___y_1041_ = v___y_1050_;
v___y_1042_ = v___y_1051_;
v___y_1043_ = v___y_1052_;
v___y_1044_ = v___y_1053_;
v___y_1045_ = v___x_1055_;
goto v___jp_1038_;
}
}
}
v___jp_1056_:
{
lean_object* v_toCold_1062_; lean_object* v_options_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_toCold_1062_ = lean_ctor_get(v___y_1060_, 0);
v_options_1063_ = lean_ctor_get(v_toCold_1062_, 2);
v___x_1064_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_1065_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
v___y_1049_ = v___y_1057_;
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___y_1058_;
v___y_1052_ = v___y_1061_;
v___y_1053_ = v___y_1059_;
v___y_1054_ = v___x_850_;
goto v___jp_1048_;
}
else
{
uint8_t v___x_1066_; 
v___x_1066_ = l_Lean_Environment_isImportedConst(v_env_891_, v_k_788_);
if (v___x_1066_ == 0)
{
v___y_1049_ = v___y_1057_;
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___y_1058_;
v___y_1052_ = v___y_1061_;
v___y_1053_ = v___y_1059_;
v___y_1054_ = v___x_1065_;
goto v___jp_1048_;
}
else
{
v___y_1049_ = v___y_1057_;
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___y_1058_;
v___y_1052_ = v___y_1061_;
v___y_1053_ = v___y_1059_;
v___y_1054_ = v___x_850_;
goto v___jp_1048_;
}
}
}
v___jp_1067_:
{
lean_object* v_toSignature_1071_; lean_object* v_name_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_toSignature_1071_ = lean_ctor_get(v_origDecl_777_, 0);
lean_inc_ref(v_toSignature_1071_);
lean_dec_ref(v_origDecl_777_);
v_name_1072_ = lean_ctor_get(v_toSignature_1071_, 0);
lean_inc(v_name_1072_);
lean_dec_ref(v_toSignature_1071_);
v___x_1073_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1074_ = l_Lean_MessageData_ofConstName(v_name_1072_, v___y_1069_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_MessageData_ofConstName(v_k_788_, v___y_1069_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_EnvironmentHeader_moduleNames(v___y_1070_);
v___x_1083_ = lean_array_get(v___x_892_, v___x_1082_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l_Lean_MessageData_ofName(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1081_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1087_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
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
v___jp_1098_:
{
if (v___y_1101_ == 0)
{
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
v___y_1057_ = v___x_1097_;
v___y_1058_ = v___y_783_;
v___y_1059_ = v___y_784_;
v___y_1060_ = v___y_785_;
v___y_1061_ = v___y_786_;
goto v___jp_1056_;
}
else
{
lean_object* v_toSignature_1102_; lean_object* v_name_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v___x_1097_);
lean_dec_ref(v_env_891_);
lean_del_object(v___x_795_);
lean_dec(v_r_790_);
v_toSignature_1102_ = lean_ctor_get(v_origDecl_777_, 0);
lean_inc_ref(v_toSignature_1102_);
lean_dec_ref(v_origDecl_777_);
v_name_1103_ = lean_ctor_get(v_toSignature_1102_, 0);
lean_inc(v_name_1103_);
lean_dec_ref(v_toSignature_1102_);
v___x_1104_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1105_ = l_Lean_MessageData_ofConstName(v_name_1103_, v___x_850_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_MessageData_ofConstName(v_k_788_, v___x_850_);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_EnvironmentHeader_moduleNames(v___y_1099_);
v___x_1114_ = lean_array_get(v___x_892_, v___x_1113_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = l_Lean_MessageData_ofName(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1112_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1118_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
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
v___jp_1128_:
{
if (v___y_1132_ == 0)
{
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
v___y_1057_ = v___x_1097_;
v___y_1058_ = v___y_783_;
v___y_1059_ = v___y_784_;
v___y_1060_ = v___y_785_;
v___y_1061_ = v___y_786_;
goto v___jp_1056_;
}
else
{
lean_dec(v___x_1097_);
lean_dec_ref(v_env_891_);
lean_del_object(v___x_795_);
lean_dec(v_r_790_);
v___y_1068_ = v___y_1130_;
v___y_1069_ = v___y_1129_;
v___y_1070_ = v___y_1131_;
goto v___jp_1067_;
}
}
v___jp_1133_:
{
if (v___y_1134_ == 0)
{
v___y_1057_ = v___x_1097_;
v___y_1058_ = v___y_783_;
v___y_1059_ = v___y_784_;
v___y_1060_ = v___y_785_;
v___y_1061_ = v___y_786_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_891_, v_k_788_);
if (lean_obj_tag(v___x_1135_) == 1)
{
lean_object* v_val_1136_; uint8_t v___x_1137_; 
v_val_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v___x_1135_, 1);
lean_inc(v_k_788_);
lean_inc_ref(v_env_891_);
v___x_1137_ = l_Lean_isMarkedMeta(v_env_891_, v_k_788_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v_modules_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1138_ = l_Lean_Environment_header(v_env_891_);
v_modules_1139_ = lean_ctor_get(v___x_1138_, 3);
lean_inc_ref(v_modules_1139_);
v___x_1140_ = lean_array_get_size(v_modules_1139_);
v___x_1141_ = lean_nat_dec_lt(v_val_1136_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_dec_ref(v_modules_1139_);
v___y_1129_ = v___x_1137_;
v___y_1130_ = v_val_1136_;
v___y_1131_ = v___x_1138_;
v___y_1132_ = v___x_1137_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1142_; lean_object* v_toImport_1143_; uint8_t v_isExported_1144_; 
v___x_1142_ = lean_array_fget(v_modules_1139_, v_val_1136_);
lean_dec_ref(v_modules_1139_);
v_toImport_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_toImport_1143_);
lean_dec(v___x_1142_);
v_isExported_1144_ = lean_ctor_get_uint8(v_toImport_1143_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1143_);
if (v_isExported_1144_ == 0)
{
lean_dec(v___x_1097_);
lean_dec_ref(v_env_891_);
lean_del_object(v___x_795_);
lean_dec(v_r_790_);
v___y_1068_ = v_val_1136_;
v___y_1069_ = v___x_1137_;
v___y_1070_ = v___x_1138_;
goto v___jp_1067_;
}
else
{
v___y_1129_ = v___x_1137_;
v___y_1130_ = v_val_1136_;
v___y_1131_ = v___x_1138_;
v___y_1132_ = v___x_1137_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v_modules_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1145_ = l_Lean_Environment_header(v_env_891_);
v_modules_1146_ = lean_ctor_get(v___x_1145_, 3);
lean_inc_ref(v_modules_1146_);
v___x_1147_ = lean_array_get_size(v_modules_1146_);
v___x_1148_ = lean_nat_dec_lt(v_val_1136_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec_ref(v_modules_1146_);
v___y_1099_ = v___x_1145_;
v___y_1100_ = v_val_1136_;
v___y_1101_ = v___x_850_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1149_; lean_object* v_toImport_1150_; uint8_t v_isExported_1151_; 
v___x_1149_ = lean_array_fget(v_modules_1146_, v_val_1136_);
lean_dec_ref(v_modules_1146_);
v_toImport_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_toImport_1150_);
lean_dec(v___x_1149_);
v_isExported_1151_ = lean_ctor_get_uint8(v_toImport_1150_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1150_);
if (v_isExported_1151_ == 0)
{
v___y_1099_ = v___x_1145_;
v___y_1100_ = v_val_1136_;
v___y_1101_ = v___x_1137_;
goto v___jp_1098_;
}
else
{
v___y_1099_ = v___x_1145_;
v___y_1100_ = v_val_1136_;
v___y_1101_ = v___x_850_;
goto v___jp_1098_;
}
}
}
}
else
{
lean_dec(v___x_1135_);
v___y_1057_ = v___x_1097_;
v___y_1058_ = v___y_783_;
v___y_1059_ = v___y_784_;
v___y_1060_ = v___y_785_;
v___y_1061_ = v___y_786_;
goto v___jp_1056_;
}
}
}
}
else
{
lean_del_object(v___x_795_);
lean_dec(v_k_788_);
v_init_780_ = v___x_797_;
v_x_781_ = v_r_790_;
v___y_782_ = v_snd_793_;
goto _start;
}
v___jp_798_:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; uint8_t v___x_806_; lean_object* v___x_807_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v___x_806_ = lean_unbox(v_a_805_);
v___x_807_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_788_, v___x_806_, v___y_803_);
lean_dec(v_k_788_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
if (lean_obj_tag(v_a_808_) == 1)
{
lean_object* v_val_809_; uint8_t v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_val_809_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_a_808_, 1);
v___x_810_ = lean_unbox(v_a_805_);
lean_dec(v_a_805_);
v___x_811_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_810_);
v___x_812_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_811_, v_val_809_, v_pu_776_);
lean_dec(v_val_809_);
lean_inc_ref(v_origDecl_777_);
v___x_813_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_776_, v_origDecl_777_, v_isMeta_778_, v_isPublic_779_, v___x_812_, v___y_800_, v___y_802_, v___y_801_, v___y_799_, v___y_803_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v_snd_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v_snd_815_ = lean_ctor_get(v_a_814_, 1);
lean_inc(v_snd_815_);
lean_dec(v_a_814_);
v_init_780_ = v___x_797_;
v_x_781_ = v_r_790_;
v___y_782_ = v_snd_815_;
goto _start;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_r_790_);
lean_dec_ref(v_origDecl_777_);
v_a_817_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_813_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_813_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_dec(v_a_808_);
lean_dec(v_a_805_);
v_init_780_ = v___x_797_;
v_x_781_ = v_r_790_;
v___y_782_ = v___y_800_;
goto _start;
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_a_805_);
lean_dec(v___y_800_);
lean_dec(v_r_790_);
lean_dec_ref(v_origDecl_777_);
v_a_826_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_807_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_807_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v___y_800_);
lean_dec(v_r_790_);
lean_dec(v_k_788_);
lean_dec_ref(v_origDecl_777_);
v_a_834_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_804_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_804_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
v___jp_842_:
{
if (v___y_848_ == 0)
{
lean_dec(v_k_788_);
v_init_780_ = v___x_797_;
v_x_781_ = v_r_790_;
v___y_782_ = v___y_844_;
goto _start;
}
else
{
v___y_799_ = v___y_843_;
v___y_800_ = v___y_844_;
v___y_801_ = v___y_845_;
v___y_802_ = v___y_846_;
v___y_803_ = v___y_847_;
goto v___jp_798_;
}
}
v___jp_851_:
{
uint8_t v___x_858_; uint8_t v___x_859_; 
v___x_858_ = 2;
v___x_859_ = l_Lean_instBEqIRPhases_beq(v___y_852_, v___x_858_);
if (v___x_859_ == 0)
{
if (v_isPublic_779_ == 0)
{
v___y_843_ = v___y_856_;
v___y_844_ = v___y_853_;
v___y_845_ = v___y_855_;
v___y_846_ = v___y_854_;
v___y_847_ = v___y_857_;
v___y_848_ = v___x_850_;
goto v___jp_842_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = l_Lean_isPrivateName(v_k_788_);
v___y_843_ = v___y_856_;
v___y_844_ = v___y_853_;
v___y_845_ = v___y_855_;
v___y_846_ = v___y_854_;
v___y_847_ = v___y_857_;
v___y_848_ = v___x_860_;
goto v___jp_842_;
}
}
else
{
v___y_799_ = v___y_856_;
v___y_800_ = v___y_853_;
v___y_801_ = v___y_855_;
v___y_802_ = v___y_854_;
v___y_803_ = v___y_857_;
goto v___jp_798_;
}
}
v___jp_861_:
{
lean_object* v_toSignature_868_; lean_object* v_name_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v___y_863_);
v_toSignature_868_ = lean_ctor_get(v_origDecl_777_, 0);
lean_inc_ref(v_toSignature_868_);
lean_dec_ref(v_origDecl_777_);
v_name_869_ = lean_ctor_get(v_toSignature_868_, 0);
lean_inc(v_name_869_);
lean_dec_ref(v_toSignature_868_);
v___x_870_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_871_ = l_Lean_MessageData_ofConstName(v_name_869_, v___x_850_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 7);
lean_ctor_set(v___x_795_, 1, v___x_871_);
lean_ctor_set(v___x_795_, 0, v___x_870_);
v___x_873_ = v___x_795_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_889_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v___x_874_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_MessageData_ofConstName(v_k_788_, v___x_850_);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_879_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
else
{
lean_dec(v_r_790_);
lean_dec(v_k_788_);
lean_dec_ref(v_origDecl_777_);
return v___x_791_;
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v_origDecl_777_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_init_780_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___y_782_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(uint8_t v_pu_1158_, lean_object* v_origDecl_1159_, uint8_t v_isMeta_1160_, uint8_t v_isPublic_1161_, lean_object* v_code_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = l_Lean_NameSet_empty;
v___x_1170_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_1158_, v_code_1162_, v___x_1169_);
v___x_1171_ = lean_box(0);
v___x_1172_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_1158_, v_origDecl_1159_, v_isMeta_1160_, v_isPublic_1161_, v___x_1171_, v___x_1170_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1189_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1189_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1189_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_snd_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1187_; 
v_snd_1177_ = lean_ctor_get(v_a_1173_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_a_1173_, 0);
lean_dec(v_unused_1188_);
v___x_1179_ = v_a_1173_;
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snd_1177_);
lean_dec(v_a_1173_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1171_);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1177_);
v___x_1182_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1182_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v_a_1190_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1172_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1172_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(lean_object* v_pu_1198_, lean_object* v_origDecl_1199_, lean_object* v_isMeta_1200_, lean_object* v_isPublic_1201_, lean_object* v_code_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_pu_boxed_1209_; uint8_t v_isMeta_boxed_1210_; uint8_t v_isPublic_boxed_1211_; lean_object* v_res_1212_; 
v_pu_boxed_1209_ = lean_unbox(v_pu_1198_);
v_isMeta_boxed_1210_ = lean_unbox(v_isMeta_1200_);
v_isPublic_boxed_1211_ = lean_unbox(v_isPublic_1201_);
v_res_1212_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(v_pu_boxed_1209_, v_origDecl_1199_, v_isMeta_boxed_1210_, v_isPublic_boxed_1211_, v_code_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(uint8_t v_pu_1213_, lean_object* v_origDecl_1214_, uint8_t v_isMeta_1215_, uint8_t v_isPublic_1216_, lean_object* v_decl_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_value_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v_value_1224_ = lean_ctor_get(v_decl_1217_, 1);
lean_inc_ref(v_value_1224_);
lean_dec_ref(v_decl_1217_);
v___x_1225_ = lean_box(v_pu_1213_);
v___x_1226_ = lean_box(v_isMeta_1215_);
v___x_1227_ = lean_box(v_isPublic_1216_);
v___f_1228_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1228_, 0, v___x_1225_);
lean_closure_set(v___f_1228_, 1, v_origDecl_1214_);
lean_closure_set(v___f_1228_, 2, v___x_1226_);
lean_closure_set(v___f_1228_, 3, v___x_1227_);
v___x_1229_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_1228_, v_value_1224_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(lean_object* v_pu_1230_, lean_object* v_origDecl_1231_, lean_object* v_isMeta_1232_, lean_object* v_isPublic_1233_, lean_object* v_decl_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
uint8_t v_pu_boxed_1241_; uint8_t v_isMeta_boxed_1242_; uint8_t v_isPublic_boxed_1243_; lean_object* v_res_1244_; 
v_pu_boxed_1241_ = lean_unbox(v_pu_1230_);
v_isMeta_boxed_1242_ = lean_unbox(v_isMeta_1232_);
v_isPublic_boxed_1243_ = lean_unbox(v_isPublic_1233_);
v_res_1244_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_boxed_1241_, v_origDecl_1231_, v_isMeta_boxed_1242_, v_isPublic_boxed_1243_, v_decl_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(lean_object* v_pu_1245_, lean_object* v_origDecl_1246_, lean_object* v_isMeta_1247_, lean_object* v_isPublic_1248_, lean_object* v_init_1249_, lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_pu_boxed_1257_; uint8_t v_isMeta_boxed_1258_; uint8_t v_isPublic_boxed_1259_; lean_object* v_res_1260_; 
v_pu_boxed_1257_ = lean_unbox(v_pu_1245_);
v_isMeta_boxed_1258_ = lean_unbox(v_isMeta_1247_);
v_isPublic_boxed_1259_ = lean_unbox(v_isPublic_1248_);
v_res_1260_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_1257_, v_origDecl_1246_, v_isMeta_boxed_1258_, v_isPublic_boxed_1259_, v_init_1249_, v_x_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(lean_object* v_opt_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_toCold_1264_; lean_object* v_options_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_toCold_1264_ = lean_ctor_get(v___y_1262_, 0);
v_options_1265_ = lean_ctor_get(v_toCold_1264_, 2);
v___x_1266_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1265_, v_opt_1261_);
v___x_1267_ = lean_box(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1269_, v___y_1270_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_opt_1269_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1273_, lean_object* v_origDecl_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1340_; 
v___x_1280_ = lean_st_ref_get(v_a_1278_);
v___x_1281_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1282_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1281_, v_a_1277_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1340_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1340_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1339_; 
v___x_1287_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1288_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1287_, v_a_1277_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1339_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1339_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_env_1298_; lean_object* v___x_1299_; uint8_t v_isModule_1300_; 
v_env_1298_ = lean_ctor_get(v___x_1280_, 0);
lean_inc_ref(v_env_1298_);
lean_dec(v___x_1280_);
v___x_1299_ = l_Lean_Environment_header(v_env_1298_);
lean_dec_ref(v_env_1298_);
v_isModule_1300_ = lean_ctor_get_uint8(v___x_1299_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1299_);
if (v_isModule_1300_ == 0)
{
lean_dec(v_a_1289_);
lean_del_object(v___x_1285_);
lean_dec(v_a_1283_);
lean_dec_ref(v_origDecl_1274_);
goto v___jp_1293_;
}
else
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_unbox(v_a_1283_);
lean_dec(v_a_1283_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_unbox(v_a_1289_);
if (v___x_1302_ == 0)
{
lean_dec(v_a_1289_);
lean_del_object(v___x_1285_);
lean_dec_ref(v_origDecl_1274_);
goto v___jp_1293_;
}
else
{
lean_object* v___x_1303_; lean_object* v_toSignature_1304_; lean_object* v_env_1305_; lean_object* v_name_1306_; uint8_t v___x_1307_; uint8_t v___y_1309_; uint8_t v___x_1331_; uint8_t v___x_1332_; 
lean_del_object(v___x_1291_);
v___x_1303_ = lean_st_ref_get(v_a_1278_);
v_toSignature_1304_ = lean_ctor_get(v_origDecl_1274_, 0);
v_env_1305_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_ref(v_env_1305_);
lean_dec(v___x_1303_);
v_name_1306_ = lean_ctor_get(v_toSignature_1304_, 0);
lean_inc(v_name_1306_);
v___x_1307_ = l_Lean_getIRPhases(v_env_1305_, v_name_1306_);
v___x_1331_ = 2;
v___x_1332_ = l_Lean_instBEqIRPhases_beq(v___x_1307_, v___x_1331_);
if (v___x_1332_ == 0)
{
uint8_t v___x_1333_; 
lean_del_object(v___x_1285_);
v___x_1333_ = l_Lean_isPrivateName(v_name_1306_);
if (v___x_1333_ == 0)
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
v___y_1309_ = v___x_1334_;
goto v___jp_1308_;
}
else
{
lean_dec(v_a_1289_);
v___y_1309_ = v___x_1332_;
goto v___jp_1308_;
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec(v_a_1289_);
lean_dec_ref(v_origDecl_1274_);
v___x_1335_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1335_);
v___x_1337_ = v___x_1285_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
v___jp_1308_:
{
uint8_t v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = 1;
v___x_1311_ = l_Lean_instBEqIRPhases_beq(v___x_1307_, v___x_1310_);
v___x_1312_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1274_);
v___x_1313_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1273_, v_origDecl_1274_, v___x_1311_, v___y_1309_, v_origDecl_1274_, v___x_1312_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1322_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_fst_1318_; lean_object* v___x_1320_; 
v_fst_1318_ = lean_ctor_get(v_a_1314_, 0);
lean_inc(v_fst_1318_);
lean_dec(v_a_1314_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_fst_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_fst_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1323_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1313_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1313_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1289_);
lean_del_object(v___x_1285_);
lean_dec_ref(v_origDecl_1274_);
goto v___jp_1293_;
}
}
v___jp_1293_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(0);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1341_, lean_object* v_origDecl_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
uint8_t v_pu_boxed_1348_; lean_object* v_res_1349_; 
v_pu_boxed_1348_ = lean_unbox(v_pu_1341_);
v_res_1349_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1348_, v_origDecl_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1350_, v___y_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_opt_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(uint8_t v_isExporting_1364_, lean_object* v___x_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v_env_1374_; lean_object* v_nextMacroScope_1375_; lean_object* v_ngen_1376_; lean_object* v_auxDeclNGen_1377_; lean_object* v_traceState_1378_; lean_object* v_messages_1379_; lean_object* v_infoState_1380_; lean_object* v_snapshotTasks_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1393_; 
v___x_1373_ = lean_st_ref_take(v___y_1371_);
v_env_1374_ = lean_ctor_get(v___x_1373_, 0);
v_nextMacroScope_1375_ = lean_ctor_get(v___x_1373_, 1);
v_ngen_1376_ = lean_ctor_get(v___x_1373_, 2);
v_auxDeclNGen_1377_ = lean_ctor_get(v___x_1373_, 3);
v_traceState_1378_ = lean_ctor_get(v___x_1373_, 4);
v_messages_1379_ = lean_ctor_get(v___x_1373_, 6);
v_infoState_1380_ = lean_ctor_get(v___x_1373_, 7);
v_snapshotTasks_1381_ = lean_ctor_get(v___x_1373_, 8);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1373_, 5);
lean_dec(v_unused_1394_);
v___x_1383_ = v___x_1373_;
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snapshotTasks_1381_);
lean_inc(v_infoState_1380_);
lean_inc(v_messages_1379_);
lean_inc(v_traceState_1378_);
lean_inc(v_auxDeclNGen_1377_);
lean_inc(v_ngen_1376_);
lean_inc(v_nextMacroScope_1375_);
lean_inc(v_env_1374_);
lean_dec(v___x_1373_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = l_Lean_Environment_setExporting(v_env_1374_, v_isExporting_1364_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 5, v___x_1365_);
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_nextMacroScope_1375_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_ngen_1376_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_auxDeclNGen_1377_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_traceState_1378_);
lean_ctor_set(v_reuseFailAlloc_1392_, 5, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1392_, 6, v_messages_1379_);
lean_ctor_set(v_reuseFailAlloc_1392_, 7, v_infoState_1380_);
lean_ctor_set(v_reuseFailAlloc_1392_, 8, v_snapshotTasks_1381_);
v___x_1387_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1388_ = lean_st_ref_put(v___y_1371_, v___x_1387_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___y_1367_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(lean_object* v_isExporting_1395_, lean_object* v___x_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_isExporting_boxed_1404_; lean_object* v_res_1405_; 
v_isExporting_boxed_1404_ = lean_unbox(v_isExporting_1395_);
v_res_1405_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_boxed_1404_, v___x_1396_, v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v_x_1397_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(lean_object* v___f_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v_a_x3f_1412_){
_start:
{
if (lean_obj_tag(v_a_x3f_1412_) == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
v___x_1415_ = lean_apply_7(v___f_1406_, v___x_1414_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, lean_box(0));
return v___x_1415_;
}
else
{
lean_object* v_val_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v___y_1407_);
v_val_1416_ = lean_ctor_get(v_a_x3f_1412_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_a_x3f_1412_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1418_ = v_a_x3f_1412_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_val_1416_);
lean_dec(v_a_x3f_1412_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1423_; 
v_fst_1420_ = lean_ctor_get(v_val_1416_, 0);
lean_inc(v_fst_1420_);
v_snd_1421_ = lean_ctor_get(v_val_1416_, 1);
lean_inc(v_snd_1421_);
lean_dec(v_val_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_fst_1420_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1420_);
v___x_1423_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
v___x_1424_ = lean_apply_7(v___f_1406_, v___x_1423_, v_snd_1421_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, lean_box(0));
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(lean_object* v___f_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v_a_x3f_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v_a_x3f_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(lean_object* v_x_1436_, uint8_t v_isExporting_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_env_1445_; lean_object* v___x_1446_; uint8_t v_isModule_1447_; 
v___x_1444_ = lean_st_ref_get(v___y_1442_);
v_env_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc_ref(v_env_1445_);
lean_dec(v___x_1444_);
v___x_1446_ = l_Lean_Environment_header(v_env_1445_);
v_isModule_1447_ = lean_ctor_get_uint8(v___x_1446_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1446_);
if (v_isModule_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref(v_env_1445_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
v___x_1448_ = lean_apply_6(v_x_1436_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, lean_box(0));
return v___x_1448_;
}
else
{
uint8_t v_isExporting_1449_; 
v_isExporting_1449_ = lean_ctor_get_uint8(v_env_1445_, sizeof(void*)*8);
lean_dec_ref(v_env_1445_);
if (v_isExporting_1437_ == 0)
{
if (v_isExporting_1449_ == 0)
{
lean_object* v___x_1528_; 
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
v___x_1528_ = lean_apply_6(v_x_1436_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, lean_box(0));
return v___x_1528_;
}
else
{
goto v___jp_1450_;
}
}
else
{
if (v_isExporting_1449_ == 0)
{
goto v___jp_1450_;
}
else
{
lean_object* v___x_1529_; 
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
v___x_1529_ = lean_apply_6(v_x_1436_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, lean_box(0));
return v___x_1529_;
}
}
v___jp_1450_:
{
lean_object* v___x_1451_; lean_object* v_env_1452_; lean_object* v_nextMacroScope_1453_; lean_object* v_ngen_1454_; lean_object* v_auxDeclNGen_1455_; lean_object* v_traceState_1456_; lean_object* v_messages_1457_; lean_object* v_infoState_1458_; lean_object* v_snapshotTasks_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1526_; 
v___x_1451_ = lean_st_ref_take(v___y_1442_);
v_env_1452_ = lean_ctor_get(v___x_1451_, 0);
v_nextMacroScope_1453_ = lean_ctor_get(v___x_1451_, 1);
v_ngen_1454_ = lean_ctor_get(v___x_1451_, 2);
v_auxDeclNGen_1455_ = lean_ctor_get(v___x_1451_, 3);
v_traceState_1456_ = lean_ctor_get(v___x_1451_, 4);
v_messages_1457_ = lean_ctor_get(v___x_1451_, 6);
v_infoState_1458_ = lean_ctor_get(v___x_1451_, 7);
v_snapshotTasks_1459_ = lean_ctor_get(v___x_1451_, 8);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1451_, 5);
lean_dec(v_unused_1527_);
v___x_1461_ = v___x_1451_;
v_isShared_1462_ = v_isSharedCheck_1526_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snapshotTasks_1459_);
lean_inc(v_infoState_1458_);
lean_inc(v_messages_1457_);
lean_inc(v_traceState_1456_);
lean_inc(v_auxDeclNGen_1455_);
lean_inc(v_ngen_1454_);
lean_inc(v_nextMacroScope_1453_);
lean_inc(v_env_1452_);
lean_dec(v___x_1451_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1526_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1463_ = l_Lean_Environment_setExporting(v_env_1452_, v_isExporting_1437_);
v___x_1464_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 5, v___x_1464_);
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_nextMacroScope_1453_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_ngen_1454_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_auxDeclNGen_1455_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_traceState_1456_);
lean_ctor_set(v_reuseFailAlloc_1525_, 5, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1525_, 6, v_messages_1457_);
lean_ctor_set(v_reuseFailAlloc_1525_, 7, v_infoState_1458_);
lean_ctor_set(v_reuseFailAlloc_1525_, 8, v_snapshotTasks_1459_);
v___x_1466_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v_r_1470_; 
v___x_1467_ = lean_st_ref_put(v___y_1442_, v___x_1466_);
v___x_1468_ = lean_box(v_isExporting_1449_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1469_, 0, v___x_1468_);
lean_closure_set(v___f_1469_, 1, v___x_1464_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
v_r_1470_ = lean_apply_6(v_x_1436_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, lean_box(0));
if (lean_obj_tag(v_r_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1505_; 
v_a_1471_ = lean_ctor_get(v_r_1470_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_r_1470_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1473_ = v_r_1470_;
v_isShared_1474_ = v_isSharedCheck_1505_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v_r_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1505_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
lean_inc(v_a_1471_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set_tag(v___x_1473_, 1);
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1469_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___x_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1495_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1495_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1495_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_fst_1482_; lean_object* v_snd_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1493_; 
v_fst_1482_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_fst_1482_);
lean_dec(v_a_1471_);
v_snd_1483_ = lean_ctor_get(v_a_1478_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_a_1478_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_a_1478_, 0);
lean_dec(v_unused_1494_);
v___x_1485_ = v_a_1478_;
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_snd_1483_);
lean_dec(v_a_1478_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v_fst_1482_);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_fst_1482_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1483_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1488_);
v___x_1490_ = v___x_1480_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1471_);
v_a_1496_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1477_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1477_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v_r_1470_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v_r_1470_, 1);
v___x_1507_ = lean_box(0);
v___x_1508_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1469_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___x_1507_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v___x_1508_, 0);
lean_dec(v_unused_1516_);
v___x_1510_ = v___x_1508_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v___x_1508_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 1);
lean_ctor_set(v___x_1510_, 0, v_a_1506_);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1506_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_a_1506_);
v_a_1517_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1508_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1508_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_x_1530_, lean_object* v_isExporting_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_isExporting_boxed_1538_; lean_object* v_res_1539_; 
v_isExporting_boxed_1538_ = lean_unbox(v_isExporting_1531_);
v_res_1539_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1530_, v_isExporting_boxed_1538_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_00_u03b1_1540_, lean_object* v_x_1541_, uint8_t v_isExporting_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1541_, v_isExporting_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_x_1551_, lean_object* v_isExporting_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v_isExporting_boxed_1559_; lean_object* v_res_1560_; 
v_isExporting_boxed_1559_ = lean_unbox(v_isExporting_1552_);
v_res_1560_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_1550_, v_x_1551_, v_isExporting_boxed_1559_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(lean_object* v_opt_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_toCold_1565_; lean_object* v_options_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_toCold_1565_ = lean_ctor_get(v___y_1563_, 0);
v_options_1566_ = lean_ctor_get(v_toCold_1565_, 2);
v___x_1567_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1566_, v_opt_1561_);
v___x_1568_ = lean_box(v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___y_1562_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(lean_object* v_opt_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_1571_, v___y_1572_, v___y_1573_);
lean_dec_ref(v___y_1573_);
lean_dec_ref(v_opt_1571_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(lean_object* v_cls_1576_, lean_object* v_msg_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_toCold_1584_; lean_object* v_ref_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_toCold_1584_ = lean_ctor_get(v___y_1581_, 0);
v_ref_1585_ = lean_ctor_get(v___y_1581_, 2);
v___x_1586_ = lean_st_ref_get(v___y_1582_);
v___x_1587_ = lean_st_ref_get(v___y_1580_);
v___x_1588_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1579_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1649_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1649_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1649_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_env_1593_; lean_object* v_lctx_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1647_; 
v_env_1593_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_env_1593_);
lean_dec(v___x_1586_);
v_lctx_1594_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1587_, 1);
lean_dec(v_unused_1648_);
v___x_1596_ = v___x_1587_;
v_isShared_1597_ = v_isSharedCheck_1647_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_lctx_1594_);
lean_dec(v___x_1587_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1647_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_options_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_traceState_1601_; lean_object* v_env_1602_; lean_object* v_nextMacroScope_1603_; lean_object* v_ngen_1604_; lean_object* v_auxDeclNGen_1605_; lean_object* v_cache_1606_; lean_object* v_messages_1607_; lean_object* v_infoState_1608_; lean_object* v_snapshotTasks_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1646_; 
v_options_1598_ = lean_ctor_get(v_toCold_1584_, 2);
v___x_1599_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
v___x_1600_ = lean_st_ref_take(v___y_1582_);
v_traceState_1601_ = lean_ctor_get(v___x_1600_, 4);
v_env_1602_ = lean_ctor_get(v___x_1600_, 0);
v_nextMacroScope_1603_ = lean_ctor_get(v___x_1600_, 1);
v_ngen_1604_ = lean_ctor_get(v___x_1600_, 2);
v_auxDeclNGen_1605_ = lean_ctor_get(v___x_1600_, 3);
v_cache_1606_ = lean_ctor_get(v___x_1600_, 5);
v_messages_1607_ = lean_ctor_get(v___x_1600_, 6);
v_infoState_1608_ = lean_ctor_get(v___x_1600_, 7);
v_snapshotTasks_1609_ = lean_ctor_get(v___x_1600_, 8);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1611_ = v___x_1600_;
v_isShared_1612_ = v_isSharedCheck_1646_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_snapshotTasks_1609_);
lean_inc(v_infoState_1608_);
lean_inc(v_messages_1607_);
lean_inc(v_cache_1606_);
lean_inc(v_traceState_1601_);
lean_inc(v_auxDeclNGen_1605_);
lean_inc(v_ngen_1604_);
lean_inc(v_nextMacroScope_1603_);
lean_inc(v_env_1602_);
lean_dec(v___x_1600_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1646_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
uint64_t v_tid_1613_; lean_object* v_traces_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1645_; 
v_tid_1613_ = lean_ctor_get_uint64(v_traceState_1601_, sizeof(void*)*1);
v_traces_1614_ = lean_ctor_get(v_traceState_1601_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_traceState_1601_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1616_ = v_traceState_1601_;
v_isShared_1617_ = v_isSharedCheck_1645_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_traces_1614_);
lean_dec(v_traceState_1601_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1645_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1618_ = lean_unbox(v_a_1589_);
lean_dec(v_a_1589_);
v___x_1619_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1594_, v___x_1618_);
lean_dec_ref(v_lctx_1594_);
lean_inc_ref(v_options_1598_);
v___x_1620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1620_, 0, v_env_1593_);
lean_ctor_set(v___x_1620_, 1, v___x_1599_);
lean_ctor_set(v___x_1620_, 2, v___x_1619_);
lean_ctor_set(v___x_1620_, 3, v_options_1598_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 3);
lean_ctor_set(v___x_1596_, 1, v_msg_1577_);
lean_ctor_set(v___x_1596_, 0, v___x_1620_);
v___x_1622_ = v___x_1596_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_msg_1577_);
v___x_1622_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; double v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
v___x_1625_ = 0;
v___x_1626_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1627_, 0, v_cls_1576_);
lean_ctor_set(v___x_1627_, 1, v___x_1623_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
lean_ctor_set_float(v___x_1627_, sizeof(void*)*3, v___x_1624_);
lean_ctor_set_float(v___x_1627_, sizeof(void*)*3 + 8, v___x_1624_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*3 + 16, v___x_1625_);
v___x_1628_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5));
v___x_1629_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1622_);
lean_ctor_set(v___x_1629_, 2, v___x_1628_);
lean_inc(v_ref_1585_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_ref_1585_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l_Lean_PersistentArray_push___redArg(v_traces_1614_, v___x_1630_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1631_);
v___x_1633_ = v___x_1616_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1631_);
lean_ctor_set_uint64(v_reuseFailAlloc_1643_, sizeof(void*)*1, v_tid_1613_);
v___x_1633_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 4, v___x_1633_);
v___x_1635_ = v___x_1611_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_env_1602_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_nextMacroScope_1603_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_ngen_1604_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_auxDeclNGen_1605_);
lean_ctor_set(v_reuseFailAlloc_1642_, 4, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1642_, 5, v_cache_1606_);
lean_ctor_set(v_reuseFailAlloc_1642_, 6, v_messages_1607_);
lean_ctor_set(v_reuseFailAlloc_1642_, 7, v_infoState_1608_);
lean_ctor_set(v_reuseFailAlloc_1642_, 8, v_snapshotTasks_1609_);
v___x_1635_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1636_ = lean_st_ref_put(v___y_1582_, v___x_1635_);
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___y_1578_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1638_);
v___x_1640_ = v___x_1591_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
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
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v___x_1587_);
lean_dec(v___x_1586_);
lean_dec(v___y_1578_);
lean_dec_ref(v_msg_1577_);
lean_dec(v_cls_1576_);
v_a_1650_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1588_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1588_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7___boxed(lean_object* v_cls_1658_, lean_object* v_msg_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1658_, v_msg_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1666_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object* v_keys_1667_, lean_object* v_i_1668_, lean_object* v_k_1669_){
_start:
{
lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = lean_array_get_size(v_keys_1667_);
v___x_1671_ = lean_nat_dec_lt(v_i_1668_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_dec(v_i_1668_);
return v___x_1671_;
}
else
{
lean_object* v_k_x27_1672_; uint8_t v___x_1673_; 
v_k_x27_1672_ = lean_array_fget_borrowed(v_keys_1667_, v_i_1668_);
v___x_1673_ = l_Lean_instBEqExtraModUse_beq(v_k_1669_, v_k_x27_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_nat_add(v_i_1668_, v___x_1674_);
lean_dec(v_i_1668_);
v_i_1668_ = v___x_1675_;
goto _start;
}
else
{
lean_dec(v_i_1668_);
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1677_, lean_object* v_i_1678_, lean_object* v_k_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_1677_, v_i_1678_, v_k_1679_);
lean_dec_ref(v_k_1679_);
lean_dec_ref(v_keys_1677_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1682_, size_t v_x_1683_, lean_object* v_x_1684_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
lean_object* v_es_1685_; lean_object* v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; lean_object* v_j_1689_; lean_object* v___x_1690_; 
v_es_1685_ = lean_ctor_get(v_x_1682_, 0);
v___x_1686_ = lean_box(2);
v___x_1687_ = ((size_t)31ULL);
v___x_1688_ = lean_usize_land(v_x_1683_, v___x_1687_);
v_j_1689_ = lean_usize_to_nat(v___x_1688_);
v___x_1690_ = lean_array_get_borrowed(v___x_1686_, v_es_1685_, v_j_1689_);
lean_dec(v_j_1689_);
switch(lean_obj_tag(v___x_1690_))
{
case 0:
{
lean_object* v_key_1691_; uint8_t v___x_1692_; 
v_key_1691_ = lean_ctor_get(v___x_1690_, 0);
v___x_1692_ = l_Lean_instBEqExtraModUse_beq(v_x_1684_, v_key_1691_);
return v___x_1692_;
}
case 1:
{
lean_object* v_node_1693_; size_t v___x_1694_; size_t v___x_1695_; 
v_node_1693_ = lean_ctor_get(v___x_1690_, 0);
v___x_1694_ = ((size_t)5ULL);
v___x_1695_ = lean_usize_shift_right(v_x_1683_, v___x_1694_);
v_x_1682_ = v_node_1693_;
v_x_1683_ = v___x_1695_;
goto _start;
}
default: 
{
uint8_t v___x_1697_; 
v___x_1697_ = 0;
return v___x_1697_;
}
}
}
else
{
lean_object* v_ks_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_ks_1698_ = lean_ctor_get(v_x_1682_, 0);
v___x_1699_ = lean_unsigned_to_nat(0u);
v___x_1700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_1698_, v___x_1699_, v_x_1684_);
return v___x_1700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
size_t v_x_26531__boxed_1704_; uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_x_26531__boxed_1704_ = lean_unbox_usize(v_x_1702_);
lean_dec(v_x_1702_);
v_res_1705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1701_, v_x_26531__boxed_1704_, v_x_1703_);
lean_dec_ref(v_x_1703_);
lean_dec_ref(v_x_1701_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
uint64_t v___x_1709_; size_t v___x_1710_; uint8_t v___x_1711_; 
v___x_1709_ = l_Lean_instHashableExtraModUse_hash(v_x_1708_);
v___x_1710_ = lean_uint64_to_usize(v___x_1709_);
v___x_1711_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1707_, v___x_1710_, v_x_1708_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_res_1714_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_1712_, v_x_1713_);
lean_dec_ref(v_x_1713_);
lean_dec_ref(v_x_1712_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1));
v___x_1719_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0));
v___x_1720_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7));
v___x_1729_ = l_Lean_stringToMessageData(v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
return v___x_1731_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_cls_1732_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4));
v___x_1733_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1734_ = l_Lean_Name_append(v___x_1733_, v_cls_1732_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11));
v___x_1737_ = l_Lean_stringToMessageData(v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object* v_mod_1745_, uint8_t v_isMeta_1746_, lean_object* v_hint_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v_env_1755_; uint8_t v_isExporting_1756_; lean_object* v___x_1757_; lean_object* v_env_1758_; lean_object* v___x_1759_; lean_object* v_entry_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1754_ = lean_st_ref_get(v___y_1752_);
v_env_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_ref(v_env_1755_);
lean_dec(v___x_1754_);
v_isExporting_1756_ = lean_ctor_get_uint8(v_env_1755_, sizeof(void*)*8);
lean_dec_ref(v_env_1755_);
v___x_1757_ = lean_st_ref_get(v___y_1752_);
v_env_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_ref(v_env_1758_);
lean_dec(v___x_1757_);
v___x_1759_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2);
lean_inc(v_mod_1745_);
v_entry_1760_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1760_, 0, v_mod_1745_);
lean_ctor_set_uint8(v_entry_1760_, sizeof(void*)*1, v_isExporting_1756_);
lean_ctor_set_uint8(v_entry_1760_, sizeof(void*)*1 + 1, v_isMeta_1746_);
v___x_1761_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1762_ = lean_box(1);
v___x_1763_ = lean_box(0);
v___x_1792_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1759_, v___x_1761_, v_env_1758_, v___x_1762_, v___x_1763_);
v___x_1793_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_1792_, v_entry_1760_);
lean_dec(v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v_toCold_1794_; lean_object* v_options_1795_; uint8_t v_hasTrace_1796_; 
v_toCold_1794_ = lean_ctor_get(v___y_1751_, 0);
v_options_1795_ = lean_ctor_get(v_toCold_1794_, 2);
v_hasTrace_1796_ = lean_ctor_get_uint8(v_options_1795_, sizeof(void*)*1);
if (v_hasTrace_1796_ == 0)
{
lean_dec(v_hint_1747_);
lean_dec(v_mod_1745_);
v___y_1765_ = v___y_1748_;
v___y_1766_ = v___y_1752_;
goto v___jp_1764_;
}
else
{
lean_object* v_inheritedTraceOptions_1797_; lean_object* v_cls_1798_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_inheritedTraceOptions_1797_ = lean_ctor_get(v_toCold_1794_, 11);
v_cls_1798_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4));
v___x_1820_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
v___x_1821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1797_, v_options_1795_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_dec(v_hint_1747_);
lean_dec(v_mod_1745_);
v___y_1765_ = v___y_1748_;
v___y_1766_ = v___y_1752_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1822_; lean_object* v___y_1824_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
if (v_isExporting_1756_ == 0)
{
lean_object* v___x_1831_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17));
v___y_1824_ = v___x_1831_;
goto v___jp_1823_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18));
v___y_1824_ = v___x_1832_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc_ref(v___y_1824_);
v___x_1825_ = l_Lean_stringToMessageData(v___y_1824_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1822_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
if (v_isMeta_1746_ == 0)
{
lean_object* v___x_1829_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15));
v___y_1807_ = v___x_1828_;
v___y_1808_ = v___x_1829_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16));
v___y_1807_ = v___x_1828_;
v___y_1808_ = v___x_1830_;
goto v___jp_1806_;
}
}
}
v___jp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1800_);
lean_ctor_set(v___x_1802_, 1, v___y_1801_);
v___x_1803_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1798_, v___x_1802_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v_snd_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v_snd_1805_ = lean_ctor_get(v_a_1804_, 1);
lean_inc(v_snd_1805_);
lean_dec(v_a_1804_);
v___y_1765_ = v_snd_1805_;
v___y_1766_ = v___y_1752_;
goto v___jp_1764_;
}
else
{
lean_dec_ref_known(v_entry_1760_, 1);
return v___x_1803_;
}
}
v___jp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
lean_inc_ref(v___y_1808_);
v___x_1809_ = l_Lean_stringToMessageData(v___y_1808_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___y_1807_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_MessageData_ofName(v_mod_1745_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_Name_isAnonymous(v_hint_1747_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
v___x_1817_ = l_Lean_MessageData_ofName(v_hint_1747_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___y_1800_ = v___x_1814_;
v___y_1801_ = v___x_1818_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1819_; 
lean_dec(v_hint_1747_);
v___x_1819_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9);
v___y_1800_ = v___x_1814_;
v___y_1801_ = v___x_1819_;
goto v___jp_1799_;
}
}
}
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref_known(v_entry_1760_, 1);
lean_dec(v_hint_1747_);
lean_dec(v_mod_1745_);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___y_1748_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
v___jp_1764_:
{
lean_object* v___x_1767_; lean_object* v_toEnvExtension_1768_; lean_object* v_env_1769_; lean_object* v_nextMacroScope_1770_; lean_object* v_ngen_1771_; lean_object* v_auxDeclNGen_1772_; lean_object* v_traceState_1773_; lean_object* v_messages_1774_; lean_object* v_infoState_1775_; lean_object* v_snapshotTasks_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1790_; 
v___x_1767_ = lean_st_ref_take(v___y_1766_);
v_toEnvExtension_1768_ = lean_ctor_get(v___x_1761_, 0);
v_env_1769_ = lean_ctor_get(v___x_1767_, 0);
v_nextMacroScope_1770_ = lean_ctor_get(v___x_1767_, 1);
v_ngen_1771_ = lean_ctor_get(v___x_1767_, 2);
v_auxDeclNGen_1772_ = lean_ctor_get(v___x_1767_, 3);
v_traceState_1773_ = lean_ctor_get(v___x_1767_, 4);
v_messages_1774_ = lean_ctor_get(v___x_1767_, 6);
v_infoState_1775_ = lean_ctor_get(v___x_1767_, 7);
v_snapshotTasks_1776_ = lean_ctor_get(v___x_1767_, 8);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v___x_1767_, 5);
lean_dec(v_unused_1791_);
v___x_1778_ = v___x_1767_;
v_isShared_1779_ = v_isSharedCheck_1790_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snapshotTasks_1776_);
lean_inc(v_infoState_1775_);
lean_inc(v_messages_1774_);
lean_inc(v_traceState_1773_);
lean_inc(v_auxDeclNGen_1772_);
lean_inc(v_ngen_1771_);
lean_inc(v_nextMacroScope_1770_);
lean_inc(v_env_1769_);
lean_dec(v___x_1767_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1790_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_asyncMode_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v_asyncMode_1780_ = lean_ctor_get(v_toEnvExtension_1768_, 2);
v___x_1781_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1761_, v_env_1769_, v_entry_1760_, v_asyncMode_1780_, v___x_1763_);
v___x_1782_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 5, v___x_1782_);
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1784_ = v___x_1778_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_nextMacroScope_1770_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_ngen_1771_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_auxDeclNGen_1772_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_traceState_1773_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_messages_1774_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_infoState_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_snapshotTasks_1776_);
v___x_1784_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = lean_st_ref_put(v___y_1766_, v___x_1784_);
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v___y_1765_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object* v_mod_1836_, lean_object* v_isMeta_1837_, lean_object* v_hint_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v_isMeta_boxed_1845_; lean_object* v_res_1846_; 
v_isMeta_boxed_1845_ = lean_unbox(v_isMeta_1837_);
v_res_1846_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_1836_, v_isMeta_boxed_1845_, v_hint_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
if (lean_obj_tag(v_x_1848_) == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
else
{
lean_object* v_key_1850_; lean_object* v_value_1851_; lean_object* v_tail_1852_; uint8_t v___x_1853_; 
v_key_1850_ = lean_ctor_get(v_x_1848_, 0);
v_value_1851_ = lean_ctor_get(v_x_1848_, 1);
v_tail_1852_ = lean_ctor_get(v_x_1848_, 2);
v___x_1853_ = lean_name_eq(v_key_1850_, v_a_1847_);
if (v___x_1853_ == 0)
{
v_x_1848_ = v_tail_1852_;
goto _start;
}
else
{
lean_object* v___x_1855_; 
lean_inc(v_value_1851_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_value_1851_);
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1856_, v_x_1857_);
lean_dec(v_x_1857_);
lean_dec(v_a_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object* v_m_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_buckets_1861_; lean_object* v___x_1862_; uint64_t v___y_1864_; 
v_buckets_1861_ = lean_ctor_get(v_m_1859_, 1);
v___x_1862_ = lean_array_get_size(v_buckets_1861_);
if (lean_obj_tag(v_a_1860_) == 0)
{
uint64_t v___x_1878_; 
v___x_1878_ = 1723ULL;
v___y_1864_ = v___x_1878_;
goto v___jp_1863_;
}
else
{
uint64_t v_hash_1879_; 
v_hash_1879_ = lean_ctor_get_uint64(v_a_1860_, sizeof(void*)*2);
v___y_1864_ = v_hash_1879_;
goto v___jp_1863_;
}
v___jp_1863_:
{
uint64_t v___x_1865_; uint64_t v___x_1866_; uint64_t v_fold_1867_; uint64_t v___x_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1865_ = 32ULL;
v___x_1866_ = lean_uint64_shift_right(v___y_1864_, v___x_1865_);
v_fold_1867_ = lean_uint64_xor(v___y_1864_, v___x_1866_);
v___x_1868_ = 16ULL;
v___x_1869_ = lean_uint64_shift_right(v_fold_1867_, v___x_1868_);
v___x_1870_ = lean_uint64_xor(v_fold_1867_, v___x_1869_);
v___x_1871_ = lean_uint64_to_usize(v___x_1870_);
v___x_1872_ = lean_usize_of_nat(v___x_1862_);
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_sub(v___x_1872_, v___x_1873_);
v___x_1875_ = lean_usize_land(v___x_1871_, v___x_1874_);
v___x_1876_ = lean_array_uget_borrowed(v_buckets_1861_, v___x_1875_);
v___x_1877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1860_, v___x_1876_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object* v_m_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_m_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object* v___x_1883_, lean_object* v_declName_1884_, lean_object* v_as_1885_, size_t v_sz_1886_, size_t v_i_1887_, lean_object* v_b_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_lt(v_i_1887_, v_sz_1886_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_declName_1884_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_b_1888_);
lean_ctor_set(v___x_1896_, 1, v___y_1889_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; lean_object* v_modules_1899_; lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v_toImport_1903_; lean_object* v_module_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1898_ = l_Lean_Environment_header(v___x_1883_);
v_modules_1899_ = lean_ctor_get(v___x_1898_, 3);
lean_inc_ref(v_modules_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1901_ = lean_array_uget_borrowed(v_as_1885_, v_i_1887_);
v___x_1902_ = lean_array_get(v___x_1900_, v_modules_1899_, v_a_1901_);
lean_dec_ref(v_modules_1899_);
v_toImport_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc_ref(v_toImport_1903_);
lean_dec(v___x_1902_);
v_module_1904_ = lean_ctor_get(v_toImport_1903_, 0);
lean_inc(v_module_1904_);
lean_dec_ref(v_toImport_1903_);
v___x_1905_ = 0;
lean_inc(v_declName_1884_);
v___x_1906_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1904_, v___x_1905_, v_declName_1884_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v_snd_1908_; lean_object* v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v_snd_1908_ = lean_ctor_get(v_a_1907_, 1);
lean_inc(v_snd_1908_);
lean_dec(v_a_1907_);
v___x_1909_ = lean_box(0);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1887_, v___x_1910_);
v_i_1887_ = v___x_1911_;
v_b_1888_ = v___x_1909_;
v___y_1889_ = v_snd_1908_;
goto _start;
}
else
{
lean_dec(v_declName_1884_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object* v___x_1913_, lean_object* v_declName_1914_, lean_object* v_as_1915_, lean_object* v_sz_1916_, lean_object* v_i_1917_, lean_object* v_b_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
size_t v_sz_boxed_1925_; size_t v_i_boxed_1926_; lean_object* v_res_1927_; 
v_sz_boxed_1925_ = lean_unbox_usize(v_sz_1916_);
lean_dec(v_sz_1916_);
v_i_boxed_1926_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_1913_, v_declName_1914_, v_as_1915_, v_sz_boxed_1925_, v_i_boxed_1926_, v_b_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec_ref(v_as_1915_);
lean_dec_ref(v___x_1913_);
return v_res_1927_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___x_1931_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0));
v___x_1932_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1931_, v___x_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_declName_1935_, uint8_t v_isMeta_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_env_1948_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___x_1973_; 
v___x_1943_ = lean_st_ref_get(v___y_1941_);
v_env_1948_ = lean_ctor_get(v___x_1943_, 0);
lean_inc_ref(v_env_1948_);
lean_dec(v___x_1943_);
v___x_1973_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1948_, v_declName_1935_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_dec_ref(v_env_1948_);
lean_dec(v_declName_1935_);
goto v___jp_1944_;
}
else
{
lean_object* v_val_1974_; lean_object* v___x_1975_; lean_object* v_modules_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_val_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = l_Lean_Environment_header(v_env_1948_);
v_modules_1976_ = lean_ctor_get(v___x_1975_, 3);
lean_inc_ref(v_modules_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = lean_array_get_size(v_modules_1976_);
v___x_1978_ = lean_nat_dec_lt(v_val_1974_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_dec_ref(v_modules_1976_);
lean_dec(v_val_1974_);
lean_dec_ref(v_env_1948_);
lean_dec(v_declName_1935_);
goto v___jp_1944_;
}
else
{
lean_object* v___x_1979_; lean_object* v_env_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___y_1984_; 
v___x_1979_ = lean_st_ref_get(v___y_1941_);
v_env_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc_ref(v_env_1980_);
lean_dec(v___x_1979_);
v___x_1981_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2);
v___x_1982_ = lean_array_fget(v_modules_1976_, v_val_1974_);
lean_dec(v_val_1974_);
lean_dec_ref(v_modules_1976_);
if (v_isMeta_1936_ == 0)
{
lean_dec_ref(v_env_1980_);
v___y_1984_ = v_isMeta_1936_;
goto v___jp_1983_;
}
else
{
uint8_t v___x_1997_; 
lean_inc(v_declName_1935_);
v___x_1997_ = l_Lean_isMarkedMeta(v_env_1980_, v_declName_1935_);
if (v___x_1997_ == 0)
{
v___y_1984_ = v_isMeta_1936_;
goto v___jp_1983_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = 0;
v___y_1984_ = v___x_1998_;
goto v___jp_1983_;
}
}
v___jp_1983_:
{
lean_object* v_toImport_1985_; lean_object* v_module_1986_; lean_object* v___x_1987_; 
v_toImport_1985_ = lean_ctor_get(v___x_1982_, 0);
lean_inc_ref(v_toImport_1985_);
lean_dec(v___x_1982_);
v_module_1986_ = lean_ctor_get(v_toImport_1985_, 0);
lean_inc(v_module_1986_);
lean_dec_ref(v_toImport_1985_);
lean_inc(v_declName_1935_);
v___x_1987_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1986_, v___y_1984_, v_declName_1935_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_snd_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v_snd_1989_ = lean_ctor_get(v_a_1988_, 1);
lean_inc(v_snd_1989_);
lean_dec(v_a_1988_);
v___x_1990_ = l_Lean_indirectModUseExt;
v___x_1991_ = lean_box(1);
v___x_1992_ = lean_box(0);
lean_inc_ref(v_env_1948_);
v___x_1993_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1981_, v___x_1990_, v_env_1948_, v___x_1991_, v___x_1992_);
v___x_1994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_1993_, v_declName_1935_);
lean_dec(v___x_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3));
v___y_1950_ = v_snd_1989_;
v___y_1951_ = v___x_1995_;
goto v___jp_1949_;
}
else
{
lean_object* v_val_1996_; 
v_val_1996_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v___x_1994_, 1);
v___y_1950_ = v_snd_1989_;
v___y_1951_ = v_val_1996_;
goto v___jp_1949_;
}
}
else
{
lean_dec_ref(v_env_1948_);
lean_dec(v_declName_1935_);
return v___x_1987_;
}
}
}
}
v___jp_1944_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___y_1937_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
return v___x_1947_;
}
v___jp_1949_:
{
lean_object* v___x_1952_; size_t v_sz_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = lean_box(0);
v_sz_1953_ = lean_array_size(v___y_1951_);
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_1948_, v_declName_1935_, v___y_1951_, v_sz_1953_, v___x_1954_, v___x_1952_, v___y_1950_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v_env_1948_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1972_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1972_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1972_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1970_; 
v_snd_1960_ = lean_ctor_get(v_a_1956_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_a_1956_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v_a_1956_, 0);
lean_dec(v_unused_1971_);
v___x_1962_ = v_a_1956_;
v_isShared_1963_ = v_isSharedCheck_1970_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_dec(v_a_1956_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1970_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1952_);
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_snd_1960_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1965_);
v___x_1967_ = v___x_1958_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
else
{
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_declName_1999_, lean_object* v_isMeta_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v_isMeta_boxed_2007_; lean_object* v_res_2008_; 
v_isMeta_boxed_2007_ = lean_unbox(v_isMeta_2000_);
v_res_2008_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_1999_, v_isMeta_boxed_2007_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2009_, lean_object* v_vals_2010_, lean_object* v_i_2011_, lean_object* v_k_2012_){
_start:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = lean_array_get_size(v_keys_2009_);
v___x_2014_ = lean_nat_dec_lt(v_i_2011_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec(v_i_2011_);
v___x_2015_ = lean_box(0);
return v___x_2015_;
}
else
{
lean_object* v_k_x27_2016_; uint8_t v___x_2017_; 
v_k_x27_2016_ = lean_array_fget_borrowed(v_keys_2009_, v_i_2011_);
v___x_2017_ = lean_name_eq(v_k_2012_, v_k_x27_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_add(v_i_2011_, v___x_2018_);
lean_dec(v_i_2011_);
v_i_2011_ = v___x_2019_;
goto _start;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_array_fget_borrowed(v_vals_2010_, v_i_2011_);
lean_dec(v_i_2011_);
lean_inc(v___x_2021_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2023_, lean_object* v_vals_2024_, lean_object* v_i_2025_, lean_object* v_k_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2023_, v_vals_2024_, v_i_2025_, v_k_2026_);
lean_dec(v_k_2026_);
lean_dec_ref(v_vals_2024_);
lean_dec_ref(v_keys_2023_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_2028_, size_t v_x_2029_, lean_object* v_x_2030_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
lean_object* v_es_2031_; lean_object* v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v_j_2035_; lean_object* v___x_2036_; 
v_es_2031_ = lean_ctor_get(v_x_2028_, 0);
v___x_2032_ = lean_box(2);
v___x_2033_ = ((size_t)31ULL);
v___x_2034_ = lean_usize_land(v_x_2029_, v___x_2033_);
v_j_2035_ = lean_usize_to_nat(v___x_2034_);
v___x_2036_ = lean_array_get_borrowed(v___x_2032_, v_es_2031_, v_j_2035_);
lean_dec(v_j_2035_);
switch(lean_obj_tag(v___x_2036_))
{
case 0:
{
lean_object* v_key_2037_; lean_object* v_val_2038_; uint8_t v___x_2039_; 
v_key_2037_ = lean_ctor_get(v___x_2036_, 0);
v_val_2038_ = lean_ctor_get(v___x_2036_, 1);
v___x_2039_ = lean_name_eq(v_x_2030_, v_key_2037_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_box(0);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; 
lean_inc(v_val_2038_);
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_val_2038_);
return v___x_2041_;
}
}
case 1:
{
lean_object* v_node_2042_; size_t v___x_2043_; size_t v___x_2044_; 
v_node_2042_ = lean_ctor_get(v___x_2036_, 0);
v___x_2043_ = ((size_t)5ULL);
v___x_2044_ = lean_usize_shift_right(v_x_2029_, v___x_2043_);
v_x_2028_ = v_node_2042_;
v_x_2029_ = v___x_2044_;
goto _start;
}
default: 
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_box(0);
return v___x_2046_;
}
}
}
else
{
lean_object* v_ks_2047_; lean_object* v_vs_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_ks_2047_ = lean_ctor_get(v_x_2028_, 0);
v_vs_2048_ = lean_ctor_get(v_x_2028_, 1);
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_2047_, v_vs_2048_, v___x_2049_, v_x_2030_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
size_t v_x_27093__boxed_2054_; lean_object* v_res_2055_; 
v_x_27093__boxed_2054_ = lean_unbox_usize(v_x_2052_);
lean_dec(v_x_2052_);
v_res_2055_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2051_, v_x_27093__boxed_2054_, v_x_2053_);
lean_dec(v_x_2053_);
lean_dec_ref(v_x_2051_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
uint64_t v___y_2059_; 
if (lean_obj_tag(v_x_2057_) == 0)
{
uint64_t v___x_2062_; 
v___x_2062_ = 1723ULL;
v___y_2059_ = v___x_2062_;
goto v___jp_2058_;
}
else
{
uint64_t v_hash_2063_; 
v_hash_2063_ = lean_ctor_get_uint64(v_x_2057_, sizeof(void*)*2);
v___y_2059_ = v_hash_2063_;
goto v___jp_2058_;
}
v___jp_2058_:
{
size_t v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_uint64_to_usize(v___y_2059_);
v___x_2061_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2056_, v___x_2060_, v_x_2057_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2064_, v_x_2065_);
lean_dec(v_x_2065_);
lean_dec_ref(v_x_2064_);
return v_res_2066_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___x_2068_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0));
v___x_2069_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2068_, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_2072_ = l_Lean_stringToMessageData(v___x_2071_);
return v___x_2072_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2075_ = l_Lean_stringToMessageData(v___x_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2082_, lean_object* v_init_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
if (lean_obj_tag(v_x_2084_) == 0)
{
lean_object* v_k_2091_; lean_object* v_l_2092_; lean_object* v_r_2093_; lean_object* v___x_2094_; 
v_k_2091_ = lean_ctor_get(v_x_2084_, 1);
lean_inc(v_k_2091_);
v_l_2092_ = lean_ctor_get(v_x_2084_, 3);
lean_inc(v_l_2092_);
v_r_2093_ = lean_ctor_get(v_x_2084_, 4);
lean_inc(v_r_2093_);
lean_dec_ref_known(v_x_2084_, 5);
lean_inc_ref(v_origDecl_2082_);
v___x_2094_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2082_, v_init_2083_, v_l_2092_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_snd_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2219_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v_snd_2096_ = lean_ctor_get(v_a_2095_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_a_2095_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v_a_2095_, 0);
lean_dec(v_unused_2220_);
v___x_2098_ = v_a_2095_;
v_isShared_2099_ = v_isSharedCheck_2219_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_snd_2096_);
lean_dec(v_a_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2219_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_box(0);
v___x_2101_ = l_Lean_NameSet_contains(v_snd_2096_, v_k_2091_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v_env_2103_; lean_object* v___x_2104_; lean_object* v_toEnvExtension_2105_; lean_object* v_asyncMode_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2102_ = lean_st_ref_get(v___y_2089_);
v_env_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc_ref(v_env_2103_);
lean_dec(v___x_2102_);
v___x_2104_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2105_ = lean_ctor_get(v___x_2104_, 0);
v_asyncMode_2106_ = lean_ctor_get(v_toEnvExtension_2105_, 2);
v___x_2107_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
lean_inc(v_k_2091_);
v___x_2108_ = l_Lean_NameSet_insert(v_snd_2096_, v_k_2091_);
v___x_2109_ = lean_box(0);
v___x_2110_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2107_, v___x_2104_, v_env_2103_, v_asyncMode_2106_, v___x_2109_);
v___x_2111_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2110_, v_k_2091_);
lean_dec(v___x_2110_);
if (lean_obj_tag(v___x_2111_) == 1)
{
lean_object* v_val_2112_; lean_object* v___x_2113_; 
lean_del_object(v___x_2098_);
lean_dec(v_k_2091_);
v_val_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_n(v_val_2112_, 2);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2112_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; uint8_t v___y_2116_; lean_object* v_toSignature_2130_; lean_object* v_name_2131_; uint8_t v___x_2132_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v_toSignature_2130_ = lean_ctor_get(v_val_2112_, 0);
v_name_2131_ = lean_ctor_get(v_toSignature_2130_, 0);
v___x_2132_ = l_Lean_isPrivateName(v_name_2131_);
if (v___x_2132_ == 0)
{
lean_dec(v_a_2114_);
v___y_2116_ = v___x_2101_;
goto v___jp_2115_;
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_unbox(v_a_2114_);
lean_dec(v_a_2114_);
v___y_2116_ = v___x_2133_;
goto v___jp_2115_;
}
v___jp_2115_:
{
if (v___y_2116_ == 0)
{
lean_dec(v_val_2112_);
v_init_2083_ = v___x_2100_;
v_x_2084_ = v_r_2093_;
v___y_2085_ = v___x_2108_;
goto _start;
}
else
{
lean_object* v___x_2118_; 
lean_inc_ref(v_origDecl_2082_);
v___x_2118_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2082_, v_val_2112_, v___x_2108_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_snd_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v_snd_2120_ = lean_ctor_get(v_a_2119_, 1);
lean_inc(v_snd_2120_);
lean_dec(v_a_2119_);
v_init_2083_ = v___x_2100_;
v_x_2084_ = v_r_2093_;
v___y_2085_ = v_snd_2120_;
goto _start;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_r_2093_);
lean_dec_ref(v_origDecl_2082_);
v_a_2122_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2118_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2118_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_val_2112_);
lean_dec(v___x_2108_);
lean_dec(v_r_2093_);
lean_dec_ref(v_origDecl_2082_);
v_a_2134_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2113_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2113_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v_env_2143_; lean_object* v___x_2144_; 
lean_dec(v___x_2111_);
v___x_2142_ = lean_st_ref_get(v___y_2089_);
v_env_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc_ref(v_env_2143_);
lean_dec(v___x_2142_);
v___x_2144_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2143_, v_k_2091_);
lean_dec_ref(v_env_2143_);
if (lean_obj_tag(v___x_2144_) == 1)
{
lean_object* v_val_2145_; lean_object* v___x_2146_; lean_object* v_env_2147_; lean_object* v___x_2148_; lean_object* v_modules_2149_; uint8_t v___x_2190_; uint8_t v___y_2192_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_val_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_st_ref_get(v___y_2089_);
v_env_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_ref(v_env_2147_);
lean_dec(v___x_2146_);
v___x_2148_ = l_Lean_Environment_header(v_env_2147_);
lean_dec_ref(v_env_2147_);
v_modules_2149_ = lean_ctor_get(v___x_2148_, 3);
lean_inc_ref(v_modules_2149_);
lean_dec_ref(v___x_2148_);
v___x_2190_ = 1;
v___x_2212_ = lean_array_get_size(v_modules_2149_);
v___x_2213_ = lean_nat_dec_lt(v_val_2145_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_dec_ref(v_modules_2149_);
v___y_2192_ = v___x_2101_;
goto v___jp_2191_;
}
else
{
lean_object* v___x_2214_; lean_object* v_toImport_2215_; uint8_t v_isExported_2216_; 
v___x_2214_ = lean_array_fget(v_modules_2149_, v_val_2145_);
lean_dec_ref(v_modules_2149_);
v_toImport_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc_ref(v_toImport_2215_);
lean_dec(v___x_2214_);
v_isExported_2216_ = lean_ctor_get_uint8(v_toImport_2215_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2215_);
if (v_isExported_2216_ == 0)
{
goto v___jp_2182_;
}
else
{
v___y_2192_ = v___x_2101_;
goto v___jp_2191_;
}
}
v___jp_2150_:
{
lean_object* v___x_2151_; lean_object* v_toSignature_2152_; lean_object* v_env_2153_; lean_object* v_name_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2151_ = lean_st_ref_get(v___y_2089_);
v_toSignature_2152_ = lean_ctor_get(v_origDecl_2082_, 0);
lean_inc_ref(v_toSignature_2152_);
lean_dec_ref(v_origDecl_2082_);
v_env_2153_ = lean_ctor_get(v___x_2151_, 0);
lean_inc_ref(v_env_2153_);
lean_dec(v___x_2151_);
v_name_2154_ = lean_ctor_get(v_toSignature_2152_, 0);
lean_inc(v_name_2154_);
lean_dec_ref(v_toSignature_2152_);
v___x_2155_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
v___x_2156_ = l_Lean_MessageData_ofConstName(v_name_2154_, v___x_2101_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 7);
lean_ctor_set(v___x_2098_, 1, v___x_2156_);
lean_ctor_set(v___x_2098_, 0, v___x_2155_);
v___x_2158_ = v___x_2098_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v___x_2159_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = l_Lean_MessageData_ofConstName(v_k_2091_, v___x_2101_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_Environment_header(v_env_2153_);
lean_dec_ref(v_env_2153_);
v___x_2166_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2165_);
v___x_2167_ = lean_array_get(v___x_2109_, v___x_2166_, v_val_2145_);
lean_dec(v_val_2145_);
lean_dec_ref(v___x_2166_);
v___x_2168_ = l_Lean_MessageData_ofName(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2164_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2171_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
v___jp_2182_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_a_2185_; lean_object* v_fst_2186_; uint8_t v___x_2187_; 
v___x_2183_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2184_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v___x_2183_, v___x_2108_, v___y_2088_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2184_);
v_fst_2186_ = lean_ctor_get(v_a_2185_, 0);
v___x_2187_ = lean_unbox(v_fst_2186_);
if (v___x_2187_ == 0)
{
lean_dec(v_a_2185_);
lean_dec(v_r_2093_);
goto v___jp_2150_;
}
else
{
if (v___x_2101_ == 0)
{
lean_object* v_snd_2188_; 
lean_dec(v_val_2145_);
lean_del_object(v___x_2098_);
lean_dec(v_k_2091_);
v_snd_2188_ = lean_ctor_get(v_a_2185_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_a_2185_);
v_init_2083_ = v___x_2100_;
v_x_2084_ = v_r_2093_;
v___y_2085_ = v_snd_2188_;
goto _start;
}
else
{
lean_dec(v_a_2185_);
lean_dec(v_r_2093_);
goto v___jp_2150_;
}
}
}
v___jp_2191_:
{
if (v___y_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v_env_2194_; uint8_t v___x_2195_; uint8_t v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v_val_2145_);
lean_del_object(v___x_2098_);
v___x_2193_ = lean_st_ref_get(v___y_2089_);
v_env_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_ref(v_env_2194_);
lean_dec(v___x_2193_);
lean_inc(v_k_2091_);
v___x_2195_ = l_Lean_getIRPhases(v_env_2194_, v_k_2091_);
v___x_2196_ = 1;
v___x_2197_ = l_Lean_instBEqIRPhases_beq(v___x_2195_, v___x_2196_);
v___x_2198_ = lean_box(v___x_2197_);
v___x_2199_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed), 8, 2);
lean_closure_set(v___x_2199_, 0, v_k_2091_);
lean_closure_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2199_, v___x_2190_, v___x_2108_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v_snd_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v_snd_2202_ = lean_ctor_get(v_a_2201_, 1);
lean_inc(v_snd_2202_);
lean_dec(v_a_2201_);
v_init_2083_ = v___x_2100_;
v_x_2084_ = v_r_2093_;
v___y_2085_ = v_snd_2202_;
goto _start;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_r_2093_);
lean_dec_ref(v_origDecl_2082_);
v_a_2204_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2200_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2200_);
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
else
{
goto v___jp_2182_;
}
}
}
else
{
lean_dec(v___x_2144_);
lean_del_object(v___x_2098_);
lean_dec(v_k_2091_);
v_init_2083_ = v___x_2100_;
v_x_2084_ = v_r_2093_;
v___y_2085_ = v___x_2108_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2098_);
lean_dec(v_k_2091_);
v_init_2083_ = v___x_2100_;
v_x_2084_ = v_r_2093_;
v___y_2085_ = v_snd_2096_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2093_);
lean_dec(v_k_2091_);
lean_dec_ref(v_origDecl_2082_);
return v___x_2094_;
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v_origDecl_2082_);
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_init_2083_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___y_2085_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2224_, lean_object* v_origDecl_2225_, lean_object* v_code_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = l_Lean_NameSet_empty;
v___x_2234_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2224_, v_code_2226_, v___x_2233_);
v___x_2235_ = lean_box(0);
v___x_2236_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2225_, v___x_2235_, v___x_2234_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2253_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2253_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2253_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2251_; 
v_snd_2241_ = lean_ctor_get(v_a_2237_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_a_2237_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; 
v_unused_2252_ = lean_ctor_get(v_a_2237_, 0);
lean_dec(v_unused_2252_);
v___x_2243_ = v_a_2237_;
v_isShared_2244_ = v_isSharedCheck_2251_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_dec(v_a_2237_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2251_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2235_);
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_snd_2241_);
v___x_2246_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2246_);
v___x_2248_ = v___x_2239_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_a_2254_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2236_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2236_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2262_, lean_object* v_origDecl_2263_, lean_object* v_code_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v___x_27177__boxed_2271_; lean_object* v_res_2272_; 
v___x_27177__boxed_2271_ = lean_unbox(v___x_2262_);
v_res_2272_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_27177__boxed_2271_, v_origDecl_2263_, v_code_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2273_, lean_object* v_decl_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_value_2281_; uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; 
v_value_2281_ = lean_ctor_get(v_decl_2274_, 1);
lean_inc_ref(v_value_2281_);
lean_dec_ref(v_decl_2274_);
v___x_2282_ = 0;
v___x_2283_ = lean_box(v___x_2282_);
v___f_2284_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2284_, 0, v___x_2283_);
lean_closure_set(v___f_2284_, 1, v_origDecl_2273_);
v___x_2285_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2284_, v_value_2281_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2286_, lean_object* v_decl_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2286_, v_decl_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2295_, lean_object* v_init_2296_, lean_object* v_x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2295_, v_init_2296_, v_x_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2306_, v_x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2309_, v_x_2310_, v_x_2311_);
lean_dec(v_x_2311_);
lean_dec_ref(v_x_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_opt_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_2313_, v___y_2314_, v___y_2317_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_opt_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v_opt_2321_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2329_, lean_object* v_x_2330_, size_t v_x_2331_, lean_object* v_x_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2330_, v_x_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
size_t v_x_27594__boxed_2338_; lean_object* v_res_2339_; 
v_x_27594__boxed_2338_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_res_2339_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2334_, v_x_2335_, v_x_27594__boxed_2338_, v_x_2337_);
lean_dec(v_x_2337_);
lean_dec_ref(v_x_2335_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(lean_object* v_00_u03b2_2340_, lean_object* v_m_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_2341_, v_a_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_m_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_2344_, v_m_2345_, v_a_2346_);
lean_dec(v_a_2346_);
lean_dec_ref(v_m_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2348_, lean_object* v_keys_2349_, lean_object* v_vals_2350_, lean_object* v_heq_2351_, lean_object* v_i_2352_, lean_object* v_k_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2349_, v_vals_2350_, v_i_2352_, v_k_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2355_, lean_object* v_keys_2356_, lean_object* v_vals_2357_, lean_object* v_heq_2358_, lean_object* v_i_2359_, lean_object* v_k_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2355_, v_keys_2356_, v_vals_2357_, v_heq_2358_, v_i_2359_, v_k_2360_);
lean_dec(v_k_2360_);
lean_dec_ref(v_vals_2357_);
lean_dec_ref(v_keys_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_2363_, v_x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_2366_, v_x_2367_, v_x_2368_);
lean_dec_ref(v_x_2368_);
lean_dec_ref(v_x_2367_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_2371_, lean_object* v_a_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_2372_, v_x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2375_, lean_object* v_a_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_2375_, v_a_2376_, v_x_2377_);
lean_dec(v_x_2377_);
lean_dec(v_a_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2379_, lean_object* v_x_2380_, size_t v_x_2381_, lean_object* v_x_2382_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_2380_, v_x_2381_, v_x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
size_t v_x_27622__boxed_2388_; uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_x_27622__boxed_2388_ = lean_unbox_usize(v_x_2386_);
lean_dec(v_x_2386_);
v_res_2389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_2384_, v_x_2385_, v_x_27622__boxed_2388_, v_x_2387_);
lean_dec_ref(v_x_2387_);
lean_dec_ref(v_x_2385_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_2391_, lean_object* v_keys_2392_, lean_object* v_vals_2393_, lean_object* v_heq_2394_, lean_object* v_i_2395_, lean_object* v_k_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_2392_, v_i_2395_, v_k_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_keys_2399_, lean_object* v_vals_2400_, lean_object* v_heq_2401_, lean_object* v_i_2402_, lean_object* v_k_2403_){
_start:
{
uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_res_2404_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_2398_, v_keys_2399_, v_vals_2400_, v_heq_2401_, v_i_2402_, v_k_2403_);
lean_dec_ref(v_k_2403_);
lean_dec_ref(v_vals_2400_);
lean_dec_ref(v_keys_2399_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2406_, size_t v_sz_2407_, size_t v_i_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_a_2416_; uint8_t v___x_2420_; 
v___x_2420_ = lean_usize_dec_lt(v_i_2408_, v_sz_2407_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_b_2409_);
return v___x_2421_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_array_uget_borrowed(v_as_2406_, v_i_2408_);
lean_inc(v_a_2422_);
v___x_2423_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2422_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_toSignature_2424_; lean_object* v_a_2425_; lean_object* v_name_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_toSignature_2424_ = lean_ctor_get(v_a_2422_, 0);
v_a_2425_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2423_, 1);
v_name_2426_ = lean_ctor_get(v_toSignature_2424_, 0);
v___x_2427_ = lean_box(0);
v___x_2428_ = l_Lean_isPrivateName(v_name_2426_);
if (v___x_2428_ == 0)
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_unbox(v_a_2425_);
lean_dec(v_a_2425_);
if (v___x_2429_ == 0)
{
v_a_2416_ = v___x_2427_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_st_ref_get(v___y_2413_);
lean_dec(v___x_2430_);
v___x_2431_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2422_, 2);
v___x_2432_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2422_, v_a_2422_, v___x_2431_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_dec_ref_known(v___x_2432_, 1);
v_a_2416_ = v___x_2427_;
goto v___jp_2415_;
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
else
{
lean_dec(v_a_2425_);
v_a_2416_ = v___x_2427_;
goto v___jp_2415_;
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
v_a_2441_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2423_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2423_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
v___jp_2415_:
{
size_t v___x_2417_; size_t v___x_2418_; 
v___x_2417_ = ((size_t)1ULL);
v___x_2418_ = lean_usize_add(v_i_2408_, v___x_2417_);
v_i_2408_ = v___x_2418_;
v_b_2409_ = v_a_2416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2449_, lean_object* v_sz_2450_, lean_object* v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2450_);
lean_dec(v_sz_2450_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2449_, v_sz_boxed_2458_, v_i_boxed_2459_, v_b_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v_as_2449_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; lean_object* v_env_2468_; lean_object* v___x_2469_; uint8_t v_isModule_2470_; 
v___x_2467_ = lean_st_ref_get(v___y_2465_);
v_env_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_env_2468_);
lean_dec(v___x_2467_);
v___x_2469_ = l_Lean_Environment_header(v_env_2468_);
lean_dec_ref(v_env_2468_);
v_isModule_2470_ = lean_ctor_get_uint8(v___x_2469_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2469_);
if (v_isModule_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_decls_2461_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; size_t v_sz_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v___x_2472_ = lean_box(0);
v_sz_2473_ = lean_array_size(v_decls_2461_);
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2461_, v_sz_2473_, v___x_2474_, v___x_2472_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2482_ == 0)
{
lean_object* v_unused_2483_; 
v_unused_2483_ = lean_ctor_get(v___x_2475_, 0);
lean_dec(v_unused_2483_);
v___x_2477_ = v___x_2475_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_dec(v___x_2475_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v_decls_2461_);
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_decls_2461_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v_decls_2461_);
v_a_2484_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2475_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2475_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2498_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2513_, uint8_t v___x_2514_, lean_object* v_as_2515_, size_t v_sz_2516_, size_t v_i_2517_, lean_object* v_b_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_a_2525_; uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_lt(v_i_2517_, v_sz_2516_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_b_2518_);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v_env_2532_; lean_object* v_a_2533_; lean_object* v_toSignature_2534_; lean_object* v_name_2535_; lean_object* v___x_2536_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2531_ = lean_st_ref_get(v___y_2522_);
v_env_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc_ref(v_env_2532_);
lean_dec(v___x_2531_);
v_a_2533_ = lean_array_uget_borrowed(v_as_2515_, v_i_2517_);
v_toSignature_2534_ = lean_ctor_get(v_a_2533_, 0);
v_name_2535_ = lean_ctor_get(v_toSignature_2534_, 0);
v___x_2536_ = lean_box(0);
v___x_2544_ = l_Lean_Environment_setExporting(v_env_2532_, v___x_2514_);
lean_inc(v_name_2535_);
v___x_2545_ = l_Lean_Environment_contains(v___x_2544_, v_name_2535_, v___x_2514_);
if (v___x_2545_ == 0)
{
v_a_2525_ = v___x_2536_;
goto v___jp_2524_;
}
else
{
lean_object* v_toCold_2546_; lean_object* v_options_2547_; uint8_t v_hasTrace_2548_; 
v_toCold_2546_ = lean_ctor_get(v___y_2521_, 0);
v_options_2547_ = lean_ctor_get(v_toCold_2546_, 2);
v_hasTrace_2548_ = lean_ctor_get_uint8(v_options_2547_, sizeof(void*)*1);
if (v_hasTrace_2548_ == 0)
{
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
goto v___jp_2537_;
}
else
{
lean_object* v_inheritedTraceOptions_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v_inheritedTraceOptions_2549_ = lean_ctor_get(v_toCold_2546_, 11);
v___x_2550_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2551_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2549_, v_options_2547_, v___x_2551_);
if (v___x_2552_ == 0)
{
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2553_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2535_);
v___x_2554_ = l_Lean_MessageData_ofName(v_name_2535_);
v___x_2555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2550_, v___x_2557_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
goto v___jp_2537_;
}
else
{
return v___x_2558_;
}
}
}
}
v___jp_2537_:
{
uint8_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2513_);
lean_inc(v_a_2533_);
v___x_2543_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2542_, v_phase_2513_, v_a_2533_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_dec_ref_known(v___x_2543_, 1);
v_a_2525_ = v___x_2536_;
goto v___jp_2524_;
}
else
{
return v___x_2543_;
}
}
}
v___jp_2524_:
{
size_t v___x_2526_; size_t v___x_2527_; 
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2517_, v___x_2526_);
v_i_2517_ = v___x_2527_;
v_b_2518_ = v_a_2525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2559_, lean_object* v___x_2560_, lean_object* v_as_2561_, lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v_phase_boxed_2570_; uint8_t v___x_2240__boxed_2571_; size_t v_sz_boxed_2572_; size_t v_i_boxed_2573_; lean_object* v_res_2574_; 
v_phase_boxed_2570_ = lean_unbox(v_phase_2559_);
v___x_2240__boxed_2571_ = lean_unbox(v___x_2560_);
v_sz_boxed_2572_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2573_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2570_, v___x_2240__boxed_2571_, v_as_2561_, v_sz_boxed_2572_, v_i_boxed_2573_, v_b_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v_as_2561_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2575_, lean_object* v_decls_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; lean_object* v_env_2583_; lean_object* v___x_2584_; uint8_t v_isModule_2585_; 
v___x_2582_ = lean_st_ref_get(v___y_2580_);
v_env_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc_ref(v_env_2583_);
lean_dec(v___x_2582_);
v___x_2584_ = l_Lean_Environment_header(v_env_2583_);
lean_dec_ref(v_env_2583_);
v_isModule_2585_ = lean_ctor_get_uint8(v___x_2584_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2584_);
if (v_isModule_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_decls_2576_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; size_t v_sz_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v___x_2587_ = lean_box(0);
v_sz_2588_ = lean_array_size(v_decls_2576_);
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2575_, v_isModule_2585_, v_decls_2576_, v_sz_2588_, v___x_2589_, v___x_2587_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2598_);
v___x_2592_ = v___x_2590_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_dec(v___x_2590_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v_decls_2576_);
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_decls_2576_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_decls_2576_);
v_a_2599_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2590_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2590_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2607_, lean_object* v_decls_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v_phase_boxed_2614_; lean_object* v_res_2615_; 
v_phase_boxed_2614_ = lean_unbox(v_phase_2607_);
v_res_2615_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2614_, v_decls_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2618_){
_start:
{
lean_object* v___x_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2619_ = lean_box(v_phase_2618_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2620_, 0, v___x_2619_);
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = 0;
v___x_2623_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2624_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2624_, 0, v___x_2621_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_ctor_set(v___x_2624_, 2, v___f_2620_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*3, v_phase_2618_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*3 + 1, v_phase_2618_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*3 + 2, v___x_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2625_){
_start:
{
uint8_t v_phase_boxed_2626_; lean_object* v_res_2627_; 
v_phase_boxed_2626_ = lean_unbox(v_phase_2625_);
v_res_2627_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2626_);
return v_res_2627_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_unsigned_to_nat(3356661454u);
v___x_2680_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2681_ = l_Lean_Name_num___override(v___x_2680_, v___x_2679_);
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2684_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2685_ = l_Lean_Name_str___override(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2688_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2689_ = l_Lean_Name_str___override(v___x_2688_, v___x_2687_);
return v___x_2689_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = lean_unsigned_to_nat(2u);
v___x_2691_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2692_ = l_Lean_Name_num___override(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2695_ = 0;
v___x_2696_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2697_ = l_Lean_registerTraceClass(v___x_2694_, v___x_2695_, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2699_;
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
