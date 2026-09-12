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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
extern lean_object* l_Lean_Compiler_LCNF_baseExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
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
uint8_t v_a_954__boxed_184_; uint8_t v_pu_boxed_185_; lean_object* v_res_186_; 
v_a_954__boxed_184_ = lean_unbox(v_a_176_);
v_pu_boxed_185_ = lean_unbox(v_pu_177_);
v_res_186_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(v_toSignature_175_, v_a_954__boxed_184_, v_pu_boxed_185_, v_code_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
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
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v_toCold_229_; lean_object* v_ref_230_; lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_toCold_229_ = lean_ctor_get(v___y_226_, 0);
v_ref_230_ = lean_ctor_get(v___y_226_, 2);
v___x_231_ = lean_st_ref_get(v___y_227_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v___x_233_ = lean_st_ref_get(v___y_225_);
v___x_234_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_224_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_293_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_293_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_293_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_293_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_lctx_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_291_; 
v_lctx_239_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_233_, 1);
lean_dec(v_unused_292_);
v___x_241_ = v___x_233_;
v_isShared_242_ = v_isSharedCheck_291_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_lctx_239_);
lean_dec(v___x_233_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_291_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_options_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v_options_243_ = lean_ctor_get(v_toCold_229_, 2);
v___x_244_ = lean_unbox(v_a_235_);
lean_dec(v_a_235_);
v___x_245_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_239_, v___x_244_);
lean_dec_ref(v_lctx_239_);
v___x_246_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
lean_inc_ref(v_options_243_);
v___x_247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_247_, 0, v_env_232_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
lean_ctor_set(v___x_247_, 2, v___x_245_);
lean_ctor_set(v___x_247_, 3, v_options_243_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 1, v_msg_223_);
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_249_ = v___x_241_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_msg_223_);
v___x_249_ = v_reuseFailAlloc_290_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v_traceState_251_; lean_object* v_env_252_; lean_object* v_nextMacroScope_253_; lean_object* v_ngen_254_; lean_object* v_auxDeclNGen_255_; lean_object* v_cache_256_; lean_object* v_messages_257_; lean_object* v_infoState_258_; lean_object* v_snapshotTasks_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_289_; 
v___x_250_ = lean_st_ref_take(v___y_227_);
v_traceState_251_ = lean_ctor_get(v___x_250_, 4);
v_env_252_ = lean_ctor_get(v___x_250_, 0);
v_nextMacroScope_253_ = lean_ctor_get(v___x_250_, 1);
v_ngen_254_ = lean_ctor_get(v___x_250_, 2);
v_auxDeclNGen_255_ = lean_ctor_get(v___x_250_, 3);
v_cache_256_ = lean_ctor_get(v___x_250_, 5);
v_messages_257_ = lean_ctor_get(v___x_250_, 6);
v_infoState_258_ = lean_ctor_get(v___x_250_, 7);
v_snapshotTasks_259_ = lean_ctor_get(v___x_250_, 8);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_289_ == 0)
{
v___x_261_ = v___x_250_;
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snapshotTasks_259_);
lean_inc(v_infoState_258_);
lean_inc(v_messages_257_);
lean_inc(v_cache_256_);
lean_inc(v_traceState_251_);
lean_inc(v_auxDeclNGen_255_);
lean_inc(v_ngen_254_);
lean_inc(v_nextMacroScope_253_);
lean_inc(v_env_252_);
lean_dec(v___x_250_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint64_t v_tid_263_; lean_object* v_traces_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_288_; 
v_tid_263_ = lean_ctor_get_uint64(v_traceState_251_, sizeof(void*)*1);
v_traces_264_ = lean_ctor_get(v_traceState_251_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_traceState_251_);
if (v_isSharedCheck_288_ == 0)
{
v___x_266_ = v_traceState_251_;
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_traces_264_);
lean_dec(v_traceState_251_);
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
lean_ctor_set(v___x_275_, 1, v___x_249_);
lean_ctor_set(v___x_275_, 2, v___x_274_);
lean_inc(v_ref_230_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_ref_230_);
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
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_env_252_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_nextMacroScope_253_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_ngen_254_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_auxDeclNGen_255_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_286_, 5, v_cache_256_);
lean_ctor_set(v_reuseFailAlloc_286_, 6, v_messages_257_);
lean_ctor_set(v_reuseFailAlloc_286_, 7, v_infoState_258_);
lean_ctor_set(v_reuseFailAlloc_286_, 8, v_snapshotTasks_259_);
v___x_281_ = v_reuseFailAlloc_286_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_st_ref_put(v___y_227_, v___x_281_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_268_);
v___x_284_ = v___x_237_;
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
lean_dec(v___x_233_);
lean_dec_ref(v_env_232_);
lean_dec_ref(v_msg_223_);
lean_dec(v_cls_222_);
v_a_294_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_234_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_234_);
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
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___f_398_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___x_406_; lean_object* v_toSignature_407_; lean_object* v_env_408_; lean_object* v_nextMacroScope_409_; lean_object* v_ngen_410_; lean_object* v_auxDeclNGen_411_; lean_object* v_traceState_412_; lean_object* v_messages_413_; lean_object* v_infoState_414_; lean_object* v_snapshotTasks_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_485_; 
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
v_messages_413_ = lean_ctor_get(v___x_406_, 6);
v_infoState_414_ = lean_ctor_get(v___x_406_, 7);
v_snapshotTasks_415_ = lean_ctor_get(v___x_406_, 8);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v___x_406_, 5);
lean_dec(v_unused_486_);
v___x_417_ = v___x_406_;
v_isShared_418_ = v_isSharedCheck_485_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snapshotTasks_415_);
lean_inc(v_infoState_414_);
lean_inc(v_messages_413_);
lean_inc(v_traceState_412_);
lean_inc(v_auxDeclNGen_411_);
lean_inc(v_ngen_410_);
lean_inc(v_nextMacroScope_409_);
lean_inc(v_env_408_);
lean_dec(v___x_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_485_;
goto v_resetjp_416_;
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
v_resetjp_416_:
{
lean_object* v_name_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___x_447_; 
v_name_419_ = lean_ctor_get(v_toSignature_407_, 0);
lean_inc(v_name_419_);
v___x_420_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_408_, v_name_419_);
v___x_421_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 5, v___x_421_);
lean_ctor_set(v___x_417_, 0, v___x_420_);
v___x_447_ = v___x_417_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_nextMacroScope_409_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_ngen_410_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_auxDeclNGen_411_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_traceState_412_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_484_, 6, v_messages_413_);
lean_ctor_set(v_reuseFailAlloc_484_, 7, v_infoState_414_);
lean_ctor_set(v_reuseFailAlloc_484_, 8, v_snapshotTasks_415_);
v___x_447_ = v_reuseFailAlloc_484_;
goto v_reusejp_446_;
}
v___jp_422_:
{
lean_object* v___x_427_; lean_object* v_env_428_; lean_object* v_nextMacroScope_429_; lean_object* v_ngen_430_; lean_object* v_auxDeclNGen_431_; lean_object* v_traceState_432_; lean_object* v_messages_433_; lean_object* v_infoState_434_; lean_object* v_snapshotTasks_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_444_; 
v___x_427_ = lean_st_ref_take(v___y_426_);
v_env_428_ = lean_ctor_get(v___x_427_, 0);
v_nextMacroScope_429_ = lean_ctor_get(v___x_427_, 1);
v_ngen_430_ = lean_ctor_get(v___x_427_, 2);
v_auxDeclNGen_431_ = lean_ctor_get(v___x_427_, 3);
v_traceState_432_ = lean_ctor_get(v___x_427_, 4);
v_messages_433_ = lean_ctor_get(v___x_427_, 6);
v_infoState_434_ = lean_ctor_get(v___x_427_, 7);
v_snapshotTasks_435_ = lean_ctor_get(v___x_427_, 8);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v___x_427_, 5);
lean_dec(v_unused_445_);
v___x_437_ = v___x_427_;
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snapshotTasks_435_);
lean_inc(v_infoState_434_);
lean_inc(v_messages_433_);
lean_inc(v_traceState_432_);
lean_inc(v_auxDeclNGen_431_);
lean_inc(v_ngen_430_);
lean_inc(v_nextMacroScope_429_);
lean_inc(v_env_428_);
lean_dec(v___x_427_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_inc(v_name_419_);
v___x_439_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_428_, v_phase_389_, v_name_419_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 5, v___x_421_);
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_nextMacroScope_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_ngen_430_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_auxDeclNGen_431_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_traceState_432_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_messages_433_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_infoState_434_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_snapshotTasks_435_);
v___x_441_ = v_reuseFailAlloc_443_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; 
v___x_442_ = lean_st_ref_put(v___y_426_, v___x_441_);
v___y_400_ = v___y_423_;
v___y_401_ = v___y_424_;
v___y_402_ = v___y_425_;
v___y_403_ = v___y_426_;
goto v___jp_399_;
}
}
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_st_ref_put(v_a_394_, v___x_447_);
lean_inc_ref(v_decl_390_);
v___x_449_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_388_, v_decl_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_475_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_475_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_unbox(v_a_450_);
lean_dec(v_a_450_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec_ref(v___f_398_);
lean_dec_ref(v_decl_390_);
v___x_455_ = lean_box(0);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_455_);
v___x_457_ = v___x_452_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_object* v___x_459_; lean_object* v_env_460_; uint8_t v___x_461_; 
lean_del_object(v___x_452_);
v___x_459_ = lean_st_ref_get(v_a_394_);
v_env_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_env_460_);
lean_dec(v___x_459_);
v___x_461_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_460_, v_phase_389_, v_name_419_);
if (v___x_461_ == 0)
{
lean_object* v_toCold_462_; lean_object* v_options_463_; uint8_t v_hasTrace_464_; 
v_toCold_462_ = lean_ctor_get(v_a_393_, 0);
v_options_463_ = lean_ctor_get(v_toCold_462_, 2);
v_hasTrace_464_ = lean_ctor_get_uint8(v_options_463_, sizeof(void*)*1);
if (v_hasTrace_464_ == 0)
{
v___y_423_ = v_a_391_;
v___y_424_ = v_a_392_;
v___y_425_ = v_a_393_;
v___y_426_ = v_a_394_;
goto v___jp_422_;
}
else
{
lean_object* v_inheritedTraceOptions_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_inheritedTraceOptions_465_ = lean_ctor_get(v_toCold_462_, 11);
v___x_466_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_467_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_468_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_465_, v_options_463_, v___x_467_);
if (v___x_468_ == 0)
{
v___y_423_ = v_a_391_;
v___y_424_ = v_a_392_;
v___y_425_ = v_a_393_;
v___y_426_ = v_a_394_;
goto v___jp_422_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_469_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_419_);
v___x_470_ = l_Lean_MessageData_ofName(v_name_419_);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_466_, v___x_473_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_dec_ref_known(v___x_474_, 1);
v___y_423_ = v_a_391_;
v___y_424_ = v_a_392_;
v___y_425_ = v_a_393_;
v___y_426_ = v_a_394_;
goto v___jp_422_;
}
else
{
lean_dec_ref(v___f_398_);
lean_dec_ref(v_decl_390_);
return v___x_474_;
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
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v___f_398_);
lean_dec_ref(v_decl_390_);
v_a_476_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_449_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_449_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
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
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(uint8_t v_phase_490_, lean_object* v_decl_491_, lean_object* v_init_492_, lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_k_499_; lean_object* v_l_500_; lean_object* v_r_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_k_499_ = lean_ctor_get(v_x_493_, 1);
lean_inc(v_k_499_);
v_l_500_ = lean_ctor_get(v_x_493_, 3);
lean_inc(v_l_500_);
v_r_501_ = lean_ctor_get(v_x_493_, 4);
lean_inc(v_r_501_);
lean_dec_ref_known(v_x_493_, 5);
v___x_502_ = lean_box(0);
lean_inc_ref(v_decl_491_);
v___x_503_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_490_, v_decl_491_, v_init_492_, v_l_500_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; 
lean_dec_ref_known(v___x_503_, 1);
v___x_504_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_499_, v_phase_490_, v___y_497_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
if (lean_obj_tag(v_a_505_) == 1)
{
lean_object* v_val_506_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___x_523_; lean_object* v_env_524_; uint8_t v___x_525_; 
v_val_506_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_505_, 1);
v___x_523_ = lean_st_ref_get(v___y_497_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v___x_525_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_524_, v_k_499_);
if (v___x_525_ == 0)
{
lean_object* v_toCold_526_; lean_object* v_options_527_; uint8_t v_hasTrace_528_; 
v_toCold_526_ = lean_ctor_get(v___y_496_, 0);
v_options_527_ = lean_ctor_get(v_toCold_526_, 2);
v_hasTrace_528_ = lean_ctor_get_uint8(v_options_527_, sizeof(void*)*1);
if (v_hasTrace_528_ == 0)
{
lean_dec(v_k_499_);
v___y_508_ = v___y_494_;
v___y_509_ = v___y_495_;
v___y_510_ = v___y_496_;
v___y_511_ = v___y_497_;
goto v___jp_507_;
}
else
{
lean_object* v_inheritedTraceOptions_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_inheritedTraceOptions_529_ = lean_ctor_get(v_toCold_526_, 11);
v___x_530_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_531_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_529_, v_options_527_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec(v_k_499_);
v___y_508_ = v___y_494_;
v___y_509_ = v___y_495_;
v___y_510_ = v___y_496_;
v___y_511_ = v___y_497_;
goto v___jp_507_;
}
else
{
lean_object* v_toSignature_533_; lean_object* v_name_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_toSignature_533_ = lean_ctor_get(v_decl_491_, 0);
v_name_534_ = lean_ctor_get(v_toSignature_533_, 0);
v___x_535_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
v___x_536_ = l_Lean_MessageData_ofName(v_k_499_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_inc(v_name_534_);
v___x_540_ = l_Lean_MessageData_ofName(v_name_534_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_530_, v___x_541_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_dec_ref_known(v___x_542_, 1);
v___y_508_ = v___y_494_;
v___y_509_ = v___y_495_;
v___y_510_ = v___y_496_;
v___y_511_ = v___y_497_;
goto v___jp_507_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_val_506_);
lean_dec(v_r_501_);
lean_dec_ref(v_decl_491_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
else
{
lean_dec(v_val_506_);
lean_dec(v_k_499_);
v_init_492_ = v___x_502_;
v_x_493_ = v_r_501_;
goto _start;
}
v___jp_507_:
{
uint8_t v___x_512_; lean_object* v___x_513_; 
v___x_512_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_490_);
v___x_513_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_512_, v_phase_490_, v_val_506_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_dec_ref_known(v___x_513_, 1);
v_init_492_ = v___x_502_;
v_x_493_ = v_r_501_;
goto _start;
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_r_501_);
lean_dec_ref(v_decl_491_);
v_a_515_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_513_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_513_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
else
{
lean_dec(v_a_505_);
lean_dec(v_k_499_);
v_init_492_ = v___x_502_;
v_x_493_ = v_r_501_;
goto _start;
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_r_501_);
lean_dec(v_k_499_);
lean_dec_ref(v_decl_491_);
v_a_553_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_504_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_504_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_dec(v_r_501_);
lean_dec(v_k_499_);
lean_dec_ref(v_decl_491_);
return v___x_503_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v_decl_491_);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_init_492_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(uint8_t v_pu_563_, uint8_t v_phase_564_, lean_object* v_decl_565_, lean_object* v_code_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = l_Lean_NameSet_empty;
v___x_573_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_563_, v_code_566_, v___x_572_);
v___x_574_ = lean_box(0);
v___x_575_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_564_, v_decl_565_, v___x_574_, v___x_573_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_575_, 0);
lean_dec(v_unused_583_);
v___x_577_ = v___x_575_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_dec(v___x_575_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_574_);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_574_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_575_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_575_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(lean_object* v_phase_592_, lean_object* v_decl_593_, lean_object* v_init_594_, lean_object* v_x_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
uint8_t v_phase_boxed_601_; lean_object* v_res_602_; 
v_phase_boxed_601_ = lean_unbox(v_phase_592_);
v_res_602_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_601_, v_decl_593_, v_init_594_, v_x_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(lean_object* v_pu_603_, lean_object* v_phase_604_, lean_object* v_decl_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
uint8_t v_pu_boxed_611_; uint8_t v_phase_boxed_612_; lean_object* v_res_613_; 
v_pu_boxed_611_ = lean_unbox(v_pu_603_);
v_phase_boxed_612_ = lean_unbox(v_phase_604_);
v_res_613_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v_pu_boxed_611_, v_phase_boxed_612_, v_decl_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_toCold_620_; lean_object* v_ref_621_; lean_object* v___x_622_; lean_object* v_env_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_toCold_620_ = lean_ctor_get(v___y_617_, 0);
v_ref_621_ = lean_ctor_get(v___y_617_, 2);
v___x_622_ = lean_st_ref_get(v___y_618_);
v_env_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_622_);
v___x_624_ = lean_st_ref_get(v___y_616_);
v___x_625_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_615_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_648_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_648_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_648_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_648_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_lctx_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_646_; 
v_lctx_630_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v___x_624_, 1);
lean_dec(v_unused_647_);
v___x_632_ = v___x_624_;
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_lctx_630_);
lean_dec(v___x_624_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_options_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v_options_634_ = lean_ctor_get(v_toCold_620_, 2);
v___x_635_ = lean_unbox(v_a_626_);
lean_dec(v_a_626_);
v___x_636_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_630_, v___x_635_);
lean_dec_ref(v_lctx_630_);
v___x_637_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
lean_inc_ref(v_options_634_);
v___x_638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_638_, 0, v_env_623_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v___x_636_);
lean_ctor_set(v___x_638_, 3, v_options_634_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 3);
lean_ctor_set(v___x_632_, 1, v_msg_614_);
lean_ctor_set(v___x_632_, 0, v___x_638_);
v___x_640_ = v___x_632_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_msg_614_);
v___x_640_ = v_reuseFailAlloc_645_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_inc(v_ref_621_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_ref_621_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 1);
lean_ctor_set(v___x_628_, 0, v___x_641_);
v___x_643_ = v___x_628_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v___x_624_);
lean_dec_ref(v_env_623_);
lean_dec_ref(v_msg_614_);
v_a_649_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_625_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_625_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(lean_object* v_msg_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(lean_object* v_00_u03b1_664_, lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_665_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(lean_object* v_00_u03b1_673_, lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_673_, v_msg_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
return v_res_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(lean_object* v_opts_682_, lean_object* v_opt_683_){
_start:
{
lean_object* v_name_684_; lean_object* v_defValue_685_; lean_object* v_map_686_; lean_object* v___x_687_; 
v_name_684_ = lean_ctor_get(v_opt_683_, 0);
v_defValue_685_ = lean_ctor_get(v_opt_683_, 1);
v_map_686_ = lean_ctor_get(v_opts_682_, 0);
v___x_687_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_686_, v_name_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
uint8_t v___x_688_; 
v___x_688_ = lean_unbox(v_defValue_685_);
return v___x_688_;
}
else
{
lean_object* v_val_689_; 
v_val_689_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v___x_687_, 1);
if (lean_obj_tag(v_val_689_) == 1)
{
uint8_t v_v_690_; 
v_v_690_ = lean_ctor_get_uint8(v_val_689_, 0);
lean_dec_ref_known(v_val_689_, 0);
return v_v_690_;
}
else
{
uint8_t v___x_691_; 
lean_dec(v_val_689_);
v___x_691_ = lean_unbox(v_defValue_685_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(lean_object* v_opts_692_, lean_object* v_opt_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_692_, v_opt_693_);
lean_dec_ref(v_opt_693_);
lean_dec_ref(v_opts_692_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(lean_object* v_f_696_, lean_object* v_v_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
if (lean_obj_tag(v_v_697_) == 0)
{
lean_object* v_code_704_; lean_object* v___x_705_; 
v_code_704_ = lean_ctor_get(v_v_697_, 0);
lean_inc_ref(v_code_704_);
lean_dec_ref_known(v_v_697_, 1);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
v___x_705_ = lean_apply_7(v_f_696_, v_code_704_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, lean_box(0));
return v___x_705_;
}
else
{
lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_f_696_);
v_isSharedCheck_714_ = !lean_is_exclusive(v_v_697_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_v_697_, 0);
lean_dec(v_unused_715_);
v___x_707_ = v_v_697_;
v_isShared_708_ = v_isSharedCheck_714_;
goto v_resetjp_706_;
}
else
{
lean_dec(v_v_697_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_714_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___y_698_);
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 0);
lean_ctor_set(v___x_707_, 0, v___x_710_);
v___x_712_ = v___x_707_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(lean_object* v_f_716_, lean_object* v_v_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_716_, v_v_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(uint8_t v_pu_725_, lean_object* v_f_726_, lean_object* v_v_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_726_, v_v_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(lean_object* v_pu_735_, lean_object* v_f_736_, lean_object* v_v_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v_pu_boxed_744_; lean_object* v_res_745_; 
v_pu_boxed_744_ = lean_unbox(v_pu_735_);
v_res_745_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_744_, v_f_736_, v_v_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_745_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4));
v___x_754_ = l_Lean_stringToMessageData(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(uint8_t v_pu_779_, lean_object* v_origDecl_780_, uint8_t v_isMeta_781_, uint8_t v_isPublic_782_, lean_object* v_init_783_, lean_object* v_x_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_k_791_; lean_object* v_l_792_; lean_object* v_r_793_; lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_845_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_k_791_ = lean_ctor_get(v_x_784_, 1);
lean_inc(v_k_791_);
v_l_792_ = lean_ctor_get(v_x_784_, 3);
lean_inc(v_l_792_);
v_r_793_ = lean_ctor_get(v_x_784_, 4);
lean_inc(v_r_793_);
lean_dec_ref_known(v_x_784_, 5);
v___x_794_ = lean_box(0);
v___x_847_ = lean_box(0);
lean_inc_ref(v_origDecl_780_);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_779_, v_origDecl_780_, v_isMeta_781_, v_isPublic_782_, v_init_783_, v_l_792_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_1156_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_snd_850_ = lean_ctor_get(v_a_849_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_849_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_a_849_, 0);
lean_dec(v_unused_1157_);
v___x_852_ = v_a_849_;
v_isShared_853_ = v_isSharedCheck_1156_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_dec(v_a_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_1156_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; uint8_t v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; uint8_t v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; 
v___x_854_ = l_Lean_NameSet_contains(v_snd_850_, v_k_791_);
if (v___x_854_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v_env_896_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; uint8_t v___y_904_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; uint8_t v___y_938_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; uint8_t v___y_948_; uint8_t v___y_949_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_956_; uint8_t v___y_957_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; uint8_t v___y_964_; uint8_t v___y_968_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_976_; uint8_t v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; uint8_t v___y_982_; uint8_t v___y_983_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1072_; uint8_t v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; uint8_t v___y_1137_; 
lean_inc(v_k_791_);
v___x_894_ = l_Lean_NameSet_insert(v_snd_850_, v_k_791_);
v___x_895_ = lean_st_ref_get(v___y_789_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref(v_env_896_);
lean_dec(v___x_895_);
if (v_isMeta_781_ == 0)
{
v___y_1137_ = v___x_854_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v_isPublic_782_;
goto v___jp_1136_;
}
v___jp_897_:
{
lean_object* v_toSignature_905_; lean_object* v_name_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v___y_900_);
v_toSignature_905_ = lean_ctor_get(v_origDecl_780_, 0);
lean_inc_ref(v_toSignature_905_);
lean_dec_ref(v_origDecl_780_);
v_name_906_ = lean_ctor_get(v_toSignature_905_, 0);
lean_inc(v_name_906_);
lean_dec_ref(v_toSignature_905_);
v___x_907_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_908_ = l_Lean_MessageData_ofConstName(v_name_906_, v___x_854_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_MessageData_ofConstName(v_k_791_, v___x_854_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_Environment_header(v_env_896_);
lean_dec_ref(v_env_896_);
v___x_917_ = l_Lean_EnvironmentHeader_moduleNames(v___x_916_);
v___x_918_ = lean_array_get(v___x_847_, v___x_917_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___x_917_);
v___x_919_ = l_Lean_MessageData_ofName(v___x_918_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_915_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_922_, v___y_903_, v___y_902_, v___y_899_, v___y_898_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
v___jp_932_:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_896_, v_k_791_);
if (lean_obj_tag(v___x_939_) == 1)
{
lean_object* v_val_940_; uint8_t v___x_941_; 
v_val_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___x_939_, 1);
lean_inc(v_k_791_);
lean_inc_ref(v_env_896_);
v___x_941_ = l_Lean_isMarkedMeta(v_env_896_, v_k_791_);
if (v___x_941_ == 0)
{
lean_del_object(v___x_852_);
v___y_898_ = v___y_933_;
v___y_899_ = v___y_934_;
v___y_900_ = v___y_935_;
v___y_901_ = v_val_940_;
v___y_902_ = v___y_937_;
v___y_903_ = v___y_936_;
v___y_904_ = v___y_938_;
goto v___jp_897_;
}
else
{
if (v___x_854_ == 0)
{
lean_dec(v_val_940_);
lean_dec_ref(v_env_896_);
v___y_866_ = v___y_938_;
v___y_867_ = v___y_935_;
v___y_868_ = v___y_936_;
v___y_869_ = v___y_937_;
v___y_870_ = v___y_934_;
v___y_871_ = v___y_933_;
goto v___jp_865_;
}
else
{
lean_del_object(v___x_852_);
v___y_898_ = v___y_933_;
v___y_899_ = v___y_934_;
v___y_900_ = v___y_935_;
v___y_901_ = v_val_940_;
v___y_902_ = v___y_937_;
v___y_903_ = v___y_936_;
v___y_904_ = v___y_938_;
goto v___jp_897_;
}
}
}
else
{
lean_dec(v___x_939_);
lean_dec_ref(v_env_896_);
v___y_866_ = v___y_938_;
v___y_867_ = v___y_935_;
v___y_868_ = v___y_936_;
v___y_869_ = v___y_937_;
v___y_870_ = v___y_934_;
v___y_871_ = v___y_933_;
goto v___jp_865_;
}
}
v___jp_942_:
{
if (v___y_949_ == 0)
{
lean_dec_ref(v_env_896_);
lean_del_object(v___x_852_);
v___y_856_ = v___y_948_;
v___y_857_ = v___y_945_;
v___y_858_ = v___y_947_;
v___y_859_ = v___y_946_;
v___y_860_ = v___y_944_;
v___y_861_ = v___y_943_;
goto v___jp_855_;
}
else
{
lean_dec(v_r_793_);
v___y_933_ = v___y_943_;
v___y_934_ = v___y_944_;
v___y_935_ = v___y_945_;
v___y_936_ = v___y_947_;
v___y_937_ = v___y_946_;
v___y_938_ = v___y_948_;
goto v___jp_932_;
}
}
v___jp_950_:
{
if (v___y_957_ == 0)
{
v___y_943_ = v___y_951_;
v___y_944_ = v___y_952_;
v___y_945_ = v___y_953_;
v___y_946_ = v___y_955_;
v___y_947_ = v___y_954_;
v___y_948_ = v___y_956_;
v___y_949_ = v___x_854_;
goto v___jp_942_;
}
else
{
if (v_isMeta_781_ == 0)
{
lean_dec(v_r_793_);
v___y_933_ = v___y_951_;
v___y_934_ = v___y_952_;
v___y_935_ = v___y_953_;
v___y_936_ = v___y_954_;
v___y_937_ = v___y_955_;
v___y_938_ = v___y_956_;
goto v___jp_932_;
}
else
{
v___y_943_ = v___y_951_;
v___y_944_ = v___y_952_;
v___y_945_ = v___y_953_;
v___y_946_ = v___y_955_;
v___y_947_ = v___y_954_;
v___y_948_ = v___y_956_;
v___y_949_ = v___x_854_;
goto v___jp_942_;
}
}
}
v___jp_958_:
{
uint8_t v___x_965_; uint8_t v___x_966_; 
v___x_965_ = 1;
v___x_966_ = l_Lean_instBEqIRPhases_beq(v___y_964_, v___x_965_);
v___y_951_ = v___y_959_;
v___y_952_ = v___y_960_;
v___y_953_ = v___y_961_;
v___y_954_ = v___y_963_;
v___y_955_ = v___y_962_;
v___y_956_ = v___y_964_;
v___y_957_ = v___x_966_;
goto v___jp_950_;
}
v___jp_967_:
{
if (v___y_968_ == 0)
{
v___y_959_ = v___y_974_;
v___y_960_ = v___y_973_;
v___y_961_ = v___y_970_;
v___y_962_ = v___y_972_;
v___y_963_ = v___y_971_;
v___y_964_ = v___y_969_;
goto v___jp_958_;
}
else
{
if (v___x_854_ == 0)
{
v___y_951_ = v___y_974_;
v___y_952_ = v___y_973_;
v___y_953_ = v___y_970_;
v___y_954_ = v___y_971_;
v___y_955_ = v___y_972_;
v___y_956_ = v___y_969_;
v___y_957_ = v___x_854_;
goto v___jp_950_;
}
else
{
v___y_959_ = v___y_974_;
v___y_960_ = v___y_973_;
v___y_961_ = v___y_970_;
v___y_962_ = v___y_972_;
v___y_963_ = v___y_971_;
v___y_964_ = v___y_969_;
goto v___jp_958_;
}
}
}
v___jp_975_:
{
if (v___y_983_ == 0)
{
v___y_968_ = v___y_977_;
v___y_969_ = v___y_982_;
v___y_970_ = v___y_976_;
v___y_971_ = v___y_979_;
v___y_972_ = v___y_981_;
v___y_973_ = v___y_978_;
v___y_974_ = v___y_980_;
goto v___jp_967_;
}
else
{
lean_object* v___x_984_; 
lean_dec(v___y_976_);
lean_del_object(v___x_852_);
lean_dec(v_r_793_);
v___x_984_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_896_, v_k_791_);
if (lean_obj_tag(v___x_984_) == 1)
{
lean_object* v_toSignature_985_; lean_object* v_val_986_; lean_object* v_name_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_toSignature_985_ = lean_ctor_get(v_origDecl_780_, 0);
lean_inc_ref(v_toSignature_985_);
lean_dec_ref(v_origDecl_780_);
v_val_986_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v___x_984_, 1);
v_name_987_ = lean_ctor_get(v_toSignature_985_, 0);
lean_inc(v_name_987_);
lean_dec_ref(v_toSignature_985_);
v___x_988_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_989_ = l_Lean_MessageData_ofConstName(v_name_987_, v___x_854_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_MessageData_ofConstName(v_k_791_, v___x_854_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Lean_Environment_header(v_env_896_);
lean_dec_ref(v_env_896_);
v___x_998_ = l_Lean_EnvironmentHeader_moduleNames(v___x_997_);
v___x_999_ = lean_array_get(v___x_847_, v___x_998_, v_val_986_);
lean_dec(v_val_986_);
lean_dec_ref(v___x_998_);
v___x_1000_ = l_Lean_MessageData_ofName(v___x_999_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_996_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1003_, v___y_979_, v___y_981_, v___y_978_, v___y_980_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_toSignature_1013_; lean_object* v_name_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v___x_984_);
lean_dec_ref(v_env_896_);
v_toSignature_1013_ = lean_ctor_get(v_origDecl_780_, 0);
lean_inc_ref(v_toSignature_1013_);
lean_dec_ref(v_origDecl_780_);
v_name_1014_ = lean_ctor_get(v_toSignature_1013_, 0);
lean_inc(v_name_1014_);
lean_dec_ref(v_toSignature_1013_);
v___x_1015_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
v___x_1016_ = l_Lean_MessageData_ofConstName(v_name_1014_, v___x_854_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_ofConstName(v_k_791_, v___x_854_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1023_, v___y_979_, v___y_981_, v___y_978_, v___y_980_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
v___jp_1033_:
{
if (v___y_1041_ == 0)
{
v___y_976_ = v___y_1034_;
v___y_977_ = v___y_1036_;
v___y_978_ = v___y_1035_;
v___y_979_ = v___y_1037_;
v___y_980_ = v___y_1038_;
v___y_981_ = v___y_1039_;
v___y_982_ = v___y_1040_;
v___y_983_ = v___x_854_;
goto v___jp_975_;
}
else
{
v___y_976_ = v___y_1034_;
v___y_977_ = v___y_1036_;
v___y_978_ = v___y_1035_;
v___y_979_ = v___y_1037_;
v___y_980_ = v___y_1038_;
v___y_981_ = v___y_1039_;
v___y_982_ = v___y_1040_;
v___y_983_ = v_isMeta_781_;
goto v___jp_975_;
}
}
v___jp_1042_:
{
uint8_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = 0;
v___x_1051_ = l_Lean_instBEqIRPhases_beq(v___y_1049_, v___x_1050_);
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___y_1044_;
v___y_1037_ = v___y_1046_;
v___y_1038_ = v___y_1047_;
v___y_1039_ = v___y_1048_;
v___y_1040_ = v___y_1049_;
v___y_1041_ = v___x_1051_;
goto v___jp_1033_;
}
v___jp_1052_:
{
uint8_t v___x_1059_; 
lean_inc(v_k_791_);
lean_inc_ref(v_env_896_);
v___x_1059_ = l_Lean_getIRPhases(v_env_896_, v_k_791_);
if (v___y_1058_ == 0)
{
v___y_1043_ = v___y_1053_;
v___y_1044_ = v___y_1058_;
v___y_1045_ = v___y_1054_;
v___y_1046_ = v___y_1055_;
v___y_1047_ = v___y_1056_;
v___y_1048_ = v___y_1057_;
v___y_1049_ = v___x_1059_;
goto v___jp_1042_;
}
else
{
if (v___x_854_ == 0)
{
v___y_1034_ = v___y_1053_;
v___y_1035_ = v___y_1054_;
v___y_1036_ = v___y_1058_;
v___y_1037_ = v___y_1055_;
v___y_1038_ = v___y_1056_;
v___y_1039_ = v___y_1057_;
v___y_1040_ = v___x_1059_;
v___y_1041_ = v___x_854_;
goto v___jp_1033_;
}
else
{
v___y_1043_ = v___y_1053_;
v___y_1044_ = v___y_1058_;
v___y_1045_ = v___y_1054_;
v___y_1046_ = v___y_1055_;
v___y_1047_ = v___y_1056_;
v___y_1048_ = v___y_1057_;
v___y_1049_ = v___x_1059_;
goto v___jp_1042_;
}
}
}
v___jp_1060_:
{
lean_object* v_toCold_1066_; lean_object* v_options_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_toCold_1066_ = lean_ctor_get(v___y_1064_, 0);
v_options_1067_ = lean_ctor_get(v_toCold_1066_, 2);
v___x_1068_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_1069_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
v___y_1053_ = v___y_1061_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v___y_1062_;
v___y_1056_ = v___y_1065_;
v___y_1057_ = v___y_1063_;
v___y_1058_ = v___x_854_;
goto v___jp_1052_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = l_Lean_Environment_isImportedConst(v_env_896_, v_k_791_);
if (v___x_1070_ == 0)
{
v___y_1053_ = v___y_1061_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v___y_1062_;
v___y_1056_ = v___y_1065_;
v___y_1057_ = v___y_1063_;
v___y_1058_ = v___x_1069_;
goto v___jp_1052_;
}
else
{
v___y_1053_ = v___y_1061_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v___y_1062_;
v___y_1056_ = v___y_1065_;
v___y_1057_ = v___y_1063_;
v___y_1058_ = v___x_854_;
goto v___jp_1052_;
}
}
}
v___jp_1071_:
{
lean_object* v_toSignature_1075_; lean_object* v_name_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_toSignature_1075_ = lean_ctor_get(v_origDecl_780_, 0);
lean_inc_ref(v_toSignature_1075_);
lean_dec_ref(v_origDecl_780_);
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
v___x_1082_ = l_Lean_MessageData_ofConstName(v_k_791_, v___y_1073_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_EnvironmentHeader_moduleNames(v___y_1074_);
v___x_1087_ = lean_array_get(v___x_847_, v___x_1086_, v___y_1072_);
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
v___x_1092_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1091_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
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
lean_dec(v___y_1103_);
v___y_1061_ = v___x_894_;
v___y_1062_ = v___y_786_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
goto v___jp_1060_;
}
else
{
lean_dec_ref(v_env_896_);
lean_dec(v___x_894_);
lean_del_object(v___x_852_);
lean_dec(v_r_793_);
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1102_;
v___y_1074_ = v___y_1104_;
goto v___jp_1071_;
}
}
v___jp_1106_:
{
if (v___y_1109_ == 0)
{
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
v___y_1061_ = v___x_894_;
v___y_1062_ = v___y_786_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
goto v___jp_1060_;
}
else
{
lean_object* v_toSignature_1110_; lean_object* v_name_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_env_896_);
lean_dec(v___x_894_);
lean_del_object(v___x_852_);
lean_dec(v_r_793_);
v_toSignature_1110_ = lean_ctor_get(v_origDecl_780_, 0);
lean_inc_ref(v_toSignature_1110_);
lean_dec_ref(v_origDecl_780_);
v_name_1111_ = lean_ctor_get(v_toSignature_1110_, 0);
lean_inc(v_name_1111_);
lean_dec_ref(v_toSignature_1110_);
v___x_1112_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
v___x_1113_ = l_Lean_MessageData_ofConstName(v_name_1111_, v___x_854_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_ofConstName(v_k_791_, v___x_854_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_EnvironmentHeader_moduleNames(v___y_1107_);
v___x_1122_ = lean_array_get(v___x_847_, v___x_1121_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = l_Lean_MessageData_ofName(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1120_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_1126_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
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
v___y_1061_ = v___x_894_;
v___y_1062_ = v___y_786_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
goto v___jp_1060_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_896_, v_k_791_);
if (lean_obj_tag(v___x_1138_) == 1)
{
lean_object* v_val_1139_; uint8_t v___x_1140_; 
v_val_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v___x_1138_, 1);
lean_inc(v_k_791_);
lean_inc_ref(v_env_896_);
v___x_1140_ = l_Lean_isMarkedMeta(v_env_896_, v_k_791_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v_modules_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = l_Lean_Environment_header(v_env_896_);
v_modules_1142_ = lean_ctor_get(v___x_1141_, 3);
lean_inc_ref(v_modules_1142_);
v___x_1143_ = lean_array_get_size(v_modules_1142_);
v___x_1144_ = lean_nat_dec_lt(v_val_1139_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec_ref(v_modules_1142_);
v___y_1102_ = v___x_1140_;
v___y_1103_ = v_val_1139_;
v___y_1104_ = v___x_1141_;
v___y_1105_ = v___x_1140_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1145_; lean_object* v_toImport_1146_; uint8_t v_isExported_1147_; 
v___x_1145_ = lean_array_fget(v_modules_1142_, v_val_1139_);
lean_dec_ref(v_modules_1142_);
v_toImport_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref(v_toImport_1146_);
lean_dec(v___x_1145_);
v_isExported_1147_ = lean_ctor_get_uint8(v_toImport_1146_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1146_);
if (v_isExported_1147_ == 0)
{
lean_dec_ref(v_env_896_);
lean_dec(v___x_894_);
lean_del_object(v___x_852_);
lean_dec(v_r_793_);
v___y_1072_ = v_val_1139_;
v___y_1073_ = v___x_1140_;
v___y_1074_ = v___x_1141_;
goto v___jp_1071_;
}
else
{
v___y_1102_ = v___x_1140_;
v___y_1103_ = v_val_1139_;
v___y_1104_ = v___x_1141_;
v___y_1105_ = v___x_1140_;
goto v___jp_1101_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v_modules_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1148_ = l_Lean_Environment_header(v_env_896_);
v_modules_1149_ = lean_ctor_get(v___x_1148_, 3);
lean_inc_ref(v_modules_1149_);
v___x_1150_ = lean_array_get_size(v_modules_1149_);
v___x_1151_ = lean_nat_dec_lt(v_val_1139_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec_ref(v_modules_1149_);
v___y_1107_ = v___x_1148_;
v___y_1108_ = v_val_1139_;
v___y_1109_ = v___x_854_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1152_; lean_object* v_toImport_1153_; uint8_t v_isExported_1154_; 
v___x_1152_ = lean_array_fget(v_modules_1149_, v_val_1139_);
lean_dec_ref(v_modules_1149_);
v_toImport_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc_ref(v_toImport_1153_);
lean_dec(v___x_1152_);
v_isExported_1154_ = lean_ctor_get_uint8(v_toImport_1153_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1153_);
if (v_isExported_1154_ == 0)
{
v___y_1107_ = v___x_1148_;
v___y_1108_ = v_val_1139_;
v___y_1109_ = v___x_1140_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v___x_1148_;
v___y_1108_ = v_val_1139_;
v___y_1109_ = v___x_854_;
goto v___jp_1106_;
}
}
}
}
else
{
lean_dec(v___x_1138_);
v___y_1061_ = v___x_894_;
v___y_1062_ = v___y_786_;
v___y_1063_ = v___y_787_;
v___y_1064_ = v___y_788_;
v___y_1065_ = v___y_789_;
goto v___jp_1060_;
}
}
}
}
else
{
lean_del_object(v___x_852_);
lean_dec(v_k_791_);
v_init_783_ = v___x_794_;
v_x_784_ = v_r_793_;
v___y_785_ = v_snd_850_;
goto _start;
}
v___jp_855_:
{
uint8_t v___x_862_; uint8_t v___x_863_; 
v___x_862_ = 2;
v___x_863_ = l_Lean_instBEqIRPhases_beq(v___y_856_, v___x_862_);
if (v___x_863_ == 0)
{
if (v_isPublic_782_ == 0)
{
v___y_840_ = v___y_860_;
v___y_841_ = v___y_857_;
v___y_842_ = v___y_859_;
v___y_843_ = v___y_858_;
v___y_844_ = v___y_861_;
v___y_845_ = v___x_854_;
goto v___jp_839_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_isPrivateName(v_k_791_);
v___y_840_ = v___y_860_;
v___y_841_ = v___y_857_;
v___y_842_ = v___y_859_;
v___y_843_ = v___y_858_;
v___y_844_ = v___y_861_;
v___y_845_ = v___x_864_;
goto v___jp_839_;
}
}
else
{
v___y_796_ = v___y_860_;
v___y_797_ = v___y_857_;
v___y_798_ = v___y_859_;
v___y_799_ = v___y_858_;
v___y_800_ = v___y_861_;
goto v___jp_795_;
}
}
v___jp_865_:
{
lean_object* v_toSignature_872_; lean_object* v_name_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v___y_867_);
v_toSignature_872_ = lean_ctor_get(v_origDecl_780_, 0);
lean_inc_ref(v_toSignature_872_);
lean_dec_ref(v_origDecl_780_);
v_name_873_ = lean_ctor_get(v_toSignature_872_, 0);
lean_inc(v_name_873_);
lean_dec_ref(v_toSignature_872_);
v___x_874_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
v___x_875_ = l_Lean_MessageData_ofConstName(v_name_873_, v___x_854_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 7);
lean_ctor_set(v___x_852_, 1, v___x_875_);
lean_ctor_set(v___x_852_, 0, v___x_874_);
v___x_877_ = v___x_852_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_893_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v___x_878_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_MessageData_ofConstName(v_k_791_, v___x_854_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_883_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
else
{
lean_dec(v_r_793_);
lean_dec(v_k_791_);
lean_dec_ref(v_origDecl_780_);
return v___x_848_;
}
v___jp_795_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v___x_803_ = lean_unbox(v_a_802_);
v___x_804_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_k_791_, v___x_803_, v___y_800_);
lean_dec(v_k_791_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
if (lean_obj_tag(v_a_805_) == 1)
{
lean_object* v_val_806_; uint8_t v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_val_806_ = lean_ctor_get(v_a_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_a_805_, 1);
v___x_807_ = lean_unbox(v_a_802_);
lean_dec(v_a_802_);
v___x_808_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_807_);
v___x_809_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(v___x_808_, v_val_806_, v_pu_779_);
lean_dec(v_val_806_);
lean_inc_ref(v_origDecl_780_);
v___x_810_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_779_, v_origDecl_780_, v_isMeta_781_, v_isPublic_782_, v___x_809_, v___y_797_, v___y_799_, v___y_798_, v___y_796_, v___y_800_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v_snd_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v_snd_812_ = lean_ctor_get(v_a_811_, 1);
lean_inc(v_snd_812_);
lean_dec(v_a_811_);
v_init_783_ = v___x_794_;
v_x_784_ = v_r_793_;
v___y_785_ = v_snd_812_;
goto _start;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_r_793_);
lean_dec_ref(v_origDecl_780_);
v_a_814_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_810_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_dec(v_a_805_);
lean_dec(v_a_802_);
v_init_783_ = v___x_794_;
v_x_784_ = v_r_793_;
v___y_785_ = v___y_797_;
goto _start;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_a_802_);
lean_dec(v___y_797_);
lean_dec(v_r_793_);
lean_dec_ref(v_origDecl_780_);
v_a_823_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_804_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_804_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v___y_797_);
lean_dec(v_r_793_);
lean_dec(v_k_791_);
lean_dec_ref(v_origDecl_780_);
v_a_831_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_801_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_801_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
v___jp_839_:
{
if (v___y_845_ == 0)
{
lean_dec(v_k_791_);
v_init_783_ = v___x_794_;
v_x_784_ = v_r_793_;
v___y_785_ = v___y_841_;
goto _start;
}
else
{
v___y_796_ = v___y_840_;
v___y_797_ = v___y_841_;
v___y_798_ = v___y_842_;
v___y_799_ = v___y_843_;
v___y_800_ = v___y_844_;
goto v___jp_795_;
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v_origDecl_780_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_init_783_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___y_785_);
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
lean_object* v_toCold_1267_; lean_object* v_options_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_toCold_1267_ = lean_ctor_get(v___y_1265_, 0);
v_options_1268_ = lean_ctor_get(v_toCold_1267_, 2);
v___x_1269_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1268_, v_opt_1264_);
v___x_1270_ = lean_box(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(lean_object* v_opt_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1272_, v___y_1273_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v_opt_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t v_pu_1276_, lean_object* v_origDecl_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_env_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1343_; 
v___x_1283_ = lean_st_ref_get(v_a_1281_);
v_env_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_env_1284_);
lean_dec(v___x_1283_);
v___x_1285_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_1286_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1285_, v_a_1280_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1343_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1343_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1342_; 
v___x_1291_ = l_Lean_Compiler_compiler_checkMeta;
v___x_1292_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v___x_1291_, v_a_1280_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1342_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1342_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1302_; uint8_t v_isModule_1303_; 
v___x_1302_ = l_Lean_Environment_header(v_env_1284_);
lean_dec_ref(v_env_1284_);
v_isModule_1303_ = lean_ctor_get_uint8(v___x_1302_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1302_);
if (v_isModule_1303_ == 0)
{
lean_dec(v_a_1293_);
lean_del_object(v___x_1289_);
lean_dec(v_a_1287_);
lean_dec_ref(v_origDecl_1277_);
goto v___jp_1297_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_unbox(v_a_1293_);
if (v___x_1305_ == 0)
{
lean_dec(v_a_1293_);
lean_del_object(v___x_1289_);
lean_dec_ref(v_origDecl_1277_);
goto v___jp_1297_;
}
else
{
lean_object* v___x_1306_; lean_object* v_toSignature_1307_; lean_object* v_env_1308_; lean_object* v_name_1309_; uint8_t v___x_1310_; uint8_t v___y_1312_; uint8_t v___x_1334_; uint8_t v___x_1335_; 
lean_del_object(v___x_1295_);
v___x_1306_ = lean_st_ref_get(v_a_1281_);
v_toSignature_1307_ = lean_ctor_get(v_origDecl_1277_, 0);
v_env_1308_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_env_1308_);
lean_dec(v___x_1306_);
v_name_1309_ = lean_ctor_get(v_toSignature_1307_, 0);
lean_inc(v_name_1309_);
v___x_1310_ = l_Lean_getIRPhases(v_env_1308_, v_name_1309_);
v___x_1334_ = 2;
v___x_1335_ = l_Lean_instBEqIRPhases_beq(v___x_1310_, v___x_1334_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; 
lean_del_object(v___x_1289_);
v___x_1336_ = l_Lean_isPrivateName(v_name_1309_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
v___y_1312_ = v___x_1337_;
goto v___jp_1311_;
}
else
{
lean_dec(v_a_1293_);
v___y_1312_ = v___x_1335_;
goto v___jp_1311_;
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_a_1293_);
lean_dec_ref(v_origDecl_1277_);
v___x_1338_ = lean_box(0);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1338_);
v___x_1340_ = v___x_1289_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
v___jp_1311_:
{
uint8_t v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1313_ = 1;
v___x_1314_ = l_Lean_instBEqIRPhases_beq(v___x_1310_, v___x_1313_);
v___x_1315_ = l_Lean_NameSet_empty;
lean_inc_ref(v_origDecl_1277_);
v___x_1316_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_1276_, v_origDecl_1277_, v___x_1314_, v___y_1312_, v_origDecl_1277_, v___x_1315_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_fst_1321_; lean_object* v___x_1323_; 
v_fst_1321_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_fst_1321_);
lean_dec(v_a_1317_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v_fst_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_fst_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1316_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1293_);
lean_del_object(v___x_1289_);
lean_dec_ref(v_origDecl_1277_);
goto v___jp_1297_;
}
}
v___jp_1297_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_box(0);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1298_);
v___x_1300_ = v___x_1295_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkMeta___boxed(lean_object* v_pu_1344_, lean_object* v_origDecl_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
uint8_t v_pu_boxed_1351_; lean_object* v_res_1352_; 
v_pu_boxed_1351_ = lean_unbox(v_pu_1344_);
v_res_1352_ = l_Lean_Compiler_LCNF_checkMeta(v_pu_boxed_1351_, v_origDecl_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(lean_object* v_opt_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(v_opt_1353_, v___y_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(lean_object* v_opt_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(v_opt_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec_ref(v_opt_1360_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(uint8_t v_isExporting_1367_, lean_object* v___x_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_env_1377_; lean_object* v_nextMacroScope_1378_; lean_object* v_ngen_1379_; lean_object* v_auxDeclNGen_1380_; lean_object* v_traceState_1381_; lean_object* v_messages_1382_; lean_object* v_infoState_1383_; lean_object* v_snapshotTasks_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1396_; 
v___x_1376_ = lean_st_ref_take(v___y_1374_);
v_env_1377_ = lean_ctor_get(v___x_1376_, 0);
v_nextMacroScope_1378_ = lean_ctor_get(v___x_1376_, 1);
v_ngen_1379_ = lean_ctor_get(v___x_1376_, 2);
v_auxDeclNGen_1380_ = lean_ctor_get(v___x_1376_, 3);
v_traceState_1381_ = lean_ctor_get(v___x_1376_, 4);
v_messages_1382_ = lean_ctor_get(v___x_1376_, 6);
v_infoState_1383_ = lean_ctor_get(v___x_1376_, 7);
v_snapshotTasks_1384_ = lean_ctor_get(v___x_1376_, 8);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___x_1376_, 5);
lean_dec(v_unused_1397_);
v___x_1386_ = v___x_1376_;
v_isShared_1387_ = v_isSharedCheck_1396_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snapshotTasks_1384_);
lean_inc(v_infoState_1383_);
lean_inc(v_messages_1382_);
lean_inc(v_traceState_1381_);
lean_inc(v_auxDeclNGen_1380_);
lean_inc(v_ngen_1379_);
lean_inc(v_nextMacroScope_1378_);
lean_inc(v_env_1377_);
lean_dec(v___x_1376_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1396_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Lean_Environment_setExporting(v_env_1377_, v_isExporting_1367_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 5, v___x_1368_);
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_nextMacroScope_1378_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_ngen_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_auxDeclNGen_1380_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_traceState_1381_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_messages_1382_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_infoState_1383_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v_snapshotTasks_1384_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_st_ref_put(v___y_1374_, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1388_);
lean_ctor_set(v___x_1393_, 1, v___y_1370_);
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
v_isExporting_1452_ = lean_ctor_get_uint8(v_env_1448_, sizeof(void*)*8);
lean_dec_ref(v_env_1448_);
if (v_isExporting_1440_ == 0)
{
if (v_isExporting_1452_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1531_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1531_;
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
lean_object* v___x_1532_; 
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1532_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1532_;
}
}
v___jp_1453_:
{
lean_object* v___x_1454_; lean_object* v_env_1455_; lean_object* v_nextMacroScope_1456_; lean_object* v_ngen_1457_; lean_object* v_auxDeclNGen_1458_; lean_object* v_traceState_1459_; lean_object* v_messages_1460_; lean_object* v_infoState_1461_; lean_object* v_snapshotTasks_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1529_; 
v___x_1454_ = lean_st_ref_take(v___y_1445_);
v_env_1455_ = lean_ctor_get(v___x_1454_, 0);
v_nextMacroScope_1456_ = lean_ctor_get(v___x_1454_, 1);
v_ngen_1457_ = lean_ctor_get(v___x_1454_, 2);
v_auxDeclNGen_1458_ = lean_ctor_get(v___x_1454_, 3);
v_traceState_1459_ = lean_ctor_get(v___x_1454_, 4);
v_messages_1460_ = lean_ctor_get(v___x_1454_, 6);
v_infoState_1461_ = lean_ctor_get(v___x_1454_, 7);
v_snapshotTasks_1462_ = lean_ctor_get(v___x_1454_, 8);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1454_, 5);
lean_dec(v_unused_1530_);
v___x_1464_ = v___x_1454_;
v_isShared_1465_ = v_isSharedCheck_1529_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snapshotTasks_1462_);
lean_inc(v_infoState_1461_);
lean_inc(v_messages_1460_);
lean_inc(v_traceState_1459_);
lean_inc(v_auxDeclNGen_1458_);
lean_inc(v_ngen_1457_);
lean_inc(v_nextMacroScope_1456_);
lean_inc(v_env_1455_);
lean_dec(v___x_1454_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1529_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v___x_1471_; 
v___x_1466_ = l_Lean_Environment_setExporting(v_env_1455_, v_isExporting_1440_);
v___x_1467_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
v___x_1468_ = lean_box(v_isExporting_1452_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1469_, 0, v___x_1468_);
lean_closure_set(v___f_1469_, 1, v___x_1467_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 5, v___x_1467_);
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1471_ = v___x_1464_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_nextMacroScope_1456_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_ngen_1457_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_auxDeclNGen_1458_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_traceState_1459_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1528_, 6, v_messages_1460_);
lean_ctor_set(v_reuseFailAlloc_1528_, 7, v_infoState_1461_);
lean_ctor_set(v_reuseFailAlloc_1528_, 8, v_snapshotTasks_1462_);
v___x_1471_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; lean_object* v_r_1473_; 
v___x_1472_ = lean_st_ref_put(v___y_1445_, v___x_1471_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
v_r_1473_ = lean_apply_6(v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
if (lean_obj_tag(v_r_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1508_; 
v_a_1474_ = lean_ctor_get(v_r_1473_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_r_1473_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1476_ = v_r_1473_;
v_isShared_1477_ = v_isSharedCheck_1508_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v_r_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1508_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
lean_inc(v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set_tag(v___x_1476_, 1);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1469_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___x_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1498_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1498_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1498_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1496_; 
v_fst_1485_ = lean_ctor_get(v_a_1474_, 0);
lean_inc(v_fst_1485_);
lean_dec(v_a_1474_);
v_snd_1486_ = lean_ctor_get(v_a_1481_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_a_1481_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_a_1481_, 0);
lean_dec(v_unused_1497_);
v___x_1488_ = v_a_1481_;
v_isShared_1489_ = v_isSharedCheck_1496_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snd_1486_);
lean_dec(v_a_1481_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1496_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_fst_1485_);
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_fst_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_snd_1486_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1491_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1474_);
v_a_1499_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1480_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1480_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1509_ = lean_ctor_get(v_r_1473_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_r_1473_, 1);
v___x_1510_ = lean_box(0);
v___x_1511_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_1469_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; 
v_unused_1519_ = lean_ctor_get(v___x_1511_, 0);
lean_dec(v_unused_1519_);
v___x_1513_ = v___x_1511_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v___x_1511_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set_tag(v___x_1513_, 1);
lean_ctor_set(v___x_1513_, 0, v_a_1509_);
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1509_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1509_);
v_a_1520_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1511_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1511_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(lean_object* v_x_1533_, lean_object* v_isExporting_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v_isExporting_boxed_1541_; lean_object* v_res_1542_; 
v_isExporting_boxed_1541_ = lean_unbox(v_isExporting_1534_);
v_res_1542_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1533_, v_isExporting_boxed_1541_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(lean_object* v_00_u03b1_1543_, lean_object* v_x_1544_, uint8_t v_isExporting_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_1544_, v_isExporting_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_x_1554_, lean_object* v_isExporting_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_isExporting_boxed_1562_; lean_object* v_res_1563_; 
v_isExporting_boxed_1562_ = lean_unbox(v_isExporting_1555_);
v_res_1563_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_1553_, v_x_1554_, v_isExporting_boxed_1562_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(lean_object* v_opt_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_toCold_1568_; lean_object* v_options_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_toCold_1568_ = lean_ctor_get(v___y_1566_, 0);
v_options_1569_ = lean_ctor_get(v_toCold_1568_, 2);
v___x_1570_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_1569_, v_opt_1564_);
v___x_1571_ = lean_box(v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___y_1565_);
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
lean_object* v_toCold_1587_; lean_object* v_ref_1588_; lean_object* v___x_1589_; lean_object* v_env_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_toCold_1587_ = lean_ctor_get(v___y_1584_, 0);
v_ref_1588_ = lean_ctor_get(v___y_1584_, 2);
v___x_1589_ = lean_st_ref_get(v___y_1585_);
v_env_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc_ref(v_env_1590_);
lean_dec(v___x_1589_);
v___x_1591_ = lean_st_ref_get(v___y_1583_);
v___x_1592_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1582_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1652_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1652_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1652_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_lctx_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1650_; 
v_lctx_1597_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1591_, 1);
lean_dec(v_unused_1651_);
v___x_1599_ = v___x_1591_;
v_isShared_1600_ = v_isSharedCheck_1650_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_lctx_1597_);
lean_dec(v___x_1591_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1650_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_options_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v_options_1601_ = lean_ctor_get(v_toCold_1587_, 2);
v___x_1602_ = lean_unbox(v_a_1593_);
lean_dec(v_a_1593_);
v___x_1603_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1597_, v___x_1602_);
lean_dec_ref(v_lctx_1597_);
v___x_1604_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
lean_inc_ref(v_options_1601_);
v___x_1605_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1605_, 0, v_env_1590_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
lean_ctor_set(v___x_1605_, 2, v___x_1603_);
lean_ctor_set(v___x_1605_, 3, v_options_1601_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 3);
lean_ctor_set(v___x_1599_, 1, v_msg_1580_);
lean_ctor_set(v___x_1599_, 0, v___x_1605_);
v___x_1607_ = v___x_1599_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_msg_1580_);
v___x_1607_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v_traceState_1609_; lean_object* v_env_1610_; lean_object* v_nextMacroScope_1611_; lean_object* v_ngen_1612_; lean_object* v_auxDeclNGen_1613_; lean_object* v_cache_1614_; lean_object* v_messages_1615_; lean_object* v_infoState_1616_; lean_object* v_snapshotTasks_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1648_; 
v___x_1608_ = lean_st_ref_take(v___y_1585_);
v_traceState_1609_ = lean_ctor_get(v___x_1608_, 4);
v_env_1610_ = lean_ctor_get(v___x_1608_, 0);
v_nextMacroScope_1611_ = lean_ctor_get(v___x_1608_, 1);
v_ngen_1612_ = lean_ctor_get(v___x_1608_, 2);
v_auxDeclNGen_1613_ = lean_ctor_get(v___x_1608_, 3);
v_cache_1614_ = lean_ctor_get(v___x_1608_, 5);
v_messages_1615_ = lean_ctor_get(v___x_1608_, 6);
v_infoState_1616_ = lean_ctor_get(v___x_1608_, 7);
v_snapshotTasks_1617_ = lean_ctor_get(v___x_1608_, 8);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1619_ = v___x_1608_;
v_isShared_1620_ = v_isSharedCheck_1648_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snapshotTasks_1617_);
lean_inc(v_infoState_1616_);
lean_inc(v_messages_1615_);
lean_inc(v_cache_1614_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1613_);
lean_inc(v_ngen_1612_);
lean_inc(v_nextMacroScope_1611_);
lean_inc(v_env_1610_);
lean_dec(v___x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1648_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
uint64_t v_tid_1621_; lean_object* v_traces_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1647_; 
v_tid_1621_ = lean_ctor_get_uint64(v_traceState_1609_, sizeof(void*)*1);
v_traces_1622_ = lean_ctor_get(v_traceState_1609_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_traceState_1609_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1624_ = v_traceState_1609_;
v_isShared_1625_ = v_isSharedCheck_1647_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_traces_1622_);
lean_dec(v_traceState_1609_);
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
lean_ctor_set(v___x_1633_, 1, v___x_1607_);
lean_ctor_set(v___x_1633_, 2, v___x_1632_);
lean_inc(v_ref_1588_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_ref_1588_);
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
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_env_1610_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_nextMacroScope_1611_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_ngen_1612_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_auxDeclNGen_1613_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1645_, 5, v_cache_1614_);
lean_ctor_set(v_reuseFailAlloc_1645_, 6, v_messages_1615_);
lean_ctor_set(v_reuseFailAlloc_1645_, 7, v_infoState_1616_);
lean_ctor_set(v_reuseFailAlloc_1645_, 8, v_snapshotTasks_1617_);
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
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1641_);
v___x_1643_ = v___x_1595_;
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
lean_dec(v___x_1591_);
lean_dec_ref(v_env_1590_);
lean_dec(v___y_1581_);
lean_dec_ref(v_msg_1580_);
lean_dec(v_cls_1579_);
v_a_1653_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1592_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1592_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(lean_object* v_keys_1670_, lean_object* v_i_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = lean_array_get_size(v_keys_1670_);
v___x_1674_ = lean_nat_dec_lt(v_i_1671_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_dec(v_i_1671_);
return v___x_1674_;
}
else
{
lean_object* v_k_x27_1675_; uint8_t v___x_1676_; 
v_k_x27_1675_ = lean_array_fget_borrowed(v_keys_1670_, v_i_1671_);
v___x_1676_ = l_Lean_instBEqExtraModUse_beq(v_k_1672_, v_k_x27_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_add(v_i_1671_, v___x_1677_);
lean_dec(v_i_1671_);
v_i_1671_ = v___x_1678_;
goto _start;
}
else
{
lean_dec(v_i_1671_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object* v_keys_1680_, lean_object* v_i_1681_, lean_object* v_k_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_1680_, v_i_1681_, v_k_1682_);
lean_dec_ref(v_k_1682_);
lean_dec_ref(v_keys_1680_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1685_, size_t v_x_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v_es_1688_; lean_object* v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; lean_object* v_j_1692_; lean_object* v___x_1693_; 
v_es_1688_ = lean_ctor_get(v_x_1685_, 0);
v___x_1689_ = lean_box(2);
v___x_1690_ = ((size_t)31ULL);
v___x_1691_ = lean_usize_land(v_x_1686_, v___x_1690_);
v_j_1692_ = lean_usize_to_nat(v___x_1691_);
v___x_1693_ = lean_array_get_borrowed(v___x_1689_, v_es_1688_, v_j_1692_);
lean_dec(v_j_1692_);
switch(lean_obj_tag(v___x_1693_))
{
case 0:
{
lean_object* v_key_1694_; uint8_t v___x_1695_; 
v_key_1694_ = lean_ctor_get(v___x_1693_, 0);
v___x_1695_ = l_Lean_instBEqExtraModUse_beq(v_x_1687_, v_key_1694_);
return v___x_1695_;
}
case 1:
{
lean_object* v_node_1696_; size_t v___x_1697_; size_t v___x_1698_; 
v_node_1696_ = lean_ctor_get(v___x_1693_, 0);
v___x_1697_ = ((size_t)5ULL);
v___x_1698_ = lean_usize_shift_right(v_x_1686_, v___x_1697_);
v_x_1685_ = v_node_1696_;
v_x_1686_ = v___x_1698_;
goto _start;
}
default: 
{
uint8_t v___x_1700_; 
v___x_1700_ = 0;
return v___x_1700_;
}
}
}
else
{
lean_object* v_ks_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_ks_1701_ = lean_ctor_get(v_x_1685_, 0);
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_1701_, v___x_1702_, v_x_1687_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
size_t v_x_26551__boxed_1707_; uint8_t v_res_1708_; lean_object* v_r_1709_; 
v_x_26551__boxed_1707_ = lean_unbox_usize(v_x_1705_);
lean_dec(v_x_1705_);
v_res_1708_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1704_, v_x_26551__boxed_1707_, v_x_1706_);
lean_dec_ref(v_x_1706_);
lean_dec_ref(v_x_1704_);
v_r_1709_ = lean_box(v_res_1708_);
return v_r_1709_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
uint64_t v___x_1712_; size_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = l_Lean_instHashableExtraModUse_hash(v_x_1711_);
v___x_1713_ = lean_uint64_to_usize(v___x_1712_);
v___x_1714_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_1710_, v___x_1713_, v_x_1711_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
uint8_t v_res_1717_; lean_object* v_r_1718_; 
v_res_1717_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_1715_, v_x_1716_);
lean_dec_ref(v_x_1716_);
lean_dec_ref(v_x_1715_);
v_r_1718_ = lean_box(v_res_1717_);
return v_r_1718_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1719_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4));
v___x_1730_ = l_Lean_stringToMessageData(v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v_cls_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_cls_1731_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2));
v___x_1732_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4));
v___x_1733_ = l_Lean_Name_append(v___x_1732_, v_cls_1731_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9));
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11));
v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(lean_object* v_mod_1744_, uint8_t v_isMeta_1745_, lean_object* v_hint_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_env_1755_; uint8_t v_isExporting_1756_; lean_object* v_entry_1757_; lean_object* v___x_1758_; lean_object* v_env_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1753_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0);
v___x_1754_ = lean_st_ref_get(v___y_1751_);
v_env_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_ref(v_env_1755_);
lean_dec(v___x_1754_);
v_isExporting_1756_ = lean_ctor_get_uint8(v_env_1755_, sizeof(void*)*8);
lean_dec_ref(v_env_1755_);
lean_inc(v_mod_1744_);
v_entry_1757_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1757_, 0, v_mod_1744_);
lean_ctor_set_uint8(v_entry_1757_, sizeof(void*)*1, v_isExporting_1756_);
lean_ctor_set_uint8(v_entry_1757_, sizeof(void*)*1 + 1, v_isMeta_1745_);
v___x_1758_ = lean_st_ref_get(v___y_1751_);
v_env_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_ref(v_env_1759_);
lean_dec(v___x_1758_);
v___x_1760_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1761_ = lean_box(1);
v___x_1762_ = lean_box(0);
v___x_1791_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1753_, v___x_1760_, v_env_1759_, v___x_1761_, v___x_1762_);
v___x_1792_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_1791_, v_entry_1757_);
lean_dec(v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v_toCold_1793_; lean_object* v_options_1794_; uint8_t v_hasTrace_1795_; 
v_toCold_1793_ = lean_ctor_get(v___y_1750_, 0);
v_options_1794_ = lean_ctor_get(v_toCold_1793_, 2);
v_hasTrace_1795_ = lean_ctor_get_uint8(v_options_1794_, sizeof(void*)*1);
if (v_hasTrace_1795_ == 0)
{
lean_dec(v_hint_1746_);
lean_dec(v_mod_1744_);
v___y_1764_ = v___y_1747_;
v___y_1765_ = v___y_1751_;
goto v___jp_1763_;
}
else
{
lean_object* v_inheritedTraceOptions_1796_; lean_object* v_cls_1797_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_inheritedTraceOptions_1796_ = lean_ctor_get(v_toCold_1793_, 11);
v_cls_1797_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2));
v___x_1819_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
v___x_1820_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1796_, v_options_1794_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec(v_hint_1746_);
lean_dec(v_mod_1744_);
v___y_1764_ = v___y_1747_;
v___y_1765_ = v___y_1751_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1821_; lean_object* v___y_1823_; 
v___x_1821_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
if (v_isExporting_1756_ == 0)
{
lean_object* v___x_1830_; 
v___x_1830_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15));
v___y_1823_ = v___x_1830_;
goto v___jp_1822_;
}
else
{
lean_object* v___x_1831_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16));
v___y_1823_ = v___x_1831_;
goto v___jp_1822_;
}
v___jp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_inc_ref(v___y_1823_);
v___x_1824_ = l_Lean_stringToMessageData(v___y_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1821_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
if (v_isMeta_1745_ == 0)
{
lean_object* v___x_1828_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13));
v___y_1806_ = v___x_1827_;
v___y_1807_ = v___x_1828_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14));
v___y_1806_ = v___x_1827_;
v___y_1807_ = v___x_1829_;
goto v___jp_1805_;
}
}
}
v___jp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___y_1799_);
lean_ctor_set(v___x_1801_, 1, v___y_1800_);
v___x_1802_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_1797_, v___x_1801_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v_snd_1804_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v_snd_1804_ = lean_ctor_get(v_a_1803_, 1);
lean_inc(v_snd_1804_);
lean_dec(v_a_1803_);
v___y_1764_ = v_snd_1804_;
v___y_1765_ = v___y_1751_;
goto v___jp_1763_;
}
else
{
lean_dec_ref_known(v_entry_1757_, 1);
return v___x_1802_;
}
}
v___jp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
lean_inc_ref(v___y_1807_);
v___x_1808_ = l_Lean_stringToMessageData(v___y_1807_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___y_1806_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Lean_MessageData_ofName(v_mod_1744_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Name_isAnonymous(v_hint_1746_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
v___x_1816_ = l_Lean_MessageData_ofName(v_hint_1746_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___y_1799_ = v___x_1813_;
v___y_1800_ = v___x_1817_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_hint_1746_);
v___x_1818_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7);
v___y_1799_ = v___x_1813_;
v___y_1800_ = v___x_1818_;
goto v___jp_1798_;
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec_ref_known(v_entry_1757_, 1);
lean_dec(v_hint_1746_);
lean_dec(v_mod_1744_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___y_1747_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
v___jp_1763_:
{
lean_object* v___x_1766_; lean_object* v_toEnvExtension_1767_; lean_object* v_env_1768_; lean_object* v_nextMacroScope_1769_; lean_object* v_ngen_1770_; lean_object* v_auxDeclNGen_1771_; lean_object* v_traceState_1772_; lean_object* v_messages_1773_; lean_object* v_infoState_1774_; lean_object* v_snapshotTasks_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1789_; 
v___x_1766_ = lean_st_ref_take(v___y_1765_);
v_toEnvExtension_1767_ = lean_ctor_get(v___x_1760_, 0);
v_env_1768_ = lean_ctor_get(v___x_1766_, 0);
v_nextMacroScope_1769_ = lean_ctor_get(v___x_1766_, 1);
v_ngen_1770_ = lean_ctor_get(v___x_1766_, 2);
v_auxDeclNGen_1771_ = lean_ctor_get(v___x_1766_, 3);
v_traceState_1772_ = lean_ctor_get(v___x_1766_, 4);
v_messages_1773_ = lean_ctor_get(v___x_1766_, 6);
v_infoState_1774_ = lean_ctor_get(v___x_1766_, 7);
v_snapshotTasks_1775_ = lean_ctor_get(v___x_1766_, 8);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1766_, 5);
lean_dec(v_unused_1790_);
v___x_1777_ = v___x_1766_;
v_isShared_1778_ = v_isSharedCheck_1789_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_snapshotTasks_1775_);
lean_inc(v_infoState_1774_);
lean_inc(v_messages_1773_);
lean_inc(v_traceState_1772_);
lean_inc(v_auxDeclNGen_1771_);
lean_inc(v_ngen_1770_);
lean_inc(v_nextMacroScope_1769_);
lean_inc(v_env_1768_);
lean_dec(v___x_1766_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1789_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_asyncMode_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v_asyncMode_1779_ = lean_ctor_get(v_toEnvExtension_1767_, 2);
v___x_1780_ = lean_box(0);
v___x_1781_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1760_, v_env_1768_, v_entry_1757_, v_asyncMode_1779_, v___x_1762_);
v___x_1782_ = lean_obj_once(&l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1, &l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once, _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 5, v___x_1782_);
lean_ctor_set(v___x_1777_, 0, v___x_1781_);
v___x_1784_ = v___x_1777_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_nextMacroScope_1769_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_ngen_1770_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_auxDeclNGen_1771_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_traceState_1772_);
lean_ctor_set(v_reuseFailAlloc_1788_, 5, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1788_, 6, v_messages_1773_);
lean_ctor_set(v_reuseFailAlloc_1788_, 7, v_infoState_1774_);
lean_ctor_set(v_reuseFailAlloc_1788_, 8, v_snapshotTasks_1775_);
v___x_1784_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_st_ref_put(v___y_1765_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1780_);
lean_ctor_set(v___x_1786_, 1, v___y_1764_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(lean_object* v_mod_1835_, lean_object* v_isMeta_1836_, lean_object* v_hint_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
uint8_t v_isMeta_boxed_1844_; lean_object* v_res_1845_; 
v_isMeta_boxed_1844_ = lean_unbox(v_isMeta_1836_);
v_res_1845_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_1835_, v_isMeta_boxed_1844_, v_hint_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
if (lean_obj_tag(v_x_1847_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_box(0);
return v___x_1848_;
}
else
{
lean_object* v_key_1849_; lean_object* v_value_1850_; lean_object* v_tail_1851_; uint8_t v___x_1852_; 
v_key_1849_ = lean_ctor_get(v_x_1847_, 0);
v_value_1850_ = lean_ctor_get(v_x_1847_, 1);
v_tail_1851_ = lean_ctor_get(v_x_1847_, 2);
v___x_1852_ = lean_name_eq(v_key_1849_, v_a_1846_);
if (v___x_1852_ == 0)
{
v_x_1847_ = v_tail_1851_;
goto _start;
}
else
{
lean_object* v___x_1854_; 
lean_inc(v_value_1850_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_value_1850_);
return v___x_1854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1855_, v_x_1856_);
lean_dec(v_x_1856_);
lean_dec(v_a_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(lean_object* v_m_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_buckets_1860_; lean_object* v___x_1861_; uint64_t v___y_1863_; 
v_buckets_1860_ = lean_ctor_get(v_m_1858_, 1);
v___x_1861_ = lean_array_get_size(v_buckets_1860_);
if (lean_obj_tag(v_a_1859_) == 0)
{
uint64_t v___x_1877_; 
v___x_1877_ = 1723ULL;
v___y_1863_ = v___x_1877_;
goto v___jp_1862_;
}
else
{
uint64_t v_hash_1878_; 
v_hash_1878_ = lean_ctor_get_uint64(v_a_1859_, sizeof(void*)*2);
v___y_1863_ = v_hash_1878_;
goto v___jp_1862_;
}
v___jp_1862_:
{
uint64_t v___x_1864_; uint64_t v___x_1865_; uint64_t v_fold_1866_; uint64_t v___x_1867_; uint64_t v___x_1868_; uint64_t v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1864_ = 32ULL;
v___x_1865_ = lean_uint64_shift_right(v___y_1863_, v___x_1864_);
v_fold_1866_ = lean_uint64_xor(v___y_1863_, v___x_1865_);
v___x_1867_ = 16ULL;
v___x_1868_ = lean_uint64_shift_right(v_fold_1866_, v___x_1867_);
v___x_1869_ = lean_uint64_xor(v_fold_1866_, v___x_1868_);
v___x_1870_ = lean_uint64_to_usize(v___x_1869_);
v___x_1871_ = lean_usize_of_nat(v___x_1861_);
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_sub(v___x_1871_, v___x_1872_);
v___x_1874_ = lean_usize_land(v___x_1870_, v___x_1873_);
v___x_1875_ = lean_array_uget_borrowed(v_buckets_1860_, v___x_1874_);
v___x_1876_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_1859_, v___x_1875_);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(lean_object* v_m_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_m_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(lean_object* v___x_1882_, lean_object* v_declName_1883_, lean_object* v_as_1884_, size_t v_sz_1885_, size_t v_i_1886_, lean_object* v_b_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_lt(v_i_1886_, v_sz_1885_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_declName_1883_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_b_1887_);
lean_ctor_set(v___x_1895_, 1, v___y_1888_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v_modules_1898_; lean_object* v___x_1899_; lean_object* v_a_1900_; lean_object* v___x_1901_; lean_object* v_toImport_1902_; lean_object* v_module_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1897_ = l_Lean_Environment_header(v___x_1882_);
v_modules_1898_ = lean_ctor_get(v___x_1897_, 3);
lean_inc_ref(v_modules_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1900_ = lean_array_uget_borrowed(v_as_1884_, v_i_1886_);
v___x_1901_ = lean_array_get(v___x_1899_, v_modules_1898_, v_a_1900_);
lean_dec_ref(v_modules_1898_);
v_toImport_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc_ref(v_toImport_1902_);
lean_dec(v___x_1901_);
v_module_1903_ = lean_ctor_get(v_toImport_1902_, 0);
lean_inc(v_module_1903_);
lean_dec_ref(v_toImport_1902_);
v___x_1904_ = lean_box(0);
v___x_1905_ = 0;
lean_inc(v_declName_1883_);
v___x_1906_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1903_, v___x_1905_, v_declName_1883_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v_snd_1908_; size_t v___x_1909_; size_t v___x_1910_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v_snd_1908_ = lean_ctor_get(v_a_1907_, 1);
lean_inc(v_snd_1908_);
lean_dec(v_a_1907_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1886_, v___x_1909_);
v_i_1886_ = v___x_1910_;
v_b_1887_ = v___x_1904_;
v___y_1888_ = v_snd_1908_;
goto _start;
}
else
{
lean_dec(v_declName_1883_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(lean_object* v___x_1912_, lean_object* v_declName_1913_, lean_object* v_as_1914_, lean_object* v_sz_1915_, lean_object* v_i_1916_, lean_object* v_b_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
size_t v_sz_boxed_1924_; size_t v_i_boxed_1925_; lean_object* v_res_1926_; 
v_sz_boxed_1924_ = lean_unbox_usize(v_sz_1915_);
lean_dec(v_sz_1915_);
v_i_boxed_1925_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_1912_, v_declName_1913_, v_as_1914_, v_sz_boxed_1924_, v_i_boxed_1925_, v_b_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_as_1914_);
lean_dec_ref(v___x_1912_);
return v_res_1926_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(lean_object* v_declName_1930_, uint8_t v_isMeta_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_env_1944_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___x_1969_; 
v___x_1938_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0);
v___x_1939_ = lean_st_ref_get(v___y_1936_);
v_env_1944_ = lean_ctor_get(v___x_1939_, 0);
lean_inc_ref(v_env_1944_);
lean_dec(v___x_1939_);
v___x_1969_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1944_, v_declName_1930_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_dec_ref(v_env_1944_);
lean_dec(v_declName_1930_);
goto v___jp_1940_;
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1971_; lean_object* v_modules_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_val_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = l_Lean_Environment_header(v_env_1944_);
v_modules_1972_ = lean_ctor_get(v___x_1971_, 3);
lean_inc_ref(v_modules_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = lean_array_get_size(v_modules_1972_);
v___x_1974_ = lean_nat_dec_lt(v_val_1970_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v_modules_1972_);
lean_dec(v_val_1970_);
lean_dec_ref(v_env_1944_);
lean_dec(v_declName_1930_);
goto v___jp_1940_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___y_1978_; 
v___x_1975_ = lean_array_fget(v_modules_1972_, v_val_1970_);
lean_dec(v_val_1970_);
lean_dec_ref(v_modules_1972_);
v___x_1976_ = lean_st_ref_get(v___y_1936_);
if (v_isMeta_1931_ == 0)
{
lean_dec(v___x_1976_);
v___y_1978_ = v_isMeta_1931_;
goto v___jp_1977_;
}
else
{
lean_object* v_env_1991_; uint8_t v___x_1992_; 
v_env_1991_ = lean_ctor_get(v___x_1976_, 0);
lean_inc_ref(v_env_1991_);
lean_dec(v___x_1976_);
lean_inc(v_declName_1930_);
v___x_1992_ = l_Lean_isMarkedMeta(v_env_1991_, v_declName_1930_);
if (v___x_1992_ == 0)
{
v___y_1978_ = v_isMeta_1931_;
goto v___jp_1977_;
}
else
{
uint8_t v___x_1993_; 
v___x_1993_ = 0;
v___y_1978_ = v___x_1993_;
goto v___jp_1977_;
}
}
v___jp_1977_:
{
lean_object* v_toImport_1979_; lean_object* v_module_1980_; lean_object* v___x_1981_; 
v_toImport_1979_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref(v_toImport_1979_);
lean_dec(v___x_1975_);
v_module_1980_ = lean_ctor_get(v_toImport_1979_, 0);
lean_inc(v_module_1980_);
lean_dec_ref(v_toImport_1979_);
lean_inc(v_declName_1930_);
v___x_1981_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_1980_, v___y_1978_, v_declName_1930_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v_snd_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v_snd_1983_ = lean_ctor_get(v_a_1982_, 1);
lean_inc(v_snd_1983_);
lean_dec(v_a_1982_);
v___x_1984_ = l_Lean_indirectModUseExt;
v___x_1985_ = lean_box(1);
v___x_1986_ = lean_box(0);
lean_inc_ref(v_env_1944_);
v___x_1987_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1938_, v___x_1984_, v_env_1944_, v___x_1985_, v___x_1986_);
v___x_1988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_1987_, v_declName_1930_);
lean_dec(v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1));
v___y_1946_ = v_snd_1983_;
v___y_1947_ = v___x_1989_;
goto v___jp_1945_;
}
else
{
lean_object* v_val_1990_; 
v_val_1990_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v___x_1988_, 1);
v___y_1946_ = v_snd_1983_;
v___y_1947_ = v_val_1990_;
goto v___jp_1945_;
}
}
else
{
lean_dec_ref(v_env_1944_);
lean_dec(v_declName_1930_);
return v___x_1981_;
}
}
}
}
v___jp_1940_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___y_1932_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
v___jp_1945_:
{
lean_object* v___x_1948_; size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1948_ = lean_box(0);
v_sz_1949_ = lean_array_size(v___y_1947_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_1944_, v_declName_1930_, v___y_1947_, v_sz_1949_, v___x_1950_, v___x_1948_, v___y_1946_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v_env_1944_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1968_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1968_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1968_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_snd_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1966_; 
v_snd_1956_ = lean_ctor_get(v_a_1952_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_a_1952_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v_a_1952_, 0);
lean_dec(v_unused_1967_);
v___x_1958_ = v_a_1952_;
v_isShared_1959_ = v_isSharedCheck_1966_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_snd_1956_);
lean_dec(v_a_1952_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1966_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1948_);
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_snd_1956_);
v___x_1961_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1961_);
v___x_1963_ = v___x_1954_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
else
{
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(lean_object* v_declName_1994_, lean_object* v_isMeta_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v_isMeta_boxed_2002_; lean_object* v_res_2003_; 
v_isMeta_boxed_2002_ = lean_unbox(v_isMeta_1995_);
v_res_2003_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_1994_, v_isMeta_boxed_2002_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2004_, lean_object* v_vals_2005_, lean_object* v_i_2006_, lean_object* v_k_2007_){
_start:
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = lean_array_get_size(v_keys_2004_);
v___x_2009_ = lean_nat_dec_lt(v_i_2006_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec(v_i_2006_);
v___x_2010_ = lean_box(0);
return v___x_2010_;
}
else
{
lean_object* v_k_x27_2011_; uint8_t v___x_2012_; 
v_k_x27_2011_ = lean_array_fget_borrowed(v_keys_2004_, v_i_2006_);
v___x_2012_ = lean_name_eq(v_k_2007_, v_k_x27_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = lean_nat_add(v_i_2006_, v___x_2013_);
lean_dec(v_i_2006_);
v_i_2006_ = v___x_2014_;
goto _start;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_array_fget_borrowed(v_vals_2005_, v_i_2006_);
lean_dec(v_i_2006_);
lean_inc(v___x_2016_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2018_, lean_object* v_vals_2019_, lean_object* v_i_2020_, lean_object* v_k_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2018_, v_vals_2019_, v_i_2020_, v_k_2021_);
lean_dec(v_k_2021_);
lean_dec_ref(v_vals_2019_);
lean_dec_ref(v_keys_2018_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(lean_object* v_x_2023_, size_t v_x_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v_es_2026_; lean_object* v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; lean_object* v_j_2030_; lean_object* v___x_2031_; 
v_es_2026_ = lean_ctor_get(v_x_2023_, 0);
v___x_2027_ = lean_box(2);
v___x_2028_ = ((size_t)31ULL);
v___x_2029_ = lean_usize_land(v_x_2024_, v___x_2028_);
v_j_2030_ = lean_usize_to_nat(v___x_2029_);
v___x_2031_ = lean_array_get_borrowed(v___x_2027_, v_es_2026_, v_j_2030_);
lean_dec(v_j_2030_);
switch(lean_obj_tag(v___x_2031_))
{
case 0:
{
lean_object* v_key_2032_; lean_object* v_val_2033_; uint8_t v___x_2034_; 
v_key_2032_ = lean_ctor_get(v___x_2031_, 0);
v_val_2033_ = lean_ctor_get(v___x_2031_, 1);
v___x_2034_ = lean_name_eq(v_x_2025_, v_key_2032_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_box(0);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; 
lean_inc(v_val_2033_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_val_2033_);
return v___x_2036_;
}
}
case 1:
{
lean_object* v_node_2037_; size_t v___x_2038_; size_t v___x_2039_; 
v_node_2037_ = lean_ctor_get(v___x_2031_, 0);
v___x_2038_ = ((size_t)5ULL);
v___x_2039_ = lean_usize_shift_right(v_x_2024_, v___x_2038_);
v_x_2023_ = v_node_2037_;
v_x_2024_ = v___x_2039_;
goto _start;
}
default: 
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_box(0);
return v___x_2041_;
}
}
}
else
{
lean_object* v_ks_2042_; lean_object* v_vs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_ks_2042_ = lean_ctor_get(v_x_2023_, 0);
v_vs_2043_ = lean_ctor_get(v_x_2023_, 1);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_2042_, v_vs_2043_, v___x_2044_, v_x_2025_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_){
_start:
{
size_t v_x_27089__boxed_2049_; lean_object* v_res_2050_; 
v_x_27089__boxed_2049_ = lean_unbox_usize(v_x_2047_);
lean_dec(v_x_2047_);
v_res_2050_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2046_, v_x_27089__boxed_2049_, v_x_2048_);
lean_dec(v_x_2048_);
lean_dec_ref(v_x_2046_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
uint64_t v___y_2054_; 
if (lean_obj_tag(v_x_2052_) == 0)
{
uint64_t v___x_2057_; 
v___x_2057_ = 1723ULL;
v___y_2054_ = v___x_2057_;
goto v___jp_2053_;
}
else
{
uint64_t v_hash_2058_; 
v_hash_2058_ = lean_ctor_get_uint64(v_x_2052_, sizeof(void*)*2);
v___y_2054_ = v_hash_2058_;
goto v___jp_2053_;
}
v___jp_2053_:
{
size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_uint64_to_usize(v___y_2054_);
v___x_2056_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2051_, v___x_2055_, v_x_2052_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(lean_object* v_x_2059_, lean_object* v_x_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2059_, v_x_2060_);
lean_dec(v_x_2060_);
lean_dec_ref(v_x_2059_);
return v_res_2061_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2062_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1));
v___x_2065_ = l_Lean_stringToMessageData(v___x_2064_);
return v___x_2065_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3));
v___x_2068_ = l_Lean_stringToMessageData(v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5));
v___x_2071_ = l_Lean_stringToMessageData(v___x_2070_);
return v___x_2071_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7));
v___x_2074_ = l_Lean_stringToMessageData(v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(lean_object* v_origDecl_2075_, lean_object* v_init_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_object* v_k_2084_; lean_object* v_l_2085_; lean_object* v_r_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_k_2084_ = lean_ctor_get(v_x_2077_, 1);
lean_inc(v_k_2084_);
v_l_2085_ = lean_ctor_get(v_x_2077_, 3);
lean_inc(v_l_2085_);
v_r_2086_ = lean_ctor_get(v_x_2077_, 4);
lean_inc(v_r_2086_);
lean_dec_ref_known(v_x_2077_, 5);
v___x_2087_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_box(0);
lean_inc_ref(v_origDecl_2075_);
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2075_, v_init_2076_, v_l_2085_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v_snd_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2212_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v_snd_2092_ = lean_ctor_get(v_a_2091_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_a_2091_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v_a_2091_, 0);
lean_dec(v_unused_2213_);
v___x_2094_ = v_a_2091_;
v_isShared_2095_ = v_isSharedCheck_2212_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_snd_2092_);
lean_dec(v_a_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2212_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_NameSet_contains(v_snd_2092_, v_k_2084_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_env_2100_; lean_object* v___x_2101_; lean_object* v_toEnvExtension_2102_; lean_object* v_asyncMode_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2097_ = 1;
lean_inc(v_k_2084_);
v___x_2098_ = l_Lean_NameSet_insert(v_snd_2092_, v_k_2084_);
v___x_2099_ = lean_st_ref_get(v___y_2082_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
v___x_2101_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2102_ = lean_ctor_get(v___x_2101_, 0);
v_asyncMode_2103_ = lean_ctor_get(v_toEnvExtension_2102_, 2);
v___x_2104_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2087_, v___x_2101_, v_env_2100_, v_asyncMode_2103_, v___x_2089_);
v___x_2105_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_2104_, v_k_2084_);
lean_dec(v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 1)
{
lean_object* v_val_2106_; lean_object* v___x_2107_; 
lean_del_object(v___x_2094_);
lean_dec(v_k_2084_);
v_val_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_n(v_val_2106_, 2);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_val_2106_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; uint8_t v___y_2110_; lean_object* v_toSignature_2124_; lean_object* v_name_2125_; uint8_t v___x_2126_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_toSignature_2124_ = lean_ctor_get(v_val_2106_, 0);
v_name_2125_ = lean_ctor_get(v_toSignature_2124_, 0);
v___x_2126_ = l_Lean_isPrivateName(v_name_2125_);
if (v___x_2126_ == 0)
{
lean_dec(v_a_2108_);
v___y_2110_ = v___x_2096_;
goto v___jp_2109_;
}
else
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_unbox(v_a_2108_);
lean_dec(v_a_2108_);
v___y_2110_ = v___x_2127_;
goto v___jp_2109_;
}
v___jp_2109_:
{
if (v___y_2110_ == 0)
{
lean_dec(v_val_2106_);
v_init_2076_ = v___x_2088_;
v_x_2077_ = v_r_2086_;
v___y_2078_ = v___x_2098_;
goto _start;
}
else
{
lean_object* v___x_2112_; 
lean_inc_ref(v_origDecl_2075_);
v___x_2112_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2075_, v_val_2106_, v___x_2098_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v_snd_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v_snd_2114_ = lean_ctor_get(v_a_2113_, 1);
lean_inc(v_snd_2114_);
lean_dec(v_a_2113_);
v_init_2076_ = v___x_2088_;
v_x_2077_ = v_r_2086_;
v___y_2078_ = v_snd_2114_;
goto _start;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_r_2086_);
lean_dec_ref(v_origDecl_2075_);
v_a_2116_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2112_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2112_);
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
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_val_2106_);
lean_dec(v___x_2098_);
lean_dec(v_r_2086_);
lean_dec_ref(v_origDecl_2075_);
v_a_2128_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2107_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2107_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v___x_2136_; lean_object* v_env_2137_; lean_object* v___x_2138_; 
lean_dec(v___x_2105_);
v___x_2136_ = lean_st_ref_get(v___y_2082_);
v_env_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc_ref(v_env_2137_);
lean_dec(v___x_2136_);
v___x_2138_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2137_, v_k_2084_);
lean_dec_ref(v_env_2137_);
if (lean_obj_tag(v___x_2138_) == 1)
{
lean_object* v_val_2139_; lean_object* v___x_2172_; uint8_t v___y_2182_; lean_object* v_env_2202_; lean_object* v___x_2203_; lean_object* v_modules_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_val_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2172_ = lean_st_ref_get(v___y_2082_);
v_env_2202_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_ref(v_env_2202_);
lean_dec(v___x_2172_);
v___x_2203_ = l_Lean_Environment_header(v_env_2202_);
lean_dec_ref(v_env_2202_);
v_modules_2204_ = lean_ctor_get(v___x_2203_, 3);
lean_inc_ref(v_modules_2204_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = lean_array_get_size(v_modules_2204_);
v___x_2206_ = lean_nat_dec_lt(v_val_2139_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_dec_ref(v_modules_2204_);
v___y_2182_ = v___x_2096_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2207_; lean_object* v_toImport_2208_; uint8_t v_isExported_2209_; 
v___x_2207_ = lean_array_fget(v_modules_2204_, v_val_2139_);
lean_dec_ref(v_modules_2204_);
v_toImport_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_toImport_2208_);
lean_dec(v___x_2207_);
v_isExported_2209_ = lean_ctor_get_uint8(v_toImport_2208_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2208_);
if (v_isExported_2209_ == 0)
{
goto v___jp_2173_;
}
else
{
v___y_2182_ = v___x_2096_;
goto v___jp_2181_;
}
}
v___jp_2140_:
{
lean_object* v___x_2141_; lean_object* v_toSignature_2142_; lean_object* v_env_2143_; lean_object* v_name_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2141_ = lean_st_ref_get(v___y_2082_);
v_toSignature_2142_ = lean_ctor_get(v_origDecl_2075_, 0);
lean_inc_ref(v_toSignature_2142_);
lean_dec_ref(v_origDecl_2075_);
v_env_2143_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_ref(v_env_2143_);
lean_dec(v___x_2141_);
v_name_2144_ = lean_ctor_get(v_toSignature_2142_, 0);
lean_inc(v_name_2144_);
lean_dec_ref(v_toSignature_2142_);
v___x_2145_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
v___x_2146_ = l_Lean_MessageData_ofConstName(v_name_2144_, v___x_2096_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 7);
lean_ctor_set(v___x_2094_, 1, v___x_2146_);
lean_ctor_set(v___x_2094_, 0, v___x_2145_);
v___x_2148_ = v___x_2094_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v___x_2149_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Lean_MessageData_ofConstName(v_k_2084_, v___x_2096_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_Environment_header(v_env_2143_);
lean_dec_ref(v_env_2143_);
v___x_2156_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2155_);
v___x_2157_ = lean_array_get(v___x_2089_, v___x_2156_, v_val_2139_);
lean_dec(v_val_2139_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = l_Lean_MessageData_ofName(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2154_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_2161_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
v___jp_2173_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_a_2176_; lean_object* v_fst_2177_; uint8_t v___x_2178_; 
v___x_2174_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2175_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v___x_2174_, v___x_2098_, v___y_2081_);
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2175_);
v_fst_2177_ = lean_ctor_get(v_a_2176_, 0);
v___x_2178_ = lean_unbox(v_fst_2177_);
if (v___x_2178_ == 0)
{
lean_dec(v_a_2176_);
lean_dec(v_r_2086_);
goto v___jp_2140_;
}
else
{
if (v___x_2096_ == 0)
{
lean_object* v_snd_2179_; 
lean_dec(v_val_2139_);
lean_del_object(v___x_2094_);
lean_dec(v_k_2084_);
v_snd_2179_ = lean_ctor_get(v_a_2176_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_a_2176_);
v_init_2076_ = v___x_2088_;
v_x_2077_ = v_r_2086_;
v___y_2078_ = v_snd_2179_;
goto _start;
}
else
{
lean_dec(v_a_2176_);
lean_dec(v_r_2086_);
goto v___jp_2140_;
}
}
}
v___jp_2181_:
{
if (v___y_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v_env_2184_; uint8_t v___x_2185_; uint8_t v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_val_2139_);
lean_del_object(v___x_2094_);
v___x_2183_ = lean_st_ref_get(v___y_2082_);
v_env_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_ref(v_env_2184_);
lean_dec(v___x_2183_);
lean_inc(v_k_2084_);
v___x_2185_ = l_Lean_getIRPhases(v_env_2184_, v_k_2084_);
v___x_2186_ = 1;
v___x_2187_ = l_Lean_instBEqIRPhases_beq(v___x_2185_, v___x_2186_);
v___x_2188_ = lean_box(v___x_2187_);
v___x_2189_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed), 8, 2);
lean_closure_set(v___x_2189_, 0, v_k_2084_);
lean_closure_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_2189_, v___x_2097_, v___x_2098_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v_snd_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v_snd_2192_ = lean_ctor_get(v_a_2191_, 1);
lean_inc(v_snd_2192_);
lean_dec(v_a_2191_);
v_init_2076_ = v___x_2088_;
v_x_2077_ = v_r_2086_;
v___y_2078_ = v_snd_2192_;
goto _start;
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_r_2086_);
lean_dec_ref(v_origDecl_2075_);
v_a_2194_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2190_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2190_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
goto v___jp_2173_;
}
}
}
else
{
lean_dec(v___x_2138_);
lean_del_object(v___x_2094_);
lean_dec(v_k_2084_);
v_init_2076_ = v___x_2088_;
v_x_2077_ = v_r_2086_;
v___y_2078_ = v___x_2098_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2094_);
lean_dec(v_k_2084_);
v_init_2076_ = v___x_2088_;
v_x_2077_ = v_r_2086_;
v___y_2078_ = v_snd_2092_;
goto _start;
}
}
}
else
{
lean_dec(v_r_2086_);
lean_dec(v_k_2084_);
lean_dec_ref(v_origDecl_2075_);
return v___x_2090_;
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v_origDecl_2075_);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_init_2076_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___y_2078_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(uint8_t v___x_2217_, lean_object* v_origDecl_2218_, lean_object* v_code_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = l_Lean_NameSet_empty;
v___x_2227_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_2217_, v_code_2219_, v___x_2226_);
v___x_2228_ = lean_box(0);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2218_, v___x_2228_, v___x_2227_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2246_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2246_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2246_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_snd_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2244_; 
v_snd_2234_ = lean_ctor_get(v_a_2230_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v_a_2230_, 0);
lean_dec(v_unused_2245_);
v___x_2236_ = v_a_2230_;
v_isShared_2237_ = v_isSharedCheck_2244_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2234_);
lean_dec(v_a_2230_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2244_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2228_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_snd_2234_);
v___x_2239_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2239_);
v___x_2241_ = v___x_2232_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2229_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2229_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(lean_object* v___x_2255_, lean_object* v_origDecl_2256_, lean_object* v_code_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v___x_27169__boxed_2264_; lean_object* v_res_2265_; 
v___x_27169__boxed_2264_ = lean_unbox(v___x_2255_);
v_res_2265_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_27169__boxed_2264_, v_origDecl_2256_, v_code_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(lean_object* v_origDecl_2266_, lean_object* v_decl_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_value_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; 
v_value_2274_ = lean_ctor_get(v_decl_2267_, 1);
lean_inc_ref(v_value_2274_);
lean_dec_ref(v_decl_2267_);
v___x_2275_ = 0;
v___x_2276_ = lean_box(v___x_2275_);
v___f_2277_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2277_, 0, v___x_2276_);
lean_closure_set(v___f_2277_, 1, v_origDecl_2266_);
v___x_2278_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_2277_, v_value_2274_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(lean_object* v_origDecl_2279_, lean_object* v_decl_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_2279_, v_decl_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(lean_object* v_origDecl_2288_, lean_object* v_init_2289_, lean_object* v_x_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_2288_, v_init_2289_, v_x_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(lean_object* v_00_u03b2_2298_, lean_object* v_x_2299_, lean_object* v_x_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_2299_, v_x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(lean_object* v_00_u03b2_2302_, lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_2302_, v_x_2303_, v_x_2304_);
lean_dec(v_x_2304_);
lean_dec_ref(v_x_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(lean_object* v_opt_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_2306_, v___y_2307_, v___y_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(lean_object* v_opt_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v_opt_2314_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(lean_object* v_00_u03b2_2322_, lean_object* v_x_2323_, size_t v_x_2324_, lean_object* v_x_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_2323_, v_x_2324_, v_x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
size_t v_x_27582__boxed_2331_; lean_object* v_res_2332_; 
v_x_27582__boxed_2331_ = lean_unbox_usize(v_x_2329_);
lean_dec(v_x_2329_);
v_res_2332_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_2327_, v_x_2328_, v_x_27582__boxed_2331_, v_x_2330_);
lean_dec(v_x_2330_);
lean_dec_ref(v_x_2328_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(lean_object* v_00_u03b2_2333_, lean_object* v_m_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_2334_, v_a_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2337_, lean_object* v_m_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_2337_, v_m_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_m_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2341_, lean_object* v_keys_2342_, lean_object* v_vals_2343_, lean_object* v_heq_2344_, lean_object* v_i_2345_, lean_object* v_k_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_2342_, v_vals_2343_, v_i_2345_, v_k_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2348_, lean_object* v_keys_2349_, lean_object* v_vals_2350_, lean_object* v_heq_2351_, lean_object* v_i_2352_, lean_object* v_k_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_2348_, v_keys_2349_, v_vals_2350_, v_heq_2351_, v_i_2352_, v_k_2353_);
lean_dec(v_k_2353_);
lean_dec_ref(v_vals_2350_);
lean_dec_ref(v_keys_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2355_, lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_2356_, v_x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_){
_start:
{
uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_res_2362_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_2359_, v_x_2360_, v_x_2361_);
lean_dec_ref(v_x_2361_);
lean_dec_ref(v_x_2360_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_2364_, lean_object* v_a_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_2365_, v_x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2368_, lean_object* v_a_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_2368_, v_a_2369_, v_x_2370_);
lean_dec(v_x_2370_);
lean_dec(v_a_2369_);
return v_res_2371_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2372_, lean_object* v_x_2373_, size_t v_x_2374_, lean_object* v_x_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_2373_, v_x_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
size_t v_x_27610__boxed_2381_; uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_x_27610__boxed_2381_ = lean_unbox_usize(v_x_2379_);
lean_dec(v_x_2379_);
v_res_2382_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_2377_, v_x_2378_, v_x_27610__boxed_2381_, v_x_2380_);
lean_dec_ref(v_x_2380_);
lean_dec_ref(v_x_2378_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_2384_, lean_object* v_keys_2385_, lean_object* v_vals_2386_, lean_object* v_heq_2387_, lean_object* v_i_2388_, lean_object* v_k_2389_){
_start:
{
uint8_t v___x_2390_; 
v___x_2390_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_2385_, v_i_2388_, v_k_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2391_, lean_object* v_keys_2392_, lean_object* v_vals_2393_, lean_object* v_heq_2394_, lean_object* v_i_2395_, lean_object* v_k_2396_){
_start:
{
uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_res_2397_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_2391_, v_keys_2392_, v_vals_2393_, v_heq_2394_, v_i_2395_, v_k_2396_);
lean_dec_ref(v_k_2396_);
lean_dec_ref(v_vals_2393_);
lean_dec_ref(v_keys_2392_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(lean_object* v_as_2399_, size_t v_sz_2400_, size_t v_i_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_a_2409_; uint8_t v___x_2413_; 
v___x_2413_ = lean_usize_dec_lt(v_i_2401_, v_sz_2400_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_b_2402_);
return v___x_2414_;
}
else
{
lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_box(0);
v_a_2416_ = lean_array_uget_borrowed(v_as_2399_, v_i_2401_);
lean_inc(v_a_2416_);
v___x_2417_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_a_2416_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_toSignature_2418_; lean_object* v_a_2419_; lean_object* v_name_2420_; uint8_t v___x_2421_; 
v_toSignature_2418_ = lean_ctor_get(v_a_2416_, 0);
v_a_2419_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2417_, 1);
v_name_2420_ = lean_ctor_get(v_toSignature_2418_, 0);
v___x_2421_ = l_Lean_isPrivateName(v_name_2420_);
if (v___x_2421_ == 0)
{
uint8_t v___x_2422_; 
v___x_2422_ = lean_unbox(v_a_2419_);
lean_dec(v_a_2419_);
if (v___x_2422_ == 0)
{
v_a_2409_ = v___x_2415_;
goto v___jp_2408_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = lean_st_ref_get(v___y_2406_);
lean_dec(v___x_2423_);
v___x_2424_ = l_Lean_NameSet_empty;
lean_inc_n(v_a_2416_, 2);
v___x_2425_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_2416_, v_a_2416_, v___x_2424_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_dec_ref_known(v___x_2425_, 1);
v_a_2409_ = v___x_2415_;
goto v___jp_2408_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
else
{
lean_dec(v_a_2419_);
v_a_2409_ = v___x_2415_;
goto v___jp_2408_;
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
v_a_2434_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2417_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2417_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
v___jp_2408_:
{
size_t v___x_2410_; size_t v___x_2411_; 
v___x_2410_ = ((size_t)1ULL);
v___x_2411_ = lean_usize_add(v_i_2401_, v___x_2410_);
v_i_2401_ = v___x_2411_;
v_b_2402_ = v_a_2409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(lean_object* v_as_2442_, lean_object* v_sz_2443_, lean_object* v_i_2444_, lean_object* v_b_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
size_t v_sz_boxed_2451_; size_t v_i_boxed_2452_; lean_object* v_res_2453_; 
v_sz_boxed_2451_ = lean_unbox_usize(v_sz_2443_);
lean_dec(v_sz_2443_);
v_i_boxed_2452_ = lean_unbox_usize(v_i_2444_);
lean_dec(v_i_2444_);
v_res_2453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_2442_, v_sz_boxed_2451_, v_i_boxed_2452_, v_b_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec_ref(v_as_2442_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(lean_object* v_decls_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v_env_2461_; lean_object* v___x_2462_; uint8_t v_isModule_2463_; 
v___x_2460_ = lean_st_ref_get(v___y_2458_);
v_env_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_ref(v_env_2461_);
lean_dec(v___x_2460_);
v___x_2462_ = l_Lean_Environment_header(v_env_2461_);
lean_dec_ref(v_env_2461_);
v_isModule_2463_ = lean_ctor_get_uint8(v___x_2462_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2462_);
if (v_isModule_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_decls_2454_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; size_t v_sz_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_box(0);
v_sz_2466_ = lean_array_size(v_decls_2454_);
v___x_2467_ = ((size_t)0ULL);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_2454_, v_sz_2466_, v___x_2467_, v___x_2465_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2468_, 0);
lean_dec(v_unused_2476_);
v___x_2470_ = v___x_2468_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v___x_2468_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v_decls_2454_);
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_decls_2454_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_decls_2454_);
v_a_2477_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2468_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2468_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(lean_object* v_decls_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(v_decls_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2491_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0));
v___x_2505_ = l_Lean_stringToMessageData(v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(uint8_t v_phase_2506_, uint8_t v___x_2507_, lean_object* v_as_2508_, size_t v_sz_2509_, size_t v_i_2510_, lean_object* v_b_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_a_2518_; uint8_t v___x_2522_; 
v___x_2522_ = lean_usize_dec_lt(v_i_2510_, v_sz_2509_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_b_2511_);
return v___x_2523_;
}
else
{
lean_object* v___x_2524_; lean_object* v_a_2525_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___x_2533_; lean_object* v_toSignature_2534_; lean_object* v_env_2535_; lean_object* v_name_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2524_ = lean_box(0);
v_a_2525_ = lean_array_uget_borrowed(v_as_2508_, v_i_2510_);
v___x_2533_ = lean_st_ref_get(v___y_2515_);
v_toSignature_2534_ = lean_ctor_get(v_a_2525_, 0);
v_env_2535_ = lean_ctor_get(v___x_2533_, 0);
lean_inc_ref(v_env_2535_);
lean_dec(v___x_2533_);
v_name_2536_ = lean_ctor_get(v_toSignature_2534_, 0);
v___x_2537_ = l_Lean_Environment_setExporting(v_env_2535_, v___x_2507_);
lean_inc(v_name_2536_);
v___x_2538_ = l_Lean_Environment_contains(v___x_2537_, v_name_2536_, v___x_2507_);
if (v___x_2538_ == 0)
{
v_a_2518_ = v___x_2524_;
goto v___jp_2517_;
}
else
{
lean_object* v_toCold_2539_; lean_object* v_options_2540_; uint8_t v_hasTrace_2541_; 
v_toCold_2539_ = lean_ctor_get(v___y_2514_, 0);
v_options_2540_ = lean_ctor_get(v_toCold_2539_, 2);
v_hasTrace_2541_ = lean_ctor_get_uint8(v_options_2540_, sizeof(void*)*1);
if (v_hasTrace_2541_ == 0)
{
v___y_2527_ = v___y_2512_;
v___y_2528_ = v___y_2513_;
v___y_2529_ = v___y_2514_;
v___y_2530_ = v___y_2515_;
goto v___jp_2526_;
}
else
{
lean_object* v_inheritedTraceOptions_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_inheritedTraceOptions_2542_ = lean_ctor_get(v_toCold_2539_, 11);
v___x_2543_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2544_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
v___x_2545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2542_, v_options_2540_, v___x_2544_);
if (v___x_2545_ == 0)
{
v___y_2527_ = v___y_2512_;
v___y_2528_ = v___y_2513_;
v___y_2529_ = v___y_2514_;
v___y_2530_ = v___y_2515_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2546_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
lean_inc(v_name_2536_);
v___x_2547_ = l_Lean_MessageData_ofName(v_name_2536_);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_2543_, v___x_2550_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_dec_ref_known(v___x_2551_, 1);
v___y_2527_ = v___y_2512_;
v___y_2528_ = v___y_2513_;
v___y_2529_ = v___y_2514_;
v___y_2530_ = v___y_2515_;
goto v___jp_2526_;
}
else
{
return v___x_2551_;
}
}
}
}
v___jp_2526_:
{
uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2506_);
lean_inc(v_a_2525_);
v___x_2532_ = l_Lean_Compiler_LCNF_markDeclPublicRec(v___x_2531_, v_phase_2506_, v_a_2525_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_dec_ref_known(v___x_2532_, 1);
v_a_2518_ = v___x_2524_;
goto v___jp_2517_;
}
else
{
return v___x_2532_;
}
}
}
v___jp_2517_:
{
size_t v___x_2519_; size_t v___x_2520_; 
v___x_2519_ = ((size_t)1ULL);
v___x_2520_ = lean_usize_add(v_i_2510_, v___x_2519_);
v_i_2510_ = v___x_2520_;
v_b_2511_ = v_a_2518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(lean_object* v_phase_2552_, lean_object* v___x_2553_, lean_object* v_as_2554_, lean_object* v_sz_2555_, lean_object* v_i_2556_, lean_object* v_b_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
uint8_t v_phase_boxed_2563_; uint8_t v___x_2240__boxed_2564_; size_t v_sz_boxed_2565_; size_t v_i_boxed_2566_; lean_object* v_res_2567_; 
v_phase_boxed_2563_ = lean_unbox(v_phase_2552_);
v___x_2240__boxed_2564_ = lean_unbox(v___x_2553_);
v_sz_boxed_2565_ = lean_unbox_usize(v_sz_2555_);
lean_dec(v_sz_2555_);
v_i_boxed_2566_ = lean_unbox_usize(v_i_2556_);
lean_dec(v_i_2556_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_2563_, v___x_2240__boxed_2564_, v_as_2554_, v_sz_boxed_2565_, v_i_boxed_2566_, v_b_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec_ref(v_as_2554_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0(uint8_t v_phase_2568_, lean_object* v_decls_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v_env_2576_; lean_object* v___x_2577_; uint8_t v_isModule_2578_; 
v___x_2575_ = lean_st_ref_get(v___y_2573_);
v_env_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_ref(v_env_2576_);
lean_dec(v___x_2575_);
v___x_2577_ = l_Lean_Environment_header(v_env_2576_);
lean_dec_ref(v_env_2576_);
v_isModule_2578_ = lean_ctor_get_uint8(v___x_2577_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2577_);
if (v_isModule_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_decls_2569_);
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v___x_2580_ = lean_box(0);
v_sz_2581_ = lean_array_size(v_decls_2569_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_2568_, v_isModule_2578_, v_decls_2569_, v_sz_2581_, v___x_2582_, v___x_2580_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; 
v_unused_2591_ = lean_ctor_get(v___x_2583_, 0);
lean_dec(v_unused_2591_);
v___x_2585_ = v___x_2583_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_dec(v___x_2583_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v_decls_2569_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_decls_2569_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_decls_2569_);
v_a_2592_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2583_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2583_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(lean_object* v_phase_2600_, lean_object* v_decls_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v_phase_boxed_2607_; lean_object* v_res_2608_; 
v_phase_boxed_2607_ = lean_unbox(v_phase_2600_);
v_res_2608_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(v_phase_boxed_2607_, v_decls_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t v_phase_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2612_ = lean_box(v_phase_2611_);
v___f_2613_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2613_, 0, v___x_2612_);
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = 0;
v___x_2616_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferVisibility___closed__0));
v___x_2617_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2617_, 0, v___x_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
lean_ctor_set(v___x_2617_, 2, v___f_2613_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3, v_phase_2611_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3 + 1, v_phase_2611_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3 + 2, v___x_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferVisibility___boxed(lean_object* v_phase_2618_){
_start:
{
uint8_t v_phase_boxed_2619_; lean_object* v_res_2620_; 
v_phase_boxed_2619_ = lean_unbox(v_phase_2618_);
v_res_2620_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_2619_);
return v_res_2620_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_unsigned_to_nat(3356661454u);
v___x_2673_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2674_ = l_Lean_Name_num___override(v___x_2673_, v___x_2672_);
return v___x_2674_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2677_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2678_ = l_Lean_Name_str___override(v___x_2677_, v___x_2676_);
return v___x_2678_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_));
v___x_2681_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2682_ = l_Lean_Name_str___override(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_unsigned_to_nat(2u);
v___x_2684_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2685_ = l_Lean_Name_num___override(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2687_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2));
v___x_2688_ = 0;
v___x_2689_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
v___x_2690_ = l_Lean_registerTraceClass(v___x_2687_, v___x_2688_, v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
return v_res_2692_;
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
