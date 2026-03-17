// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: public import Lean.Compiler.LCNF.PullLetDecls public import Lean.Compiler.LCNF.CSE public import Lean.Compiler.LCNF.JoinPoints public import Lean.Compiler.LCNF.Specialize public import Lean.Compiler.LCNF.ToMono public import Lean.Compiler.LCNF.LambdaLifting public import Lean.Compiler.LCNF.FloatLetIn public import Lean.Compiler.LCNF.ReduceArity public import Lean.Compiler.LCNF.ElimDeadBranches public import Lean.Compiler.LCNF.StructProjCases public import Lean.Compiler.LCNF.ExtractClosed public import Lean.Compiler.LCNF.Visibility public import Lean.Compiler.LCNF.Simp public import Lean.Compiler.LCNF.ToImpure public import Lean.Compiler.LCNF.PushProj public import Lean.Compiler.LCNF.ResetReuse public import Lean.Compiler.LCNF.SimpCase public import Lean.Compiler.LCNF.InferBorrow public import Lean.Compiler.LCNF.ExplicitBoxing public import Lean.Compiler.LCNF.ExplicitRC public import Lean.Compiler.LCNF.Toposort public import Lean.Compiler.LCNF.ExpandResetReuse public import Lean.Compiler.LCNF.SimpleGroundExpr
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toposortPass;
lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_detectSimpleGround;
lean_object* l_Lean_Compiler_LCNF_pushProj(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_expandResetReuse;
extern lean_object* l_Lean_Compiler_LCNF_explicitRc;
extern lean_object* l_Lean_Compiler_LCNF_explicitBoxing;
extern lean_object* l_Lean_Compiler_LCNF_inferBorrow;
extern lean_object* l_Lean_Compiler_LCNF_simpCase;
lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_insertResetReuse;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toImpure;
extern lean_object* l_Lean_Compiler_LCNF_extractClosed;
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_elimDeadBranches;
lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_lambdaLifting;
lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs;
extern lean_object* l_Lean_Compiler_LCNF_reduceArity;
extern lean_object* l_Lean_Compiler_LCNF_structProjCases;
lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_toMono;
lean_object* l_Lean_Compiler_LCNF_findJoinPoints(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_specialize;
extern lean_object* l_Lean_Compiler_LCNF_checkTemplateVisibility;
extern lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting;
extern lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
extern lean_object* l_Lean_Compiler_LCNF_pullInstances;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_checkMeta(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_init___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_init___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Pass_init___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Pass_init___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Pass_init___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_init___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_init___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_init___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 5, 38, 228, 229, 249, 19, 211)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_init___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_init___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_init___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Pass_init = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_init___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Pass_checkMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Pass_checkMeta___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_checkMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checkMeta"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_checkMeta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 129, 145, 166, 209, 130, 188, 38)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_checkMeta___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_checkMeta___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Pass_trace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Pass_trace___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Pass_trace___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_trace___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_trace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_trace___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_trace___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_trace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_trace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_trace___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_trace___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Pass_saveBase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Pass_saveBase___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "saveBase"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_saveBase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value),LEAN_SCALAR_PTR_LITERAL(140, 135, 216, 56, 38, 218, 93, 87)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_saveBase___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Pass_saveBase = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Pass_saveMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Pass_saveMono___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "saveMono"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_saveMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value),LEAN_SCALAR_PTR_LITERAL(138, 171, 181, 35, 167, 23, 78, 184)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_saveMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Pass_saveMono = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "saveImpure"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 186, 96, 39, 202, 122, 36, 209)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 2, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__0;
static const lean_ctor_object l_Lean_Compiler_LCNF_builtinPassManager___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_builtinPassManager___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__5;
static const lean_ctor_object l_Lean_Compiler_LCNF_builtinPassManager___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_builtinPassManager___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__10;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__11;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__13;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__14;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__15;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__16;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__17;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__18;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__19;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__20;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__21;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__22;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__23;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__24;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__25;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__26;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__27;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__28;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__29;
static lean_once_cell_t l_Lean_Compiler_LCNF_builtinPassManager___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__30;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_builtinPassManager;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "passManagerExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 46, 217, 27, 108, 148, 162, 146)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_passManagerExt;
static lean_once_cell_t l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_addPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cpass"};
static const lean_object* l_Lean_Compiler_LCNF_addPass___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 90, 210, 60, 47, 36, 58, 47)}};
static const lean_object* l_Lean_Compiler_LCNF_addPass___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_addPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PassInstaller"};
static const lean_object* l_Lean_Compiler_LCNF_addPass___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(110, 217, 253, 71, 42, 135, 144, 215)}};
static const lean_object* l_Lean_Compiler_LCNF_addPass___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_addPass___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Passes"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 202, 253, 45, 23, 235, 193, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 87, 67, 6, 155, 120, 131, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 168, 19, 173, 187, 189, 162, 33)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 231, 245, 175, 233, 54, 120, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 34, 48, 120, 254, 109, 127, 221)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 243, 214, 185, 49, 203, 111, 147)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 206, 229, 68, 67, 72, 146, 96)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 154, 255, 212, 182, 226, 77, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 148, 71, 216, 106, 168, 19, 62)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 16, 78, 18, 224, 238, 56, 194)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 193, 133, 172, 26, 85, 3, 133)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__1_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__1_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "compiler passes for the code generator"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 244, 133, 152, 72, 198, 220, 44)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1750802602) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(166, 97, 40, 105, 89, 96, 5, 138)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 48, 139, 28, 194, 37, 217, 233)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 43, 92, 99, 195, 187, 155, 75)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(132, 62, 130, 189, 105, 90, 82, 54)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 254, 187, 91, 177, 170, 7, 67)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(121, 215, 87, 166, 244, 66, 83, 246)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_trace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(234, 222, 109, 191, 39, 198, 145, 230)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_, lean_object* v___y_5_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
lean_inc(v___x_8_);
v___x_9_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v___x_8_, v___y_5_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; size_t v___x_11_; size_t v___x_12_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = ((size_t)1ULL);
v___x_12_ = lean_usize_add(v_i_2_, v___x_11_);
v_i_2_ = v___x_12_;
v_b_4_ = v_a_10_;
goto _start;
}
else
{
return v___x_9_;
}
}
else
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v_b_4_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg___boxed(lean_object* v_as_15_, lean_object* v_i_16_, lean_object* v_stop_17_, lean_object* v_b_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
size_t v_i_boxed_21_; size_t v_stop_boxed_22_; lean_object* v_res_23_; 
v_i_boxed_21_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_22_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_res_23_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_as_15_, v_i_boxed_21_, v_stop_boxed_22_, v_b_18_, v___y_19_);
lean_dec(v___y_19_);
lean_dec_ref(v_as_15_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_init___lam__0(lean_object* v___x_24_, lean_object* v_decls_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___y_32_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_array_get_size(v_decls_25_);
v___x_50_ = lean_nat_dec_lt(v___x_24_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v_decls_25_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_box(0);
v___x_53_ = lean_nat_dec_le(v___x_49_, v___x_49_);
if (v___x_53_ == 0)
{
if (v___x_50_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_decls_25_);
return v___x_54_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_49_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_decls_25_, v___x_55_, v___x_56_, v___x_52_, v___y_29_);
v___y_32_ = v___x_57_;
goto v___jp_31_;
}
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_49_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_decls_25_, v___x_58_, v___x_59_, v___x_52_, v___y_29_);
v___y_32_ = v___x_60_;
goto v___jp_31_;
}
}
v___jp_31_:
{
if (lean_obj_tag(v___y_32_) == 0)
{
lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_isSharedCheck_39_ = !lean_is_exclusive(v___y_32_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v___y_32_, 0);
lean_dec(v_unused_40_);
v___x_34_ = v___y_32_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_dec(v___y_32_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v_decls_25_);
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_decls_25_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec_ref(v_decls_25_);
v_a_41_ = lean_ctor_get(v___y_32_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___y_32_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___y_32_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___y_32_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_init___lam__0___boxed(lean_object* v___x_61_, lean_object* v_decls_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Compiler_LCNF_Pass_init___lam__0(v___x_61_, v_decls_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___x_61_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0(lean_object* v_as_81_, size_t v_i_82_, size_t v_stop_83_, lean_object* v_b_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_as_81_, v_i_82_, v_stop_83_, v_b_84_, v___y_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___boxed(lean_object* v_as_91_, lean_object* v_i_92_, lean_object* v_stop_93_, lean_object* v_b_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
size_t v_i_boxed_100_; size_t v_stop_boxed_101_; lean_object* v_res_102_; 
v_i_boxed_100_ = lean_unbox_usize(v_i_92_);
lean_dec(v_i_92_);
v_stop_boxed_101_ = lean_unbox_usize(v_stop_93_);
lean_dec(v_stop_93_);
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0(v_as_91_, v_i_boxed_100_, v_stop_boxed_101_, v_b_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec_ref(v_as_91_);
return v_res_102_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___closed__0(void){
_start:
{
uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 0;
v___x_104_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0(lean_object* v_as_105_, size_t v_i_106_, size_t v_stop_107_, lean_object* v_b_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_usize_dec_eq(v_i_106_, v_stop_107_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___closed__0);
v___x_116_ = lean_array_uget_borrowed(v_as_105_, v_i_106_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___x_116_);
v___x_117_ = l_Lean_Compiler_LCNF_checkMeta(v___x_115_, v___x_116_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; size_t v___x_119_; size_t v___x_120_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref(v___x_117_);
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_add(v_i_106_, v___x_119_);
v_i_106_ = v___x_120_;
v_b_108_ = v_a_118_;
goto _start;
}
else
{
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v___x_117_;
}
}
else
{
lean_object* v___x_122_; 
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v_b_108_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0___boxed(lean_object* v_as_123_, lean_object* v_i_124_, lean_object* v_stop_125_, lean_object* v_b_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
size_t v_i_boxed_132_; size_t v_stop_boxed_133_; lean_object* v_res_134_; 
v_i_boxed_132_ = lean_unbox_usize(v_i_124_);
lean_dec(v_i_124_);
v_stop_boxed_133_ = lean_unbox_usize(v_stop_125_);
lean_dec(v_stop_125_);
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0(v_as_123_, v_i_boxed_132_, v_stop_boxed_133_, v_b_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec_ref(v_as_123_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___lam__0(lean_object* v___x_135_, lean_object* v_decls_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___y_143_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_array_get_size(v_decls_136_);
v___x_161_ = lean_nat_dec_lt(v___x_135_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v_decls_136_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_nat_dec_le(v___x_160_, v___x_160_);
if (v___x_164_ == 0)
{
if (v___x_161_ == 0)
{
lean_object* v___x_165_; 
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v_decls_136_);
return v___x_165_;
}
else
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_160_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0(v_decls_136_, v___x_166_, v___x_167_, v___x_163_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
v___y_143_ = v___x_168_;
goto v___jp_142_;
}
}
else
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_160_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_checkMeta_spec__0(v_decls_136_, v___x_169_, v___x_170_, v___x_163_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
v___y_143_ = v___x_171_;
goto v___jp_142_;
}
}
v___jp_142_:
{
if (lean_obj_tag(v___y_143_) == 0)
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_isSharedCheck_150_ = !lean_is_exclusive(v___y_143_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v___y_143_, 0);
lean_dec(v_unused_151_);
v___x_145_ = v___y_143_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_dec(v___y_143_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v_decls_136_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_decls_136_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec_ref(v_decls_136_);
v_a_152_ = lean_ctor_get(v___y_143_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___y_143_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___y_143_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___y_143_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_checkMeta___lam__0___boxed(lean_object* v___x_172_, lean_object* v_decls_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Compiler_LCNF_Pass_checkMeta___lam__0(v___x_172_, v_decls_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___x_172_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___lam__0(lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___y_192_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___lam__0___boxed(lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Compiler_LCNF_Pass_trace___lam__0(v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace(uint8_t v_phase_210_){
_start:
{
lean_object* v___f_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___f_211_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_trace___closed__0));
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = 0;
v___x_214_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_trace___closed__2));
v___x_215_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_215_, 0, v___x_212_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___f_211_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*3, v_phase_210_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*3 + 1, v_phase_210_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*3 + 2, v___x_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___boxed(lean_object* v_phase_216_){
_start:
{
uint8_t v_phase_boxed_217_; lean_object* v_res_218_; 
v_phase_boxed_217_ = lean_unbox(v_phase_216_);
v_res_218_ = l_Lean_Compiler_LCNF_Pass_trace(v_phase_boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(size_t v_sz_219_, size_t v_i_220_, lean_object* v_bs_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lean_usize_dec_lt(v_i_220_, v_sz_219_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_bs_221_);
return v___x_226_;
}
else
{
lean_object* v_v_227_; lean_object* v___x_228_; lean_object* v_bs_x27_229_; lean_object* v_a_231_; uint8_t v___x_236_; lean_object* v___x_237_; 
v_v_227_ = lean_array_uget(v_bs_221_, v_i_220_);
v___x_228_ = lean_unsigned_to_nat(0u);
v_bs_x27_229_ = lean_array_uset(v_bs_221_, v_i_220_, v___x_228_);
v___x_236_ = 0;
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
lean_inc(v_v_227_);
v___x_237_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v___x_236_, v_v_227_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref(v___x_237_);
v___x_239_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_a_238_, v___y_223_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_dec_ref(v___x_239_);
v_a_231_ = v_v_227_;
goto v___jp_230_;
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_bs_x27_229_);
lean_dec(v_v_227_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_dec(v_v_227_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_248_; 
v_a_248_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_237_);
v_a_231_ = v_a_248_;
goto v___jp_230_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v_bs_x27_229_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
v_a_249_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_237_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_237_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
v___jp_230_:
{
size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_220_, v___x_232_);
v___x_234_ = lean_array_uset(v_bs_x27_229_, v_i_220_, v_a_231_);
v_i_220_ = v___x_233_;
v_bs_221_ = v___x_234_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg___boxed(lean_object* v_sz_257_, lean_object* v_i_258_, lean_object* v_bs_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
size_t v_sz_boxed_263_; size_t v_i_boxed_264_; lean_object* v_res_265_; 
v_sz_boxed_263_ = lean_unbox_usize(v_sz_257_);
lean_dec(v_sz_257_);
v_i_boxed_264_ = lean_unbox_usize(v_i_258_);
lean_dec(v_i_258_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_boxed_263_, v_i_boxed_264_, v_bs_259_, v___y_260_, v___y_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(lean_object* v_decls_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
size_t v_sz_272_; size_t v___x_273_; lean_object* v___x_274_; 
v_sz_272_ = lean_array_size(v_decls_266_);
v___x_273_ = ((size_t)0ULL);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_272_, v___x_273_, v_decls_266_, v___y_269_, v___y_270_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___lam__0___boxed(lean_object* v_decls_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(v_decls_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(size_t v_sz_293_, size_t v_i_294_, lean_object* v_bs_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_293_, v_i_294_, v_bs_295_, v___y_298_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___boxed(lean_object* v_sz_302_, lean_object* v_i_303_, lean_object* v_bs_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
size_t v_sz_boxed_310_; size_t v_i_boxed_311_; lean_object* v_res_312_; 
v_sz_boxed_310_ = lean_unbox_usize(v_sz_302_);
lean_dec(v_sz_302_);
v_i_boxed_311_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(v_sz_boxed_310_, v_i_boxed_311_, v_bs_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(size_t v_sz_313_, size_t v_i_314_, lean_object* v_bs_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_usize_dec_lt(v_i_314_, v_sz_313_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_bs_315_);
return v___x_320_;
}
else
{
lean_object* v_v_321_; lean_object* v___x_322_; lean_object* v_bs_x27_323_; lean_object* v_a_325_; uint8_t v___x_330_; lean_object* v___x_331_; 
v_v_321_ = lean_array_uget(v_bs_315_, v_i_314_);
v___x_322_ = lean_unsigned_to_nat(0u);
v_bs_x27_323_ = lean_array_uset(v_bs_315_, v_i_314_, v___x_322_);
v___x_330_ = 0;
lean_inc(v___y_317_);
lean_inc_ref(v___y_316_);
lean_inc(v_v_321_);
v___x_331_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v___x_330_, v_v_321_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_a_332_, v___y_317_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_dec_ref(v___x_333_);
v_a_325_ = v_v_321_;
goto v___jp_324_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_bs_x27_323_);
lean_dec(v_v_321_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_dec(v_v_321_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_331_);
v_a_325_ = v_a_342_;
goto v___jp_324_;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_bs_x27_323_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
v_a_343_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_331_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_331_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
v___jp_324_:
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_314_, v___x_326_);
v___x_328_ = lean_array_uset(v_bs_x27_323_, v_i_314_, v_a_325_);
v_i_314_ = v___x_327_;
v_bs_315_ = v___x_328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg___boxed(lean_object* v_sz_351_, lean_object* v_i_352_, lean_object* v_bs_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
size_t v_sz_boxed_357_; size_t v_i_boxed_358_; lean_object* v_res_359_; 
v_sz_boxed_357_ = lean_unbox_usize(v_sz_351_);
lean_dec(v_sz_351_);
v_i_boxed_358_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_boxed_357_, v_i_boxed_358_, v_bs_353_, v___y_354_, v___y_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(lean_object* v_decls_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
size_t v_sz_366_; size_t v___x_367_; lean_object* v___x_368_; 
v_sz_366_ = lean_array_size(v_decls_360_);
v___x_367_ = ((size_t)0ULL);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_366_, v___x_367_, v_decls_360_, v___y_363_, v___y_364_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___lam__0___boxed(lean_object* v_decls_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(v_decls_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(size_t v_sz_387_, size_t v_i_388_, lean_object* v_bs_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_387_, v_i_388_, v_bs_389_, v___y_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___boxed(lean_object* v_sz_396_, lean_object* v_i_397_, lean_object* v_bs_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
size_t v_sz_boxed_404_; size_t v_i_boxed_405_; lean_object* v_res_406_; 
v_sz_boxed_404_ = lean_unbox_usize(v_sz_396_);
lean_dec(v_sz_396_);
v_i_boxed_405_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(v_sz_boxed_404_, v_i_boxed_405_, v_bs_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_406_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_407_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(size_t v_sz_412_, size_t v_i_413_, lean_object* v_bs_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_413_, v_sz_412_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_bs_414_);
return v___x_419_;
}
else
{
lean_object* v_v_420_; lean_object* v___x_421_; lean_object* v_bs_x27_422_; lean_object* v_a_424_; uint8_t v___x_429_; lean_object* v___x_430_; 
v_v_420_ = lean_array_uget(v_bs_414_, v_i_413_);
v___x_421_ = lean_unsigned_to_nat(0u);
v_bs_x27_422_ = lean_array_uset(v_bs_414_, v_i_413_, v___x_421_);
v___x_429_ = 1;
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
v___x_430_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v___x_429_, v_v_420_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___x_430_);
lean_inc(v_a_431_);
v___x_432_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_431_, v___y_416_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; lean_object* v_toSignature_434_; lean_object* v_env_435_; lean_object* v_nextMacroScope_436_; lean_object* v_ngen_437_; lean_object* v_auxDeclNGen_438_; lean_object* v_traceState_439_; lean_object* v_messages_440_; lean_object* v_infoState_441_; lean_object* v_snapshotTasks_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___x_432_);
v___x_433_ = lean_st_ref_take(v___y_416_);
v_toSignature_434_ = lean_ctor_get(v_a_431_, 0);
v_env_435_ = lean_ctor_get(v___x_433_, 0);
v_nextMacroScope_436_ = lean_ctor_get(v___x_433_, 1);
v_ngen_437_ = lean_ctor_get(v___x_433_, 2);
v_auxDeclNGen_438_ = lean_ctor_get(v___x_433_, 3);
v_traceState_439_ = lean_ctor_get(v___x_433_, 4);
v_messages_440_ = lean_ctor_get(v___x_433_, 6);
v_infoState_441_ = lean_ctor_get(v___x_433_, 7);
v_snapshotTasks_442_ = lean_ctor_get(v___x_433_, 8);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_433_, 5);
lean_dec(v_unused_454_);
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_453_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snapshotTasks_442_);
lean_inc(v_infoState_441_);
lean_inc(v_messages_440_);
lean_inc(v_traceState_439_);
lean_inc(v_auxDeclNGen_438_);
lean_inc(v_ngen_437_);
lean_inc(v_nextMacroScope_436_);
lean_inc(v_env_435_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_453_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_name_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v_name_446_ = lean_ctor_get(v_toSignature_434_, 0);
lean_inc(v_name_446_);
v___x_447_ = l_Lean_Compiler_LCNF_recordFinalImpureDecl(v_env_435_, v_name_446_);
v___x_448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 5, v___x_448_);
lean_ctor_set(v___x_444_, 0, v___x_447_);
v___x_450_ = v___x_444_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_nextMacroScope_436_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_ngen_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_auxDeclNGen_438_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_traceState_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_messages_440_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_infoState_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_snapshotTasks_442_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = lean_st_ref_set(v___y_416_, v___x_450_);
v_a_424_ = v_a_431_;
goto v___jp_423_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_a_431_);
lean_dec_ref(v_bs_x27_422_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
v_a_455_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_432_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_432_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_463_; 
v_a_463_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_430_);
v_a_424_ = v_a_463_;
goto v___jp_423_;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_bs_x27_422_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
v_a_464_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_430_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_430_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
v___jp_423_:
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_413_, v___x_425_);
v___x_427_ = lean_array_uset(v_bs_x27_422_, v_i_413_, v_a_424_);
v_i_413_ = v___x_426_;
v_bs_414_ = v___x_427_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___boxed(lean_object* v_sz_472_, lean_object* v_i_473_, lean_object* v_bs_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_472_);
lean_dec(v_sz_472_);
v_i_boxed_479_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_boxed_478_, v_i_boxed_479_, v_bs_474_, v___y_475_, v___y_476_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(lean_object* v_decls_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
size_t v_sz_487_; size_t v___x_488_; lean_object* v___x_489_; 
v_sz_487_ = lean_array_size(v_decls_481_);
v___x_488_ = ((size_t)0ULL);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_487_, v___x_488_, v_decls_481_, v___y_484_, v___y_485_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0___boxed(lean_object* v_decls_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(v_decls_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(size_t v_sz_508_, size_t v_i_509_, lean_object* v_bs_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_508_, v_i_509_, v_bs_510_, v___y_513_, v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___boxed(lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_bs_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_526_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(v_sz_boxed_525_, v_i_boxed_526_, v_bs_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0(void){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = 0;
v___x_530_ = 0;
v___x_531_ = l_Lean_Compiler_LCNF_cse(v___x_530_, v___x_529_, v___x_528_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2(void){
_start:
{
uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = 0;
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_538_ = l_Lean_Compiler_LCNF_simp(v___x_537_, v___x_536_, v___x_535_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3(void){
_start:
{
lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = 0;
v___x_541_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_540_, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Lean_Compiler_LCNF_findJoinPoints(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5(void){
_start:
{
uint8_t v___x_544_; lean_object* v___x_545_; 
v___x_544_ = 0;
v___x_545_ = l_Lean_Compiler_LCNF_reduceJpArity(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7(void){
_start:
{
uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = 0;
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__6));
v___x_551_ = l_Lean_Compiler_LCNF_simp(v___x_550_, v___x_549_, v___x_548_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = l_Lean_Compiler_LCNF_findJoinPoints(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9(void){
_start:
{
uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = 0;
v___x_555_ = lean_unsigned_to_nat(2u);
v___x_556_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_557_ = l_Lean_Compiler_LCNF_simp(v___x_556_, v___x_555_, v___x_554_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10(void){
_start:
{
lean_object* v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = 0;
v___x_560_ = 0;
v___x_561_ = l_Lean_Compiler_LCNF_cse(v___x_560_, v___x_559_, v___x_558_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11(void){
_start:
{
uint8_t v___x_562_; lean_object* v___x_563_; 
v___x_562_ = 0;
v___x_563_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_564_ = l_Lean_Compiler_LCNF_toMono;
v___x_565_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__11, &l_Lean_Compiler_LCNF_builtinPassManager___closed__11_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11);
v___x_566_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_saveBase));
v___x_567_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__10, &l_Lean_Compiler_LCNF_builtinPassManager___closed__10_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10);
v___x_568_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__9, &l_Lean_Compiler_LCNF_builtinPassManager___closed__9_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9);
v___x_569_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__8, &l_Lean_Compiler_LCNF_builtinPassManager___closed__8_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8);
v___x_570_ = l_Lean_Compiler_LCNF_specialize;
v___x_571_ = l_Lean_Compiler_LCNF_checkTemplateVisibility;
v___x_572_ = l_Lean_Compiler_LCNF_eagerLambdaLifting;
v___x_573_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__7, &l_Lean_Compiler_LCNF_builtinPassManager___closed__7_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7);
v___x_574_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__5, &l_Lean_Compiler_LCNF_builtinPassManager___closed__5_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5);
v___x_575_ = l_Lean_Compiler_LCNF_pullFunDecls;
v___x_576_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__4, &l_Lean_Compiler_LCNF_builtinPassManager___closed__4_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4);
v___x_577_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__3, &l_Lean_Compiler_LCNF_builtinPassManager___closed__3_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3);
v___x_578_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__2, &l_Lean_Compiler_LCNF_builtinPassManager___closed__2_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2);
v___x_579_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__0, &l_Lean_Compiler_LCNF_builtinPassManager___closed__0_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0);
v___x_580_ = l_Lean_Compiler_LCNF_pullInstances;
v___x_581_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_checkMeta));
v___x_582_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_init));
v___x_583_ = lean_unsigned_to_nat(19u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_array_push(v___x_584_, v___x_582_);
v___x_586_ = lean_array_push(v___x_585_, v___x_581_);
v___x_587_ = lean_array_push(v___x_586_, v___x_580_);
v___x_588_ = lean_array_push(v___x_587_, v___x_579_);
v___x_589_ = lean_array_push(v___x_588_, v___x_578_);
v___x_590_ = lean_array_push(v___x_589_, v___x_577_);
v___x_591_ = lean_array_push(v___x_590_, v___x_576_);
v___x_592_ = lean_array_push(v___x_591_, v___x_575_);
v___x_593_ = lean_array_push(v___x_592_, v___x_574_);
v___x_594_ = lean_array_push(v___x_593_, v___x_573_);
v___x_595_ = lean_array_push(v___x_594_, v___x_572_);
v___x_596_ = lean_array_push(v___x_595_, v___x_571_);
v___x_597_ = lean_array_push(v___x_596_, v___x_570_);
v___x_598_ = lean_array_push(v___x_597_, v___x_569_);
v___x_599_ = lean_array_push(v___x_598_, v___x_568_);
v___x_600_ = lean_array_push(v___x_599_, v___x_567_);
v___x_601_ = lean_array_push(v___x_600_, v___x_566_);
v___x_602_ = lean_array_push(v___x_601_, v___x_565_);
v___x_603_ = lean_array_push(v___x_602_, v___x_564_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13(void){
_start:
{
uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = 1;
v___x_605_ = lean_unsigned_to_nat(3u);
v___x_606_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_607_ = l_Lean_Compiler_LCNF_simp(v___x_606_, v___x_605_, v___x_604_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14(void){
_start:
{
uint8_t v___x_608_; lean_object* v___x_609_; 
v___x_608_ = 1;
v___x_609_ = l_Lean_Compiler_LCNF_reduceJpArity(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15(void){
_start:
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = 1;
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16(void){
_start:
{
lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = 1;
v___x_615_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17(void){
_start:
{
uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_616_ = 1;
v___x_617_ = lean_unsigned_to_nat(4u);
v___x_618_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_619_ = l_Lean_Compiler_LCNF_simp(v___x_618_, v___x_617_, v___x_616_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18(void){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_unsigned_to_nat(2u);
v___x_621_ = 1;
v___x_622_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_623_ = l_Lean_Compiler_LCNF_lambdaLifting;
v___x_624_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__18, &l_Lean_Compiler_LCNF_builtinPassManager___closed__18_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18);
v___x_625_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__17, &l_Lean_Compiler_LCNF_builtinPassManager___closed__17_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17);
v___x_626_ = l_Lean_Compiler_LCNF_commonJoinPointArgs;
v___x_627_ = l_Lean_Compiler_LCNF_reduceArity;
v___x_628_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__16, &l_Lean_Compiler_LCNF_builtinPassManager___closed__16_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16);
v___x_629_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__15, &l_Lean_Compiler_LCNF_builtinPassManager___closed__15_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15);
v___x_630_ = l_Lean_Compiler_LCNF_structProjCases;
v___x_631_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__14, &l_Lean_Compiler_LCNF_builtinPassManager___closed__14_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14);
v___x_632_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__13, &l_Lean_Compiler_LCNF_builtinPassManager___closed__13_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13);
v___x_633_ = lean_unsigned_to_nat(10u);
v___x_634_ = lean_mk_empty_array_with_capacity(v___x_633_);
v___x_635_ = lean_array_push(v___x_634_, v___x_632_);
v___x_636_ = lean_array_push(v___x_635_, v___x_631_);
v___x_637_ = lean_array_push(v___x_636_, v___x_630_);
v___x_638_ = lean_array_push(v___x_637_, v___x_629_);
v___x_639_ = lean_array_push(v___x_638_, v___x_628_);
v___x_640_ = lean_array_push(v___x_639_, v___x_627_);
v___x_641_ = lean_array_push(v___x_640_, v___x_626_);
v___x_642_ = lean_array_push(v___x_641_, v___x_625_);
v___x_643_ = lean_array_push(v___x_642_, v___x_624_);
v___x_644_ = lean_array_push(v___x_643_, v___x_623_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20(void){
_start:
{
uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = 1;
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21(void){
_start:
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = 1;
v___x_649_ = lean_unsigned_to_nat(5u);
v___x_650_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_651_ = l_Lean_Compiler_LCNF_simp(v___x_650_, v___x_649_, v___x_648_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22(void){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_unsigned_to_nat(2u);
v___x_653_ = 0;
v___x_654_ = 1;
v___x_655_ = l_Lean_Compiler_LCNF_cse(v___x_654_, v___x_653_, v___x_652_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23(void){
_start:
{
uint8_t v___x_656_; lean_object* v___x_657_; 
v___x_656_ = 1;
v___x_657_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_658_ = l_Lean_Compiler_LCNF_toImpure;
v___x_659_ = l_Lean_Compiler_LCNF_extractClosed;
v___x_660_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__23, &l_Lean_Compiler_LCNF_builtinPassManager___closed__23_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23);
v___x_661_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_saveMono));
v___x_662_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__22, &l_Lean_Compiler_LCNF_builtinPassManager___closed__22_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22);
v___x_663_ = l_Lean_Compiler_LCNF_elimDeadBranches;
v___x_664_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__21, &l_Lean_Compiler_LCNF_builtinPassManager___closed__21_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21);
v___x_665_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__20, &l_Lean_Compiler_LCNF_builtinPassManager___closed__20_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20);
v___x_666_ = lean_unsigned_to_nat(8u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_array_push(v___x_667_, v___x_665_);
v___x_669_ = lean_array_push(v___x_668_, v___x_664_);
v___x_670_ = lean_array_push(v___x_669_, v___x_663_);
v___x_671_ = lean_array_push(v___x_670_, v___x_662_);
v___x_672_ = lean_array_push(v___x_671_, v___x_661_);
v___x_673_ = lean_array_push(v___x_672_, v___x_660_);
v___x_674_ = lean_array_push(v___x_673_, v___x_659_);
v___x_675_ = lean_array_push(v___x_674_, v___x_658_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_Compiler_LCNF_pushProj(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26(void){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = 2;
v___x_680_ = l_Lean_Compiler_LCNF_elimDeadVars(v___x_679_, v___x_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = l_Lean_Compiler_LCNF_pushProj(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28(void){
_start:
{
uint8_t v___x_683_; lean_object* v___x_684_; 
v___x_683_ = 2;
v___x_684_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_685_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_saveImpure));
v___x_686_ = l_Lean_Compiler_LCNF_toposortPass;
v___x_687_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__28, &l_Lean_Compiler_LCNF_builtinPassManager___closed__28_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28);
v___x_688_ = l_Lean_Compiler_LCNF_detectSimpleGround;
v___x_689_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__27, &l_Lean_Compiler_LCNF_builtinPassManager___closed__27_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27);
v___x_690_ = l_Lean_Compiler_LCNF_expandResetReuse;
v___x_691_ = l_Lean_Compiler_LCNF_explicitRc;
v___x_692_ = l_Lean_Compiler_LCNF_explicitBoxing;
v___x_693_ = l_Lean_Compiler_LCNF_inferBorrow;
v___x_694_ = l_Lean_Compiler_LCNF_simpCase;
v___x_695_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__26, &l_Lean_Compiler_LCNF_builtinPassManager___closed__26_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26);
v___x_696_ = l_Lean_Compiler_LCNF_insertResetReuse;
v___x_697_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__25, &l_Lean_Compiler_LCNF_builtinPassManager___closed__25_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25);
v___x_698_ = lean_unsigned_to_nat(13u);
v___x_699_ = lean_mk_empty_array_with_capacity(v___x_698_);
v___x_700_ = lean_array_push(v___x_699_, v___x_697_);
v___x_701_ = lean_array_push(v___x_700_, v___x_696_);
v___x_702_ = lean_array_push(v___x_701_, v___x_695_);
v___x_703_ = lean_array_push(v___x_702_, v___x_694_);
v___x_704_ = lean_array_push(v___x_703_, v___x_693_);
v___x_705_ = lean_array_push(v___x_704_, v___x_692_);
v___x_706_ = lean_array_push(v___x_705_, v___x_691_);
v___x_707_ = lean_array_push(v___x_706_, v___x_690_);
v___x_708_ = lean_array_push(v___x_707_, v___x_689_);
v___x_709_ = lean_array_push(v___x_708_, v___x_688_);
v___x_710_ = lean_array_push(v___x_709_, v___x_687_);
v___x_711_ = lean_array_push(v___x_710_, v___x_686_);
v___x_712_ = lean_array_push(v___x_711_, v___x_685_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_713_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__29, &l_Lean_Compiler_LCNF_builtinPassManager___closed__29_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29);
v___x_714_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__24, &l_Lean_Compiler_LCNF_builtinPassManager___closed__24_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24);
v___x_715_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__19, &l_Lean_Compiler_LCNF_builtinPassManager___closed__19_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19);
v___x_716_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__12, &l_Lean_Compiler_LCNF_builtinPassManager___closed__12_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12);
v___x_717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_714_);
lean_ctor_set(v___x_717_, 3, v___x_713_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__30, &l_Lean_Compiler_LCNF_builtinPassManager___closed__30_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object* v_as_719_, size_t v_sz_720_, size_t v_i_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_lt(v_i_721_, v_sz_720_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_b_722_);
return v___x_727_;
}
else
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_array_uget_borrowed(v_as_719_, v_i_721_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v_a_728_);
v___x_729_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_b_722_, v_a_728_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; size_t v___x_731_; size_t v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_721_, v___x_731_);
v_i_721_ = v___x_732_;
v_b_722_ = v_a_730_;
goto _start;
}
else
{
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object* v_as_734_, lean_object* v_sz_735_, lean_object* v_i_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
size_t v_sz_boxed_741_; size_t v_i_boxed_742_; lean_object* v_res_743_; 
v_sz_boxed_741_ = lean_unbox_usize(v_sz_735_);
lean_dec(v_sz_735_);
v_i_boxed_742_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_res_743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(v_as_734_, v_sz_boxed_741_, v_i_boxed_742_, v_b_737_, v___y_738_, v___y_739_);
lean_dec_ref(v_as_734_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object* v_as_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v_b_747_);
return v___x_752_;
}
else
{
lean_object* v_a_753_; size_t v_sz_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_a_753_ = lean_array_uget_borrowed(v_as_744_, v_i_746_);
v_sz_754_ = lean_array_size(v_a_753_);
v___x_755_ = ((size_t)0ULL);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(v_a_753_, v_sz_754_, v___x_755_, v_b_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; size_t v___x_758_; size_t v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_746_, v___x_758_);
v_i_746_ = v___x_759_;
v_b_747_ = v_a_757_;
goto _start;
}
else
{
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object* v_as_761_, lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_769_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(v_as_761_, v_sz_boxed_768_, v_i_boxed_769_, v_b_764_, v___y_765_, v___y_766_);
lean_dec_ref(v_as_761_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object* v_importedDeclNames_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_m_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_m_775_ = l_Lean_Compiler_LCNF_builtinPassManager;
v_sz_776_ = lean_array_size(v_importedDeclNames_771_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(v_importedDeclNames_771_, v_sz_776_, v___x_777_, v_m_775_, v_a_772_, v_a_773_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object* v_importedDeclNames_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Compiler_LCNF_runImportedDecls(v_importedDeclNames_779_, v_a_780_, v_a_781_);
lean_dec_ref(v_importedDeclNames_779_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_fst_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_802_; 
v_fst_786_ = lean_ctor_get(v_x_784_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_x_784_, 1);
lean_dec(v_unused_803_);
v___x_788_ = v_x_784_;
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_fst_786_);
lean_dec(v_x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_fst_790_; lean_object* v_snd_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_801_; 
v_fst_790_ = lean_ctor_get(v_x_785_, 0);
v_snd_791_ = lean_ctor_get(v_x_785_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_801_ == 0)
{
v___x_793_ = v_x_785_;
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snd_791_);
lean_inc(v_fst_790_);
lean_dec(v_x_785_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 1, v_fst_786_);
lean_ctor_set(v___x_788_, 0, v_fst_790_);
v___x_796_ = v___x_788_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_fst_790_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_fst_786_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_796_);
v___x_798_ = v___x_793_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_791_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_x_804_, lean_object* v_s_805_, uint8_t v_x_806_){
_start:
{
lean_object* v_fst_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_fst_807_ = lean_ctor_get(v_s_805_, 0);
lean_inc(v_fst_807_);
lean_dec_ref(v_s_805_);
v___x_808_ = l_List_reverse___redArg(v_fst_807_);
v___x_809_ = lean_array_mk(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v_x_810_, lean_object* v_s_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_x_520__boxed_813_; lean_object* v_res_814_; 
v_x_520__boxed_813_ = lean_unbox(v_x_812_);
v_res_814_ = l_Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v_x_810_, v_s_811_, v_x_520__boxed_813_);
lean_dec_ref(v_x_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lean_box(0);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v_x_817_);
lean_dec_ref(v_x_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_s_819_){
_start:
{
lean_object* v_fst_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_fst_820_ = lean_ctor_get(v_s_819_, 0);
lean_inc(v_fst_820_);
lean_dec_ref(v_s_819_);
v___x_821_ = l_List_reverse___redArg(v_fst_820_);
v___x_822_ = lean_array_mk(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v___x_823_, lean_object* v_ns_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_runImportedDecls___boxed), 4, 1);
lean_closure_set(v___x_827_, 0, v_ns_824_);
v___x_828_ = l_Lean_ImportM_runCoreM___redArg(v___x_827_, v___y_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_837_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_837_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_823_);
lean_ctor_set(v___x_833_, 1, v_a_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_833_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v___x_823_);
v_a_838_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_828_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_828_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v___x_846_, lean_object* v_ns_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v___x_846_, v_ns_847_, v___y_848_);
lean_dec_ref(v___y_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v___x_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v___x_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v___x_854_);
return v_res_856_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_Compiler_LCNF_builtinPassManager;
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_875_; lean_object* v___f_876_; 
v___x_875_ = lean_obj_once(&l_Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_876_, 0, v___x_875_);
return v___f_876_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_877_ = lean_box(0);
v___x_878_ = lean_box(2);
v___f_879_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_880_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_881_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_882_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_883_ = lean_obj_once(&l_Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___x_884_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_885_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___f_883_);
lean_ctor_set(v___x_885_, 2, v___f_882_);
lean_ctor_set(v___x_885_, 3, v___f_881_);
lean_ctor_set(v___x_885_, 4, v___f_880_);
lean_ctor_set(v___x_885_, 5, v___f_879_);
lean_ctor_set(v___x_885_, 6, v___x_878_);
lean_ctor_set(v___x_885_, 7, v___x_877_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___f_886_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_887_ = lean_obj_once(&l_Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___f_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&l_Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___x_891_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
return v_res_893_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = l_Lean_Compiler_LCNF_instInhabitedPassManager_default;
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object* v_a_897_){
_start:
{
lean_object* v___x_899_; lean_object* v_env_900_; lean_object* v___x_901_; lean_object* v_toEnvExtension_902_; lean_object* v_asyncMode_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_snd_907_; lean_object* v___x_908_; 
v___x_899_ = lean_st_ref_get(v_a_897_);
v_env_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc_ref(v_env_900_);
lean_dec(v___x_899_);
v___x_901_ = l_Lean_Compiler_LCNF_passManagerExt;
v_toEnvExtension_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref(v_toEnvExtension_902_);
v_asyncMode_903_ = lean_ctor_get(v_toEnvExtension_902_, 2);
lean_inc(v_asyncMode_903_);
lean_dec_ref(v_toEnvExtension_902_);
v___x_904_ = lean_obj_once(&l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0, &l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0);
v___x_905_ = lean_box(0);
v___x_906_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_904_, v___x_901_, v_env_900_, v_asyncMode_903_, v___x_905_);
lean_dec(v_asyncMode_903_);
v_snd_907_ = lean_ctor_get(v___x_906_, 1);
lean_inc(v_snd_907_);
lean_dec(v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_snd_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_909_);
lean_dec(v_a_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Compiler_LCNF_getPassManager(v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_920_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_ctor_set(v___x_925_, 3, v___x_923_);
lean_ctor_set(v___x_925_, 4, v___x_923_);
lean_ctor_set(v___x_925_, 5, v___x_923_);
lean_ctor_set(v___x_925_, 6, v___x_923_);
lean_ctor_set(v___x_925_, 7, v___x_923_);
lean_ctor_set(v___x_925_, 8, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(32u);
v___x_927_ = lean_mk_empty_array_with_capacity(v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4(void){
_start:
{
size_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_929_ = ((size_t)5ULL);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_unsigned_to_nat(32u);
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___x_933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3);
v___x_934_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
lean_ctor_set(v___x_934_, 2, v___x_930_);
lean_ctor_set(v___x_934_, 3, v___x_930_);
lean_ctor_set_usize(v___x_934_, 4, v___x_929_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = lean_box(1);
v___x_936_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4);
v___x_937_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1);
v___x_938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(lean_object* v_msgData_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v_env_944_; lean_object* v_options_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_943_ = lean_st_ref_get(v___y_941_);
v_env_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_env_944_);
lean_dec(v___x_943_);
v_options_945_ = lean_ctor_get(v___y_940_, 2);
v___x_946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2);
v___x_947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5);
lean_inc_ref(v_options_945_);
v___x_948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_948_, 0, v_env_944_);
lean_ctor_set(v___x_948_, 1, v___x_946_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
lean_ctor_set(v___x_948_, 3, v_options_945_);
v___x_949_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_msgData_939_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(v_msgData_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_ref_960_; lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_ref_960_ = lean_ctor_get(v___y_957_, 5);
v___x_961_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(v_msg_956_, v___y_957_, v___y_958_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_970_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
lean_inc(v_ref_960_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_ref_960_);
lean_ctor_set(v___x_966_, 1, v_a_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg___boxed(lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_975_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(lean_object* v_attrName_991_, lean_object* v_declName_992_, lean_object* v_givenType_993_, lean_object* v_expectedType_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_998_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1);
v___x_999_ = l_Lean_MessageData_ofName(v_attrName_991_);
lean_inc_ref(v___x_999_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = 0;
v___x_1004_ = l_Lean_MessageData_ofConstName(v_declName_992_, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_indentExpr(v_givenType_993_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_999_);
v___x_1013_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_indentExpr(v_expectedType_994_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_1016_, v___y_995_, v___y_996_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___boxed(lean_object* v_attrName_1018_, lean_object* v_declName_1019_, lean_object* v_givenType_1020_, lean_object* v_expectedType_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v_attrName_1018_, v_declName_1019_, v_givenType_1020_, v_expectedType_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_ref_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_fileName_1031_; lean_object* v_fileMap_1032_; lean_object* v_options_1033_; lean_object* v_currRecDepth_1034_; lean_object* v_maxRecDepth_1035_; lean_object* v_ref_1036_; lean_object* v_currNamespace_1037_; lean_object* v_openDecls_1038_; lean_object* v_initHeartbeats_1039_; lean_object* v_maxHeartbeats_1040_; lean_object* v_quotContext_1041_; lean_object* v_currMacroScope_1042_; uint8_t v_diag_1043_; lean_object* v_cancelTk_x3f_1044_; uint8_t v_suppressElabErrors_1045_; lean_object* v_inheritedTraceOptions_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1055_; 
v_fileName_1031_ = lean_ctor_get(v___y_1028_, 0);
v_fileMap_1032_ = lean_ctor_get(v___y_1028_, 1);
v_options_1033_ = lean_ctor_get(v___y_1028_, 2);
v_currRecDepth_1034_ = lean_ctor_get(v___y_1028_, 3);
v_maxRecDepth_1035_ = lean_ctor_get(v___y_1028_, 4);
v_ref_1036_ = lean_ctor_get(v___y_1028_, 5);
v_currNamespace_1037_ = lean_ctor_get(v___y_1028_, 6);
v_openDecls_1038_ = lean_ctor_get(v___y_1028_, 7);
v_initHeartbeats_1039_ = lean_ctor_get(v___y_1028_, 8);
v_maxHeartbeats_1040_ = lean_ctor_get(v___y_1028_, 9);
v_quotContext_1041_ = lean_ctor_get(v___y_1028_, 10);
v_currMacroScope_1042_ = lean_ctor_get(v___y_1028_, 11);
v_diag_1043_ = lean_ctor_get_uint8(v___y_1028_, sizeof(void*)*14);
v_cancelTk_x3f_1044_ = lean_ctor_get(v___y_1028_, 12);
v_suppressElabErrors_1045_ = lean_ctor_get_uint8(v___y_1028_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1046_ = lean_ctor_get(v___y_1028_, 13);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___y_1028_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1048_ = v___y_1028_;
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_inheritedTraceOptions_1046_);
lean_inc(v_cancelTk_x3f_1044_);
lean_inc(v_currMacroScope_1042_);
lean_inc(v_quotContext_1041_);
lean_inc(v_maxHeartbeats_1040_);
lean_inc(v_initHeartbeats_1039_);
lean_inc(v_openDecls_1038_);
lean_inc(v_currNamespace_1037_);
lean_inc(v_ref_1036_);
lean_inc(v_maxRecDepth_1035_);
lean_inc(v_currRecDepth_1034_);
lean_inc(v_options_1033_);
lean_inc(v_fileMap_1032_);
lean_inc(v_fileName_1031_);
lean_dec(v___y_1028_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_ref_1050_; lean_object* v___x_1052_; 
v_ref_1050_ = l_Lean_replaceRef(v_ref_1026_, v_ref_1036_);
lean_dec(v_ref_1036_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 5, v_ref_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_fileName_1031_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_fileMap_1032_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_options_1033_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_currRecDepth_1034_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_maxRecDepth_1035_);
lean_ctor_set(v_reuseFailAlloc_1054_, 5, v_ref_1050_);
lean_ctor_set(v_reuseFailAlloc_1054_, 6, v_currNamespace_1037_);
lean_ctor_set(v_reuseFailAlloc_1054_, 7, v_openDecls_1038_);
lean_ctor_set(v_reuseFailAlloc_1054_, 8, v_initHeartbeats_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 9, v_maxHeartbeats_1040_);
lean_ctor_set(v_reuseFailAlloc_1054_, 10, v_quotContext_1041_);
lean_ctor_set(v_reuseFailAlloc_1054_, 11, v_currMacroScope_1042_);
lean_ctor_set(v_reuseFailAlloc_1054_, 12, v_cancelTk_x3f_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 13, v_inheritedTraceOptions_1046_);
lean_ctor_set_uint8(v_reuseFailAlloc_1054_, sizeof(void*)*14, v_diag_1043_);
lean_ctor_set_uint8(v_reuseFailAlloc_1054_, sizeof(void*)*14 + 1, v_suppressElabErrors_1045_);
v___x_1052_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_1027_, v___x_1052_, v___y_1029_);
lean_dec_ref(v___x_1052_);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1056_, v_msg_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec(v_ref_1056_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_msg_1083_, lean_object* v_declHint_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_env_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_st_ref_get(v___y_1085_);
v_env_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_env_1088_);
lean_dec(v___x_1087_);
v___x_1089_ = l_Lean_Name_isAnonymous(v_declHint_1084_);
if (v___x_1089_ == 0)
{
uint8_t v_isExporting_1090_; 
v_isExporting_1090_ = lean_ctor_get_uint8(v_env_1088_, sizeof(void*)*8);
if (v_isExporting_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v_env_1088_);
lean_dec(v_declHint_1084_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_msg_1083_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
lean_inc_ref(v_env_1088_);
v___x_1092_ = l_Lean_Environment_setExporting(v_env_1088_, v___x_1089_);
lean_inc(v_declHint_1084_);
lean_inc_ref(v___x_1092_);
v___x_1093_ = l_Lean_Environment_contains(v___x_1092_, v_declHint_1084_, v_isExporting_1090_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v___x_1092_);
lean_dec_ref(v_env_1088_);
lean_dec(v_declHint_1084_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_msg_1083_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_c_1100_; lean_object* v___x_1101_; 
v___x_1095_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2);
v___x_1096_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5);
v___x_1097_ = l_Lean_Options_empty;
v___x_1098_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1092_);
lean_ctor_set(v___x_1098_, 1, v___x_1095_);
lean_ctor_set(v___x_1098_, 2, v___x_1096_);
lean_ctor_set(v___x_1098_, 3, v___x_1097_);
lean_inc(v_declHint_1084_);
v___x_1099_ = l_Lean_MessageData_ofConstName(v_declHint_1084_, v___x_1089_);
v_c_1100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1100_, 0, v___x_1098_);
lean_ctor_set(v_c_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1088_, v_declHint_1084_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_env_1088_);
lean_dec(v_declHint_1084_);
v___x_1102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_c_1100_);
v___x_1104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_MessageData_note(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_msg_1083_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v_val_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1144_; 
v_val_1109_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1111_ = v___x_1101_;
v_isShared_1112_ = v_isSharedCheck_1144_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_val_1109_);
lean_dec(v___x_1101_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1144_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_mod_1116_; uint8_t v___x_1117_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Lean_Environment_header(v_env_1088_);
lean_dec_ref(v_env_1088_);
v___x_1115_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1114_);
v_mod_1116_ = lean_array_get(v___x_1113_, v___x_1115_, v_val_1109_);
lean_dec(v_val_1109_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = l_Lean_isPrivateName(v_declHint_1084_);
lean_dec(v_declHint_1084_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_c_1100_);
v___x_1120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_MessageData_ofName(v_mod_1116_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_MessageData_note(v___x_1125_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_msg_1083_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1127_);
v___x_1129_ = v___x_1111_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_c_1100_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofName(v_mod_1116_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_note(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_msg_1083_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1140_);
v___x_1142_ = v___x_1111_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1145_; 
lean_dec_ref(v_env_1088_);
lean_dec(v_declHint_1084_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_msg_1083_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1146_, lean_object* v_declHint_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_1146_, v_declHint_1147_, v___y_1148_);
lean_dec(v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_msg_1151_, lean_object* v_declHint_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1166_; 
v___x_1156_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_1151_, v_declHint_1152_, v___y_1154_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1161_ = l_Lean_unknownIdentifierMessageTag;
v___x_1162_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msg_1167_, lean_object* v_declHint_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_1167_, v_declHint_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1173_, lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_a_1180_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_1174_, v_declHint_1175_, v___y_1176_, v___y_1177_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1173_, v_a_1180_, v___y_1176_, v___y_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1182_, lean_object* v_msg_1183_, lean_object* v_declHint_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1182_, v_msg_1183_, v_declHint_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec(v_ref_1182_);
return v_res_1188_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1195_, lean_object* v_constName_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1200_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1201_ = 0;
lean_inc(v_constName_1196_);
v___x_1202_ = l_Lean_MessageData_ofConstName(v_constName_1196_, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1200_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1195_, v___x_1205_, v_constName_1196_, v___y_1197_, v___y_1198_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1207_, lean_object* v_constName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_1207_, v_constName_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec(v_ref_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(lean_object* v_constName_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_ref_1217_; lean_object* v___x_1218_; 
v_ref_1217_ = lean_ctor_get(v___y_1214_, 5);
lean_inc(v_ref_1217_);
v___x_1218_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_1217_, v_constName_1213_, v___y_1214_, v___y_1215_);
lean_dec(v_ref_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v_env_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = lean_st_ref_get(v___y_1226_);
v_env_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_ref(v_env_1229_);
lean_dec(v___x_1228_);
v___x_1230_ = 0;
lean_inc(v_constName_1224_);
v___x_1231_ = l_Lean_Environment_find_x3f(v_env_1229_, v_constName_1224_, v___x_1230_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_1224_, v___y_1225_, v___y_1226_);
return v___x_1232_;
}
else
{
lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v___y_1225_);
lean_dec(v_constName_1224_);
v_val_1233_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1231_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_dec(v___x_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set_tag(v___x_1235_, 0);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_val_1233_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0___boxed(lean_object* v_constName_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(v_constName_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
return v_res_1245_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__4(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__3));
v___x_1257_ = l_Lean_mkConst(v___x_1256_, v___x_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object* v_declName_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
lean_inc_ref(v_a_1259_);
lean_inc(v_declName_1258_);
v___x_1262_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(v_declName_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___x_1271_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref(v___x_1262_);
v___x_1271_ = l_Lean_ConstantInfo_type(v_a_1263_);
if (lean_obj_tag(v___x_1271_) == 4)
{
lean_object* v_declName_1272_; 
v_declName_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_declName_1272_);
lean_dec_ref(v___x_1271_);
if (lean_obj_tag(v_declName_1272_) == 1)
{
lean_object* v_pre_1273_; 
v_pre_1273_ = lean_ctor_get(v_declName_1272_, 0);
lean_inc(v_pre_1273_);
if (lean_obj_tag(v_pre_1273_) == 1)
{
lean_object* v_pre_1274_; 
v_pre_1274_ = lean_ctor_get(v_pre_1273_, 0);
lean_inc(v_pre_1274_);
if (lean_obj_tag(v_pre_1274_) == 1)
{
lean_object* v_pre_1275_; 
v_pre_1275_ = lean_ctor_get(v_pre_1274_, 0);
lean_inc(v_pre_1275_);
if (lean_obj_tag(v_pre_1275_) == 1)
{
lean_object* v_pre_1276_; 
v_pre_1276_ = lean_ctor_get(v_pre_1275_, 0);
lean_inc(v_pre_1276_);
if (lean_obj_tag(v_pre_1276_) == 0)
{
lean_object* v_str_1277_; lean_object* v_str_1278_; lean_object* v_str_1279_; lean_object* v_str_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_str_1277_ = lean_ctor_get(v_declName_1272_, 1);
lean_inc_ref(v_str_1277_);
lean_dec_ref(v_declName_1272_);
v_str_1278_ = lean_ctor_get(v_pre_1273_, 1);
lean_inc_ref(v_str_1278_);
lean_dec_ref(v_pre_1273_);
v_str_1279_ = lean_ctor_get(v_pre_1274_, 1);
lean_inc_ref(v_str_1279_);
lean_dec_ref(v_pre_1274_);
v_str_1280_ = lean_ctor_get(v_pre_1275_, 1);
lean_inc_ref(v_str_1280_);
lean_dec_ref(v_pre_1275_);
v___x_1281_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_1282_ = lean_string_dec_eq(v_str_1280_, v___x_1281_);
lean_dec_ref(v_str_1280_);
if (v___x_1282_ == 0)
{
lean_dec_ref(v_str_1279_);
lean_dec_ref(v_str_1278_);
lean_dec_ref(v_str_1277_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_1284_ = lean_string_dec_eq(v_str_1279_, v___x_1283_);
lean_dec_ref(v_str_1279_);
if (v___x_1284_ == 0)
{
lean_dec_ref(v_str_1278_);
lean_dec_ref(v_str_1277_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_1286_ = lean_string_dec_eq(v_str_1278_, v___x_1285_);
lean_dec_ref(v_str_1278_);
if (v___x_1286_ == 0)
{
lean_dec_ref(v_str_1277_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__2));
v___x_1288_ = lean_string_dec_eq(v_str_1277_, v___x_1287_);
lean_dec_ref(v_str_1277_);
if (v___x_1288_ == 0)
{
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1289_; lean_object* v_a_1290_; lean_object* v___x_1291_; 
lean_dec(v_a_1263_);
v___x_1289_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_1260_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v___x_1289_);
lean_inc(v_a_1260_);
lean_inc(v_declName_1258_);
v___x_1291_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_a_1290_, v_declName_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1324_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1324_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1324_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v_env_1297_; lean_object* v_nextMacroScope_1298_; lean_object* v_ngen_1299_; lean_object* v_auxDeclNGen_1300_; lean_object* v_traceState_1301_; lean_object* v_messages_1302_; lean_object* v_infoState_1303_; lean_object* v_snapshotTasks_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1322_; 
v___x_1296_ = lean_st_ref_take(v_a_1260_);
v_env_1297_ = lean_ctor_get(v___x_1296_, 0);
v_nextMacroScope_1298_ = lean_ctor_get(v___x_1296_, 1);
v_ngen_1299_ = lean_ctor_get(v___x_1296_, 2);
v_auxDeclNGen_1300_ = lean_ctor_get(v___x_1296_, 3);
v_traceState_1301_ = lean_ctor_get(v___x_1296_, 4);
v_messages_1302_ = lean_ctor_get(v___x_1296_, 6);
v_infoState_1303_ = lean_ctor_get(v___x_1296_, 7);
v_snapshotTasks_1304_ = lean_ctor_get(v___x_1296_, 8);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1296_, 5);
lean_dec(v_unused_1323_);
v___x_1306_ = v___x_1296_;
v_isShared_1307_ = v_isSharedCheck_1322_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_snapshotTasks_1304_);
lean_inc(v_infoState_1303_);
lean_inc(v_messages_1302_);
lean_inc(v_traceState_1301_);
lean_inc(v_auxDeclNGen_1300_);
lean_inc(v_ngen_1299_);
lean_inc(v_nextMacroScope_1298_);
lean_inc(v_env_1297_);
lean_dec(v___x_1296_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1322_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v_toEnvExtension_1309_; lean_object* v_asyncMode_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1308_ = l_Lean_Compiler_LCNF_passManagerExt;
v_toEnvExtension_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_toEnvExtension_1309_);
v_asyncMode_1310_ = lean_ctor_get(v_toEnvExtension_1309_, 2);
lean_inc(v_asyncMode_1310_);
lean_dec_ref(v_toEnvExtension_1309_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_declName_1258_);
lean_ctor_set(v___x_1311_, 1, v_a_1292_);
v___x_1312_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1308_, v_env_1297_, v___x_1311_, v_asyncMode_1310_, v_pre_1276_);
lean_dec(v_asyncMode_1310_);
v___x_1313_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 5, v___x_1313_);
lean_ctor_set(v___x_1306_, 0, v___x_1312_);
v___x_1315_ = v___x_1306_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1298_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1299_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1300_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_traceState_1301_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_messages_1302_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_infoState_1303_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_snapshotTasks_1304_);
v___x_1315_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = lean_st_ref_set(v_a_1260_, v___x_1315_);
lean_dec(v_a_1260_);
v___x_1317_ = lean_box(0);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1317_);
v___x_1319_ = v___x_1294_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1260_);
lean_dec(v_declName_1258_);
v_a_1325_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1291_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1291_);
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
}
}
else
{
lean_dec(v_pre_1276_);
lean_dec_ref(v_pre_1275_);
lean_dec_ref(v_pre_1274_);
lean_dec_ref(v_pre_1273_);
lean_dec_ref(v_declName_1272_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
}
else
{
lean_dec_ref(v_pre_1274_);
lean_dec(v_pre_1275_);
lean_dec_ref(v_pre_1273_);
lean_dec_ref(v_declName_1272_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
}
else
{
lean_dec(v_pre_1274_);
lean_dec_ref(v_pre_1273_);
lean_dec_ref(v_declName_1272_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
}
else
{
lean_dec(v_pre_1273_);
lean_dec_ref(v_declName_1272_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
}
else
{
lean_dec(v_declName_1272_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
}
else
{
lean_dec_ref(v___x_1271_);
v___y_1265_ = v_a_1259_;
v___y_1266_ = v_a_1260_;
goto v___jp_1264_;
}
v___jp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__1));
v___x_1268_ = l_Lean_ConstantInfo_type(v_a_1263_);
lean_dec(v_a_1263_);
v___x_1269_ = lean_obj_once(&l_Lean_Compiler_LCNF_addPass___closed__4, &l_Lean_Compiler_LCNF_addPass___closed__4_once, _init_l_Lean_Compiler_LCNF_addPass___closed__4);
v___x_1270_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v___x_1267_, v_declName_1258_, v___x_1268_, v___x_1269_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v___x_1270_;
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_declName_1258_);
v_a_1333_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1262_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1262_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___boxed(lean_object* v_declName_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Compiler_LCNF_addPass(v_declName_1341_, v_a_1342_, v_a_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(lean_object* v_00_u03b1_1346_, lean_object* v_attrName_1347_, lean_object* v_declName_1348_, lean_object* v_givenType_1349_, lean_object* v_expectedType_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v_attrName_1347_, v_declName_1348_, v_givenType_1349_, v_expectedType_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_attrName_1356_, lean_object* v_declName_1357_, lean_object* v_givenType_1358_, lean_object* v_expectedType_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(v_00_u03b1_1355_, v_attrName_1356_, v_declName_1357_, v_givenType_1358_, v_expectedType_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(lean_object* v_00_u03b1_1364_, lean_object* v_constName_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_constName_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(v_00_u03b1_1370_, v_constName_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(lean_object* v_00_u03b1_1376_, lean_object* v_msg_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(v_00_u03b1_1382_, v_msg_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1388_, lean_object* v_ref_1389_, lean_object* v_constName_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_1389_, v_constName_1390_, v___y_1391_, v___y_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1395_, lean_object* v_ref_1396_, lean_object* v_constName_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(v_00_u03b1_1395_, v_ref_1396_, v_constName_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec(v_ref_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1402_, lean_object* v_ref_1403_, lean_object* v_msg_1404_, lean_object* v_declHint_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1403_, v_msg_1404_, v_declHint_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_ref_1411_, lean_object* v_msg_1412_, lean_object* v_declHint_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1410_, v_ref_1411_, v_msg_1412_, v_declHint_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec(v_ref_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(lean_object* v_msg_1418_, lean_object* v_declHint_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_1418_, v_declHint_1419_, v___y_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___boxed(lean_object* v_msg_1424_, lean_object* v_declHint_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(v_msg_1424_, v_declHint_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b1_1430_, lean_object* v_ref_1431_, lean_object* v_msg_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1431_, v_msg_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_1437_, v_ref_1438_, v_msg_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec(v_ref_1438_);
return v_res_1443_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_1453_, uint8_t v_kind_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___y_1464_; 
v___x_1458_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_1459_ = l_Lean_MessageData_ofName(v_name_1453_);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
switch(v_kind_1454_)
{
case 0:
{
lean_object* v___x_1471_; 
v___x_1471_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_1464_ = v___x_1471_;
goto v___jp_1463_;
}
case 1:
{
lean_object* v___x_1472_; 
v___x_1472_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_1464_ = v___x_1472_;
goto v___jp_1463_;
}
default: 
{
lean_object* v___x_1473_; 
v___x_1473_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_1464_ = v___x_1473_;
goto v___jp_1463_;
}
}
v___jp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1464_);
v___x_1466_ = l_Lean_MessageData_ofFormat(v___x_1465_);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1462_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_1469_, v___y_1455_, v___y_1456_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_1474_, lean_object* v_kind_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v_kind_boxed_1479_; lean_object* v_res_1480_; 
v_kind_boxed_1479_ = lean_unbox(v_kind_1475_);
v_res_1480_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v_name_1474_, v_kind_boxed_1479_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(lean_object* v___x_1481_, lean_object* v_declName_1482_, lean_object* v_stx_1483_, uint8_t v_kind_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___x_1502_; 
lean_inc_ref(v___y_1485_);
v___x_1502_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1483_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1502_) == 0)
{
uint8_t v___x_1503_; uint8_t v___x_1504_; 
lean_dec_ref(v___x_1502_);
v___x_1503_ = 0;
v___x_1504_ = l_Lean_instBEqAttributeKind_beq(v_kind_1484_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
lean_dec(v_declName_1482_);
v___x_1505_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v___x_1481_, v_kind_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v___x_1505_;
}
else
{
v___y_1489_ = v___y_1485_;
v___y_1490_ = v___y_1486_;
goto v___jp_1488_;
}
}
else
{
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_declName_1482_);
lean_dec(v___x_1481_);
return v___x_1502_;
}
v___jp_1488_:
{
lean_object* v___x_1491_; 
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v_declName_1482_);
v___x_1491_ = l_Lean_ensureAttrDeclIsMeta(v___x_1481_, v_declName_1482_, v_kind_1484_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref(v___x_1491_);
v___x_1492_ = l_Lean_Compiler_LCNF_addPass(v_declName_1482_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1500_; 
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v___x_1492_, 0);
lean_dec(v_unused_1501_);
v___x_1494_ = v___x_1492_;
v_isShared_1495_ = v_isSharedCheck_1500_;
goto v_resetjp_1493_;
}
else
{
lean_dec(v___x_1492_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1500_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_box(0);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
else
{
return v___x_1492_;
}
}
else
{
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v_declName_1482_);
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object* v___x_1506_, lean_object* v_declName_1507_, lean_object* v_stx_1508_, lean_object* v_kind_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
uint8_t v_kind_boxed_1513_; lean_object* v_res_1514_; 
v_kind_boxed_1513_ = lean_unbox(v_kind_1509_);
v_res_1514_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(v___x_1506_, v_declName_1507_, v_stx_1508_, v_kind_boxed_1513_, v___y_1510_, v___y_1511_);
return v_res_1514_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(lean_object* v___x_1521_, lean_object* v_decl_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1526_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1527_ = l_Lean_MessageData_ofName(v___x_1521_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_1530_, v___y_1523_, v___y_1524_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object* v___x_1532_, lean_object* v_decl_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(v___x_1532_, v_decl_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v_decl_1533_);
return v_res_1537_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_unsigned_to_nat(3159741348u);
v___x_1588_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1589_ = l_Lean_Name_num___override(v___x_1588_, v___x_1587_);
return v___x_1589_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1592_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1593_ = l_Lean_Name_str___override(v___x_1592_, v___x_1591_);
return v___x_1593_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1596_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1597_ = l_Lean_Name_str___override(v___x_1596_, v___x_1595_);
return v___x_1597_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_unsigned_to_nat(2u);
v___x_1599_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1600_ = l_Lean_Name_num___override(v___x_1599_, v___x_1598_);
return v___x_1600_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1606_ = 1;
v___x_1607_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1608_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__1));
v___x_1609_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1610_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1608_);
lean_ctor_set(v___x_1610_, 2, v___x_1607_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*3, v___x_1606_);
return v___x_1610_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___f_1611_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___f_1612_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1613_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___f_1612_);
lean_ctor_set(v___x_1614_, 2, v___f_1611_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1617_ = l_Lean_registerBuiltinAttribute(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_();
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1620_, lean_object* v_name_1621_, uint8_t v_kind_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v_name_1621_, v_kind_1622_, v___y_1623_, v___y_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_name_1628_, lean_object* v_kind_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v_kind_boxed_1633_; lean_object* v_res_1634_; 
v_kind_boxed_1633_ = lean_unbox(v_kind_1629_);
v_res_1634_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(v_00_u03b1_1627_, v_name_1628_, v_kind_boxed_1633_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1661_ = 1;
v___x_1662_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1663_ = l_Lean_registerTraceClass(v___x_1660_, v___x_1661_, v___x_1662_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v___x_1663_);
v___x_1664_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1665_ = l_Lean_registerTraceClass(v___x_1664_, v___x_1661_, v___x_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v___x_1665_);
v___x_1666_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1667_ = l_Lean_registerTraceClass(v___x_1666_, v___x_1661_, v___x_1662_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___x_1667_);
v___x_1668_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1669_ = l_Lean_registerTraceClass(v___x_1668_, v___x_1661_, v___x_1662_);
return v___x_1669_;
}
else
{
return v___x_1667_;
}
}
else
{
return v___x_1665_;
}
}
else
{
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2____boxed(lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_();
return v_res_1671_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_StructProjCases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Visibility(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PushProj(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferBorrow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CSE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToMono(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Visibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PushProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Toposort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_builtinPassManager = _init_l_Lean_Compiler_LCNF_builtinPassManager();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_passManagerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_passManagerExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_StructProjCases(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Visibility(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PushProj(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_InferBorrow(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_SimpleGroundExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToMono(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Visibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PushProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Toposort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Passes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Passes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Passes(builtin);
}
#ifdef __cplusplus
}
#endif
