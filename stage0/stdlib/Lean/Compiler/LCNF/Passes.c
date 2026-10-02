// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: public import Lean.Compiler.LCNF.PullLetDecls public import Lean.Compiler.LCNF.CSE public import Lean.Compiler.LCNF.JoinPoints public import Lean.Compiler.LCNF.Specialize public import Lean.Compiler.LCNF.ToMono public import Lean.Compiler.LCNF.LambdaLifting public import Lean.Compiler.LCNF.FloatLetIn public import Lean.Compiler.LCNF.ReduceArity public import Lean.Compiler.LCNF.ElimDeadBranches public import Lean.Compiler.LCNF.StructProjCases public import Lean.Compiler.LCNF.ExtractClosed public import Lean.Compiler.LCNF.Visibility public import Lean.Compiler.LCNF.Simp public import Lean.Compiler.LCNF.ToImpure public import Lean.Compiler.LCNF.PushProj public import Lean.Compiler.LCNF.ResetReuse public import Lean.Compiler.LCNF.SimpCase public import Lean.Compiler.LCNF.InferBorrow public import Lean.Compiler.LCNF.ExplicitBoxing public import Lean.Compiler.LCNF.ExplicitRC public import Lean.Compiler.LCNF.CoalesceRC public import Lean.Compiler.LCNF.Toposort public import Lean.Compiler.LCNF.ExpandResetReuse public import Lean.Compiler.LCNF.SimpleGroundExpr
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager_default;
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toposortPass;
lean_object* l_Lean_Compiler_LCNF_inferVisibility(uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_detectSimpleGround;
lean_object* l_Lean_Compiler_LCNF_pushProj(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_coalesceRC;
extern lean_object* l_Lean_Compiler_LCNF_expandResetReuse;
extern lean_object* l_Lean_Compiler_LCNF_explicitRc;
extern lean_object* l_Lean_Compiler_LCNF_explicitBoxing;
extern lean_object* l_Lean_Compiler_LCNF_inferBorrow;
extern lean_object* l_Lean_Compiler_LCNF_simpCase;
lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_insertResetReuse;
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toImpure;
extern lean_object* l_Lean_Compiler_LCNF_extractClosed;
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, uint8_t, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_elimDeadBranches;
lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_lambdaLifting;
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
lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "passManagerExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 46, 217, 27, 108, 148, 162, 146)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Passes"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 202, 253, 45, 23, 235, 193, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 87, 67, 6, 155, 120, 131, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 168, 19, 173, 187, 189, 162, 33)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 231, 245, 175, 233, 54, 120, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 34, 48, 120, 254, 109, 127, 221)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 243, 214, 185, 49, 203, 111, 147)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 206, 229, 68, 67, 72, 146, 96)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 154, 255, 212, 182, 226, 77, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 148, 71, 216, 106, 168, 19, 62)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 16, 78, 18, 224, 238, 56, 194)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 254, 187, 91, 177, 170, 7, 67)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(121, 215, 87, 166, 244, 66, 83, 246)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
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
lean_dec_ref_known(v___x_9_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___lam__0(lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___y_103_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___lam__0___boxed(lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Compiler_LCNF_Pass_trace___lam__0(v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace(uint8_t v_phase_121_){
_start:
{
lean_object* v___f_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___f_122_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_trace___closed__0));
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = 0;
v___x_125_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_trace___closed__2));
v___x_126_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_126_, 0, v___x_123_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
lean_ctor_set(v___x_126_, 2, v___f_122_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*3, v_phase_121_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*3 + 1, v_phase_121_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*3 + 2, v___x_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_trace___boxed(lean_object* v_phase_127_){
_start:
{
uint8_t v_phase_boxed_128_; lean_object* v_res_129_; 
v_phase_boxed_128_ = lean_unbox(v_phase_127_);
v_res_129_ = l_Lean_Compiler_LCNF_Pass_trace(v_phase_boxed_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(size_t v_sz_130_, size_t v_i_131_, lean_object* v_bs_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = lean_usize_dec_lt(v_i_131_, v_sz_130_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v_bs_132_);
return v___x_137_;
}
else
{
lean_object* v_v_138_; lean_object* v___x_139_; lean_object* v_bs_x27_140_; lean_object* v_a_142_; uint8_t v___x_147_; lean_object* v___x_148_; 
v_v_138_ = lean_array_uget(v_bs_132_, v_i_131_);
v___x_139_ = lean_unsigned_to_nat(0u);
v_bs_x27_140_ = lean_array_uset(v_bs_132_, v_i_131_, v___x_139_);
v___x_147_ = 0;
lean_inc(v_v_138_);
v___x_148_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v___x_147_, v_v_138_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_a_149_, v___y_134_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_dec_ref_known(v___x_150_, 1);
v_a_142_ = v_v_138_;
goto v___jp_141_;
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v_bs_x27_140_);
lean_dec(v_v_138_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_dec(v_v_138_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_159_; 
v_a_159_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_148_, 1);
v_a_142_ = v_a_159_;
goto v___jp_141_;
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_bs_x27_140_);
v_a_160_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_148_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_148_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
v___jp_141_:
{
size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_131_, v___x_143_);
v___x_145_ = lean_array_uset(v_bs_x27_140_, v_i_131_, v_a_142_);
v_i_131_ = v___x_144_;
v_bs_132_ = v___x_145_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg___boxed(lean_object* v_sz_168_, lean_object* v_i_169_, lean_object* v_bs_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
size_t v_sz_boxed_174_; size_t v_i_boxed_175_; lean_object* v_res_176_; 
v_sz_boxed_174_ = lean_unbox_usize(v_sz_168_);
lean_dec(v_sz_168_);
v_i_boxed_175_ = lean_unbox_usize(v_i_169_);
lean_dec(v_i_169_);
v_res_176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_boxed_174_, v_i_boxed_175_, v_bs_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(lean_object* v_decls_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
size_t v_sz_183_; size_t v___x_184_; lean_object* v___x_185_; 
v_sz_183_ = lean_array_size(v_decls_177_);
v___x_184_ = ((size_t)0ULL);
v___x_185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_183_, v___x_184_, v_decls_177_, v___y_180_, v___y_181_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveBase___lam__0___boxed(lean_object* v_decls_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(v_decls_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(size_t v_sz_204_, size_t v_i_205_, lean_object* v_bs_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_204_, v_i_205_, v_bs_206_, v___y_209_, v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___boxed(lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_bs_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
size_t v_sz_boxed_221_; size_t v_i_boxed_222_; lean_object* v_res_223_; 
v_sz_boxed_221_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_222_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(v_sz_boxed_221_, v_i_boxed_222_, v_bs_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_bs_226_);
return v___x_231_;
}
else
{
lean_object* v_v_232_; lean_object* v___x_233_; lean_object* v_bs_x27_234_; lean_object* v_a_236_; uint8_t v___x_241_; lean_object* v___x_242_; 
v_v_232_ = lean_array_uget(v_bs_226_, v_i_225_);
v___x_233_ = lean_unsigned_to_nat(0u);
v_bs_x27_234_ = lean_array_uset(v_bs_226_, v_i_225_, v___x_233_);
v___x_241_ = 0;
lean_inc(v_v_232_);
v___x_242_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v___x_241_, v_v_232_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_a_243_, v___y_228_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_dec_ref_known(v___x_244_, 1);
v_a_236_ = v_v_232_;
goto v___jp_235_;
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_bs_x27_234_);
lean_dec(v_v_232_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_dec(v_v_232_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_253_; 
v_a_253_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_242_, 1);
v_a_236_ = v_a_253_;
goto v___jp_235_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_bs_x27_234_);
v_a_254_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_242_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_242_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
v___jp_235_:
{
size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_225_, v___x_237_);
v___x_239_ = lean_array_uset(v_bs_x27_234_, v_i_225_, v_a_236_);
v_i_225_ = v___x_238_;
v_bs_226_ = v___x_239_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg___boxed(lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_bs_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
size_t v_sz_boxed_268_; size_t v_i_boxed_269_; lean_object* v_res_270_; 
v_sz_boxed_268_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_269_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_boxed_268_, v_i_boxed_269_, v_bs_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(lean_object* v_decls_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
size_t v_sz_277_; size_t v___x_278_; lean_object* v___x_279_; 
v_sz_277_ = lean_array_size(v_decls_271_);
v___x_278_ = ((size_t)0ULL);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_277_, v___x_278_, v_decls_271_, v___y_274_, v___y_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveMono___lam__0___boxed(lean_object* v_decls_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(v_decls_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(size_t v_sz_298_, size_t v_i_299_, lean_object* v_bs_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_298_, v_i_299_, v_bs_300_, v___y_303_, v___y_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___boxed(lean_object* v_sz_307_, lean_object* v_i_308_, lean_object* v_bs_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
size_t v_sz_boxed_315_; size_t v_i_boxed_316_; lean_object* v_res_317_; 
v_sz_boxed_315_ = lean_unbox_usize(v_sz_307_);
lean_dec(v_sz_307_);
v_i_boxed_316_ = lean_unbox_usize(v_i_308_);
lean_dec(v_i_308_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(v_sz_boxed_315_, v_i_boxed_316_, v_bs_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_317_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_318_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(size_t v_sz_323_, size_t v_i_324_, lean_object* v_bs_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_bs_325_);
return v___x_330_;
}
else
{
lean_object* v_v_331_; lean_object* v___x_332_; lean_object* v_bs_x27_333_; lean_object* v_a_335_; uint8_t v___x_340_; lean_object* v___x_341_; 
v_v_331_ = lean_array_uget(v_bs_325_, v_i_324_);
v___x_332_ = lean_unsigned_to_nat(0u);
v_bs_x27_333_ = lean_array_uset(v_bs_325_, v_i_324_, v___x_332_);
v___x_340_ = 1;
v___x_341_ = l_Lean_Compiler_LCNF_normalizeFVarIds(v___x_340_, v_v_331_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_n(v_a_342_, 2);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_342_, v___y_327_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; lean_object* v_toSignature_345_; lean_object* v_env_346_; lean_object* v_nextMacroScope_347_; lean_object* v_ngen_348_; lean_object* v_auxDeclNGen_349_; lean_object* v_traceState_350_; lean_object* v_recordedDeps_351_; lean_object* v_messages_352_; lean_object* v_infoState_353_; lean_object* v_snapshotTasks_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref_known(v___x_343_, 1);
v___x_344_ = lean_st_ref_take(v___y_327_);
v_toSignature_345_ = lean_ctor_get(v_a_342_, 0);
v_env_346_ = lean_ctor_get(v___x_344_, 0);
v_nextMacroScope_347_ = lean_ctor_get(v___x_344_, 1);
v_ngen_348_ = lean_ctor_get(v___x_344_, 2);
v_auxDeclNGen_349_ = lean_ctor_get(v___x_344_, 3);
v_traceState_350_ = lean_ctor_get(v___x_344_, 4);
v_recordedDeps_351_ = lean_ctor_get(v___x_344_, 6);
v_messages_352_ = lean_ctor_get(v___x_344_, 7);
v_infoState_353_ = lean_ctor_get(v___x_344_, 8);
v_snapshotTasks_354_ = lean_ctor_get(v___x_344_, 9);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_344_, 5);
lean_dec(v_unused_366_);
v___x_356_ = v___x_344_;
v_isShared_357_ = v_isSharedCheck_365_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snapshotTasks_354_);
lean_inc(v_infoState_353_);
lean_inc(v_messages_352_);
lean_inc(v_recordedDeps_351_);
lean_inc(v_traceState_350_);
lean_inc(v_auxDeclNGen_349_);
lean_inc(v_ngen_348_);
lean_inc(v_nextMacroScope_347_);
lean_inc(v_env_346_);
lean_dec(v___x_344_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_365_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_name_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v_name_358_ = lean_ctor_get(v_toSignature_345_, 0);
lean_inc(v_name_358_);
v___x_359_ = l_Lean_Compiler_LCNF_recordFinalImpureDecl(v_env_346_, v_name_358_);
v___x_360_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 5, v___x_360_);
lean_ctor_set(v___x_356_, 0, v___x_359_);
v___x_362_ = v___x_356_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextMacroScope_347_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_ngen_348_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_auxDeclNGen_349_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_traceState_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_recordedDeps_351_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_messages_352_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_infoState_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 9, v_snapshotTasks_354_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_st_ref_put(v___y_327_, v___x_362_);
v_a_335_ = v_a_342_;
goto v___jp_334_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_a_342_);
lean_dec_ref(v_bs_x27_333_);
v_a_367_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_343_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_343_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_341_, 1);
v_a_335_ = v_a_375_;
goto v___jp_334_;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_bs_x27_333_);
v_a_376_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_341_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_341_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
v___jp_334_:
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_324_, v___x_336_);
v___x_338_ = lean_array_uset(v_bs_x27_333_, v_i_324_, v_a_335_);
v_i_324_ = v___x_337_;
v_bs_325_ = v___x_338_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___boxed(lean_object* v_sz_384_, lean_object* v_i_385_, lean_object* v_bs_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_384_);
lean_dec(v_sz_384_);
v_i_boxed_391_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_boxed_390_, v_i_boxed_391_, v_bs_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(lean_object* v_decls_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_sz_399_ = lean_array_size(v_decls_393_);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_399_, v___x_400_, v_decls_393_, v___y_396_, v___y_397_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0___boxed(lean_object* v_decls_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(v_decls_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(size_t v_sz_420_, size_t v_i_421_, lean_object* v_bs_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_420_, v_i_421_, v_bs_422_, v___y_425_, v___y_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___boxed(lean_object* v_sz_429_, lean_object* v_i_430_, lean_object* v_bs_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
size_t v_sz_boxed_437_; size_t v_i_boxed_438_; lean_object* v_res_439_; 
v_sz_boxed_437_ = lean_unbox_usize(v_sz_429_);
lean_dec(v_sz_429_);
v_i_boxed_438_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(v_sz_boxed_437_, v_i_boxed_438_, v_bs_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_439_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0(void){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = 0;
v___x_442_ = 0;
v___x_443_ = l_Lean_Compiler_LCNF_cse(v___x_442_, v___x_441_, v___x_440_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2(void){
_start:
{
uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = 0;
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_450_ = l_Lean_Compiler_LCNF_simp(v___x_449_, v___x_448_, v___x_447_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3(void){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = 0;
v___x_453_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = l_Lean_Compiler_LCNF_findJoinPoints(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5(void){
_start:
{
uint8_t v___x_456_; lean_object* v___x_457_; 
v___x_456_ = 0;
v___x_457_ = l_Lean_Compiler_LCNF_reduceJpArity(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7(void){
_start:
{
uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = 0;
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__6));
v___x_463_ = l_Lean_Compiler_LCNF_simp(v___x_462_, v___x_461_, v___x_460_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = l_Lean_Compiler_LCNF_findJoinPoints(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9(void){
_start:
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = 0;
v___x_467_ = lean_unsigned_to_nat(2u);
v___x_468_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_469_ = l_Lean_Compiler_LCNF_simp(v___x_468_, v___x_467_, v___x_466_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10(void){
_start:
{
lean_object* v___x_470_; uint8_t v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = 0;
v___x_472_ = 0;
v___x_473_ = l_Lean_Compiler_LCNF_cse(v___x_472_, v___x_471_, v___x_470_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11(void){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; 
v___x_474_ = 0;
v___x_475_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_476_ = l_Lean_Compiler_LCNF_toMono;
v___x_477_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__11, &l_Lean_Compiler_LCNF_builtinPassManager___closed__11_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11);
v___x_478_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_saveBase));
v___x_479_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__10, &l_Lean_Compiler_LCNF_builtinPassManager___closed__10_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10);
v___x_480_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__9, &l_Lean_Compiler_LCNF_builtinPassManager___closed__9_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9);
v___x_481_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__8, &l_Lean_Compiler_LCNF_builtinPassManager___closed__8_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8);
v___x_482_ = l_Lean_Compiler_LCNF_specialize;
v___x_483_ = l_Lean_Compiler_LCNF_checkTemplateVisibility;
v___x_484_ = l_Lean_Compiler_LCNF_eagerLambdaLifting;
v___x_485_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__7, &l_Lean_Compiler_LCNF_builtinPassManager___closed__7_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7);
v___x_486_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__5, &l_Lean_Compiler_LCNF_builtinPassManager___closed__5_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5);
v___x_487_ = l_Lean_Compiler_LCNF_pullFunDecls;
v___x_488_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__4, &l_Lean_Compiler_LCNF_builtinPassManager___closed__4_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4);
v___x_489_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__3, &l_Lean_Compiler_LCNF_builtinPassManager___closed__3_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3);
v___x_490_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__2, &l_Lean_Compiler_LCNF_builtinPassManager___closed__2_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2);
v___x_491_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__0, &l_Lean_Compiler_LCNF_builtinPassManager___closed__0_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0);
v___x_492_ = l_Lean_Compiler_LCNF_pullInstances;
v___x_493_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_init));
v___x_494_ = lean_unsigned_to_nat(18u);
v___x_495_ = lean_mk_empty_array_with_capacity(v___x_494_);
v___x_496_ = lean_array_push(v___x_495_, v___x_493_);
v___x_497_ = lean_array_push(v___x_496_, v___x_492_);
v___x_498_ = lean_array_push(v___x_497_, v___x_491_);
v___x_499_ = lean_array_push(v___x_498_, v___x_490_);
v___x_500_ = lean_array_push(v___x_499_, v___x_489_);
v___x_501_ = lean_array_push(v___x_500_, v___x_488_);
v___x_502_ = lean_array_push(v___x_501_, v___x_487_);
v___x_503_ = lean_array_push(v___x_502_, v___x_486_);
v___x_504_ = lean_array_push(v___x_503_, v___x_485_);
v___x_505_ = lean_array_push(v___x_504_, v___x_484_);
v___x_506_ = lean_array_push(v___x_505_, v___x_483_);
v___x_507_ = lean_array_push(v___x_506_, v___x_482_);
v___x_508_ = lean_array_push(v___x_507_, v___x_481_);
v___x_509_ = lean_array_push(v___x_508_, v___x_480_);
v___x_510_ = lean_array_push(v___x_509_, v___x_479_);
v___x_511_ = lean_array_push(v___x_510_, v___x_478_);
v___x_512_ = lean_array_push(v___x_511_, v___x_477_);
v___x_513_ = lean_array_push(v___x_512_, v___x_476_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13(void){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = 1;
v___x_515_ = lean_unsigned_to_nat(3u);
v___x_516_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_517_ = l_Lean_Compiler_LCNF_simp(v___x_516_, v___x_515_, v___x_514_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14(void){
_start:
{
uint8_t v___x_518_; lean_object* v___x_519_; 
v___x_518_ = 1;
v___x_519_ = l_Lean_Compiler_LCNF_reduceJpArity(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15(void){
_start:
{
uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = 1;
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16(void){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = 1;
v___x_525_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17(void){
_start:
{
uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = 1;
v___x_527_ = lean_unsigned_to_nat(4u);
v___x_528_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_529_ = l_Lean_Compiler_LCNF_simp(v___x_528_, v___x_527_, v___x_526_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18(void){
_start:
{
lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_unsigned_to_nat(2u);
v___x_531_ = 1;
v___x_532_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_533_ = l_Lean_Compiler_LCNF_lambdaLifting;
v___x_534_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__18, &l_Lean_Compiler_LCNF_builtinPassManager___closed__18_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18);
v___x_535_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__17, &l_Lean_Compiler_LCNF_builtinPassManager___closed__17_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17);
v___x_536_ = l_Lean_Compiler_LCNF_commonJoinPointArgs;
v___x_537_ = l_Lean_Compiler_LCNF_reduceArity;
v___x_538_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__16, &l_Lean_Compiler_LCNF_builtinPassManager___closed__16_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16);
v___x_539_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__15, &l_Lean_Compiler_LCNF_builtinPassManager___closed__15_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15);
v___x_540_ = l_Lean_Compiler_LCNF_structProjCases;
v___x_541_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__14, &l_Lean_Compiler_LCNF_builtinPassManager___closed__14_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14);
v___x_542_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__13, &l_Lean_Compiler_LCNF_builtinPassManager___closed__13_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13);
v___x_543_ = lean_unsigned_to_nat(10u);
v___x_544_ = lean_mk_empty_array_with_capacity(v___x_543_);
v___x_545_ = lean_array_push(v___x_544_, v___x_542_);
v___x_546_ = lean_array_push(v___x_545_, v___x_541_);
v___x_547_ = lean_array_push(v___x_546_, v___x_540_);
v___x_548_ = lean_array_push(v___x_547_, v___x_539_);
v___x_549_ = lean_array_push(v___x_548_, v___x_538_);
v___x_550_ = lean_array_push(v___x_549_, v___x_537_);
v___x_551_ = lean_array_push(v___x_550_, v___x_536_);
v___x_552_ = lean_array_push(v___x_551_, v___x_535_);
v___x_553_ = lean_array_push(v___x_552_, v___x_534_);
v___x_554_ = lean_array_push(v___x_553_, v___x_533_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20(void){
_start:
{
uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = 1;
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(v___x_556_, v___x_555_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21(void){
_start:
{
uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = 1;
v___x_559_ = lean_unsigned_to_nat(5u);
v___x_560_ = ((lean_object*)(l_Lean_Compiler_LCNF_builtinPassManager___closed__1));
v___x_561_ = l_Lean_Compiler_LCNF_simp(v___x_560_, v___x_559_, v___x_558_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22(void){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; 
v___x_562_ = lean_unsigned_to_nat(2u);
v___x_563_ = 0;
v___x_564_ = 1;
v___x_565_ = l_Lean_Compiler_LCNF_cse(v___x_564_, v___x_563_, v___x_562_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23(void){
_start:
{
uint8_t v___x_566_; lean_object* v___x_567_; 
v___x_566_ = 1;
v___x_567_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_568_ = l_Lean_Compiler_LCNF_toImpure;
v___x_569_ = l_Lean_Compiler_LCNF_extractClosed;
v___x_570_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__23, &l_Lean_Compiler_LCNF_builtinPassManager___closed__23_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23);
v___x_571_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_saveMono));
v___x_572_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__22, &l_Lean_Compiler_LCNF_builtinPassManager___closed__22_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22);
v___x_573_ = l_Lean_Compiler_LCNF_elimDeadBranches;
v___x_574_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__21, &l_Lean_Compiler_LCNF_builtinPassManager___closed__21_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21);
v___x_575_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__20, &l_Lean_Compiler_LCNF_builtinPassManager___closed__20_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20);
v___x_576_ = lean_unsigned_to_nat(8u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_array_push(v___x_577_, v___x_575_);
v___x_579_ = lean_array_push(v___x_578_, v___x_574_);
v___x_580_ = lean_array_push(v___x_579_, v___x_573_);
v___x_581_ = lean_array_push(v___x_580_, v___x_572_);
v___x_582_ = lean_array_push(v___x_581_, v___x_571_);
v___x_583_ = lean_array_push(v___x_582_, v___x_570_);
v___x_584_ = lean_array_push(v___x_583_, v___x_569_);
v___x_585_ = lean_array_push(v___x_584_, v___x_568_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = l_Lean_Compiler_LCNF_pushProj(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26(void){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = 2;
v___x_590_ = l_Lean_Compiler_LCNF_elimDeadVars(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = l_Lean_Compiler_LCNF_pushProj(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28(void){
_start:
{
uint8_t v___x_593_; lean_object* v___x_594_; 
v___x_593_ = 2;
v___x_594_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_593_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_595_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_saveImpure));
v___x_596_ = l_Lean_Compiler_LCNF_toposortPass;
v___x_597_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__28, &l_Lean_Compiler_LCNF_builtinPassManager___closed__28_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28);
v___x_598_ = l_Lean_Compiler_LCNF_detectSimpleGround;
v___x_599_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__27, &l_Lean_Compiler_LCNF_builtinPassManager___closed__27_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27);
v___x_600_ = l_Lean_Compiler_LCNF_coalesceRC;
v___x_601_ = l_Lean_Compiler_LCNF_expandResetReuse;
v___x_602_ = l_Lean_Compiler_LCNF_explicitRc;
v___x_603_ = l_Lean_Compiler_LCNF_explicitBoxing;
v___x_604_ = l_Lean_Compiler_LCNF_inferBorrow;
v___x_605_ = l_Lean_Compiler_LCNF_simpCase;
v___x_606_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__26, &l_Lean_Compiler_LCNF_builtinPassManager___closed__26_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26);
v___x_607_ = l_Lean_Compiler_LCNF_insertResetReuse;
v___x_608_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__25, &l_Lean_Compiler_LCNF_builtinPassManager___closed__25_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25);
v___x_609_ = lean_unsigned_to_nat(14u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_array_push(v___x_610_, v___x_608_);
v___x_612_ = lean_array_push(v___x_611_, v___x_607_);
v___x_613_ = lean_array_push(v___x_612_, v___x_606_);
v___x_614_ = lean_array_push(v___x_613_, v___x_605_);
v___x_615_ = lean_array_push(v___x_614_, v___x_604_);
v___x_616_ = lean_array_push(v___x_615_, v___x_603_);
v___x_617_ = lean_array_push(v___x_616_, v___x_602_);
v___x_618_ = lean_array_push(v___x_617_, v___x_601_);
v___x_619_ = lean_array_push(v___x_618_, v___x_600_);
v___x_620_ = lean_array_push(v___x_619_, v___x_599_);
v___x_621_ = lean_array_push(v___x_620_, v___x_598_);
v___x_622_ = lean_array_push(v___x_621_, v___x_597_);
v___x_623_ = lean_array_push(v___x_622_, v___x_596_);
v___x_624_ = lean_array_push(v___x_623_, v___x_595_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_625_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__29, &l_Lean_Compiler_LCNF_builtinPassManager___closed__29_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29);
v___x_626_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__24, &l_Lean_Compiler_LCNF_builtinPassManager___closed__24_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24);
v___x_627_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__19, &l_Lean_Compiler_LCNF_builtinPassManager___closed__19_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19);
v___x_628_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__12, &l_Lean_Compiler_LCNF_builtinPassManager___closed__12_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12);
v___x_629_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_626_);
lean_ctor_set(v___x_629_, 3, v___x_625_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Lean_Compiler_LCNF_builtinPassManager___closed__30, &l_Lean_Compiler_LCNF_builtinPassManager___closed__30_once, _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object* v_as_631_, size_t v_sz_632_, size_t v_i_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_lt(v_i_633_, v_sz_632_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_b_634_);
return v___x_639_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_array_uget_borrowed(v_as_631_, v_i_633_);
lean_inc(v_a_640_);
v___x_641_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_b_634_, v_a_640_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; size_t v___x_643_; size_t v___x_644_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_633_, v___x_643_);
v_i_633_ = v___x_644_;
v_b_634_ = v_a_642_;
goto _start;
}
else
{
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object* v_as_646_, lean_object* v_sz_647_, lean_object* v_i_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
size_t v_sz_boxed_653_; size_t v_i_boxed_654_; lean_object* v_res_655_; 
v_sz_boxed_653_ = lean_unbox_usize(v_sz_647_);
lean_dec(v_sz_647_);
v_i_boxed_654_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(v_as_646_, v_sz_boxed_653_, v_i_boxed_654_, v_b_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_as_646_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object* v_as_656_, size_t v_sz_657_, size_t v_i_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v___x_663_; 
v___x_663_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v_b_659_);
return v___x_664_;
}
else
{
lean_object* v_a_665_; size_t v_sz_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_a_665_ = lean_array_uget_borrowed(v_as_656_, v_i_658_);
v_sz_666_ = lean_array_size(v_a_665_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(v_a_665_, v_sz_666_, v___x_667_, v_b_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; size_t v___x_670_; size_t v___x_671_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_add(v_i_658_, v___x_670_);
v_i_658_ = v___x_671_;
v_b_659_ = v_a_669_;
goto _start;
}
else
{
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object* v_as_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_681_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(v_as_673_, v_sz_boxed_680_, v_i_boxed_681_, v_b_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v_as_673_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object* v_importedDeclNames_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_m_687_; size_t v_sz_688_; size_t v___x_689_; lean_object* v___x_690_; 
v_m_687_ = l_Lean_Compiler_LCNF_builtinPassManager;
v_sz_688_ = lean_array_size(v_importedDeclNames_683_);
v___x_689_ = ((size_t)0ULL);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(v_importedDeclNames_683_, v_sz_688_, v___x_689_, v_m_687_, v_a_684_, v_a_685_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object* v_importedDeclNames_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Compiler_LCNF_runImportedDecls(v_importedDeclNames_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec_ref(v_importedDeclNames_691_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_s_696_){
_start:
{
lean_object* v_fst_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_fst_697_ = lean_ctor_get(v_s_696_, 0);
lean_inc(v_fst_697_);
lean_dec_ref(v_s_696_);
v___x_698_ = l_List_reverse___redArg(v_fst_697_);
v___x_699_ = lean_array_mk(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_x_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_box(0);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v_x_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v_x_702_);
lean_dec_ref(v_x_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_x_704_, lean_object* v_s_705_){
_start:
{
lean_object* v_fst_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_fst_706_ = lean_ctor_get(v_s_705_, 0);
lean_inc(v_fst_706_);
lean_dec_ref(v_s_705_);
v___x_707_ = l_List_reverse___redArg(v_fst_706_);
v___x_708_ = lean_array_mk(v___x_707_);
lean_inc_ref_n(v___x_708_, 2);
v___x_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_ctor_set(v___x_709_, 2, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v_x_710_, lean_object* v_s_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v_x_710_, v_s_711_);
lean_dec_ref(v_x_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_fst_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_731_; 
v_fst_715_ = lean_ctor_get(v_x_713_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_x_713_, 1);
lean_dec(v_unused_732_);
v___x_717_ = v_x_713_;
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_fst_715_);
lean_dec(v_x_713_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_730_; 
v_fst_719_ = lean_ctor_get(v_x_714_, 0);
v_snd_720_ = lean_ctor_get(v_x_714_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_714_);
if (v_isSharedCheck_730_ == 0)
{
v___x_722_ = v_x_714_;
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snd_720_);
lean_inc(v_fst_719_);
lean_dec(v_x_714_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 1);
lean_ctor_set(v___x_717_, 1, v_fst_715_);
lean_ctor_set(v___x_717_, 0, v_fst_719_);
v___x_725_ = v___x_717_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_fst_719_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_fst_715_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_720_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v___x_733_, lean_object* v_ns_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_runImportedDecls___boxed), 4, 1);
lean_closure_set(v___x_737_, 0, v_ns_734_);
v___x_738_ = l_Lean_ImportM_runCoreM___redArg(v___x_737_, v___y_735_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_733_);
lean_ctor_set(v___x_743_, 1, v_a_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v___x_733_);
v_a_748_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_738_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v___x_756_, lean_object* v_ns_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v___x_756_, v_ns_757_, v___y_758_);
lean_dec_ref(v___y_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(lean_object* v___x_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v___x_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v___x_764_);
return v_res_766_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_Compiler_LCNF_builtinPassManager;
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_785_; lean_object* v___f_786_; 
v___x_785_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___f_786_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_786_, 0, v___x_785_);
return v___f_786_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_787_ = 0;
v___x_788_ = lean_box(0);
v___x_789_ = lean_box(2);
v___f_790_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_791_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_792_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_793_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___f_794_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___x_795_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_796_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___f_794_);
lean_ctor_set(v___x_796_, 2, v___f_793_);
lean_ctor_set(v___x_796_, 3, v___f_792_);
lean_ctor_set(v___x_796_, 4, v___f_791_);
lean_ctor_set(v___x_796_, 5, v___f_790_);
lean_ctor_set(v___x_796_, 6, v___x_789_);
lean_ctor_set(v___x_796_, 7, v___x_788_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*8, v___x_787_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___f_797_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_798_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___f_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
v___x_802_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
return v_res_804_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_Compiler_LCNF_instInhabitedPassManager_default;
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___x_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_env_812_; lean_object* v___x_813_; lean_object* v_toEnvExtension_814_; lean_object* v_asyncMode_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_snd_818_; lean_object* v___x_819_; 
v___x_810_ = lean_obj_once(&l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0, &l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0);
v___x_811_ = lean_st_ref_get(v_a_808_);
v_env_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_env_812_);
lean_dec(v___x_811_);
v___x_813_ = l_Lean_Compiler_LCNF_passManagerExt;
v_toEnvExtension_814_ = lean_ctor_get(v___x_813_, 0);
v_asyncMode_815_ = lean_ctor_get(v_toEnvExtension_814_, 2);
v___x_816_ = lean_box(0);
v___x_817_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_810_, v___x_813_, v_env_812_, v_asyncMode_815_, v___x_816_);
v_snd_818_ = lean_ctor_get(v___x_817_, 1);
lean_inc(v_snd_818_);
lean_dec(v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_snd_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_820_);
lean_dec(v_a_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Compiler_LCNF_getPassManager(v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_830_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
lean_ctor_set(v___x_835_, 3, v___x_834_);
lean_ctor_set(v___x_835_, 4, v___x_833_);
lean_ctor_set(v___x_835_, 5, v___x_833_);
lean_ctor_set(v___x_835_, 6, v___x_833_);
lean_ctor_set(v___x_835_, 7, v___x_833_);
lean_ctor_set(v___x_835_, 8, v___x_833_);
lean_ctor_set(v___x_835_, 9, v___x_833_);
lean_ctor_set(v___x_835_, 10, v___x_833_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_unsigned_to_nat(32u);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_839_ = ((size_t)5ULL);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_unsigned_to_nat(32u);
v___x_842_ = lean_mk_empty_array_with_capacity(v___x_841_);
v___x_843_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2);
v___x_844_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v___x_842_);
lean_ctor_set(v___x_844_, 2, v___x_840_);
lean_ctor_set(v___x_844_, 3, v___x_840_);
lean_ctor_set_usize(v___x_844_, 4, v___x_839_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_845_ = lean_box(1);
v___x_846_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3);
v___x_847_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0);
v___x_848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
lean_ctor_set(v___x_848_, 2, v___x_845_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(lean_object* v_msgData_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_toCold_854_; lean_object* v_env_855_; lean_object* v_options_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_853_ = lean_st_ref_get(v___y_851_);
v_toCold_854_ = lean_ctor_get(v___y_850_, 0);
v_env_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_853_);
v_options_856_ = lean_ctor_get(v_toCold_854_, 2);
v___x_857_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1);
v___x_858_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4);
lean_inc_ref(v_options_856_);
v___x_859_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_859_, 0, v_env_855_);
lean_ctor_set(v___x_859_, 1, v___x_857_);
lean_ctor_set(v___x_859_, 2, v___x_858_);
lean_ctor_set(v___x_859_, 3, v_options_856_);
v___x_860_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_msgData_849_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(v_msgData_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(lean_object* v_msg_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_ref_871_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_ref_871_ = lean_ctor_get(v___y_868_, 2);
v___x_872_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(v_msg_867_, v___y_868_, v___y_869_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_inc(v_ref_871_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_ref_871_);
lean_ctor_set(v___x_877_, 1, v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg___boxed(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(lean_object* v_attrName_902_, lean_object* v_declName_903_, lean_object* v_givenType_904_, lean_object* v_expectedType_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_909_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1);
v___x_910_ = l_Lean_MessageData_ofName(v_attrName_902_);
lean_inc_ref(v___x_910_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = 0;
v___x_915_ = l_Lean_MessageData_ofConstName(v_declName_903_, v___x_914_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_913_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_indentExpr(v_givenType_904_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_910_);
v___x_924_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_Lean_indentExpr(v_expectedType_905_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_927_, v___y_906_, v___y_907_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___boxed(lean_object* v_attrName_929_, lean_object* v_declName_930_, lean_object* v_givenType_931_, lean_object* v_expectedType_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v_attrName_929_, v_declName_930_, v_givenType_931_, v_expectedType_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_ref_937_, lean_object* v_msg_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_toCold_942_; lean_object* v_currRecDepth_943_; lean_object* v_ref_944_; uint16_t v_optionFlags_945_; uint8_t v_suppressElabErrors_946_; uint8_t v_isRecordingDeps_947_; lean_object* v_ref_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_toCold_942_ = lean_ctor_get(v___y_939_, 0);
v_currRecDepth_943_ = lean_ctor_get(v___y_939_, 1);
v_ref_944_ = lean_ctor_get(v___y_939_, 2);
v_optionFlags_945_ = lean_ctor_get_uint16(v___y_939_, sizeof(void*)*3);
v_suppressElabErrors_946_ = lean_ctor_get_uint8(v___y_939_, sizeof(void*)*3 + 2);
v_isRecordingDeps_947_ = lean_ctor_get_uint8(v___y_939_, sizeof(void*)*3 + 3);
v_ref_948_ = l_Lean_replaceRef(v_ref_937_, v_ref_944_);
lean_inc(v_currRecDepth_943_);
lean_inc_ref(v_toCold_942_);
v___x_949_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_949_, 0, v_toCold_942_);
lean_ctor_set(v___x_949_, 1, v_currRecDepth_943_);
lean_ctor_set(v___x_949_, 2, v_ref_948_);
lean_ctor_set_uint16(v___x_949_, sizeof(void*)*3, v_optionFlags_945_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*3 + 2, v_suppressElabErrors_946_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*3 + 3, v_isRecordingDeps_947_);
v___x_950_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_938_, v___x_949_, v___y_940_);
lean_dec_ref_known(v___x_949_, 3);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_ref_951_, lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_951_, v_msg_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v_ref_951_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_msg_978_, lean_object* v_declHint_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_env_984_; uint8_t v___x_985_; 
v___x_982_ = lean_box(0);
v___x_983_ = lean_st_ref_get(v___y_980_);
v_env_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc_ref(v_env_984_);
lean_dec(v___x_983_);
v___x_985_ = l_Lean_Name_isAnonymous(v_declHint_979_);
if (v___x_985_ == 0)
{
uint8_t v_isExporting_986_; 
v_isExporting_986_ = lean_ctor_get_uint8(v_env_984_, sizeof(void*)*8);
if (v_isExporting_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec_ref(v_env_984_);
lean_dec(v_declHint_979_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_msg_978_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; uint8_t v___x_989_; 
lean_inc_ref(v_env_984_);
v___x_988_ = l_Lean_Environment_setExporting(v_env_984_, v___x_985_);
lean_inc(v_declHint_979_);
lean_inc_ref(v___x_988_);
v___x_989_ = l_Lean_Environment_contains(v___x_988_, v_declHint_979_, v_isExporting_986_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
lean_dec_ref(v___x_988_);
lean_dec_ref(v_env_984_);
lean_dec(v_declHint_979_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_msg_978_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_c_996_; lean_object* v___x_997_; 
v___x_991_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1);
v___x_992_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4);
v___x_993_ = l_Lean_Options_empty;
v___x_994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_994_, 0, v___x_988_);
lean_ctor_set(v___x_994_, 1, v___x_991_);
lean_ctor_set(v___x_994_, 2, v___x_992_);
lean_ctor_set(v___x_994_, 3, v___x_993_);
lean_inc(v_declHint_979_);
v___x_995_ = l_Lean_MessageData_ofConstName(v_declHint_979_, v___x_985_);
v_c_996_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_996_, 0, v___x_994_);
lean_ctor_set(v_c_996_, 1, v___x_995_);
v___x_997_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_984_, v_declHint_979_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec_ref(v_env_984_);
lean_dec(v_declHint_979_);
v___x_998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v_c_996_);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_MessageData_note(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_msg_978_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
else
{
lean_object* v_val_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1039_; 
v_val_1005_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1007_ = v___x_997_;
v_isShared_1008_ = v_isSharedCheck_1039_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_val_1005_);
lean_dec(v___x_997_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1039_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_mod_1011_; uint8_t v___x_1012_; 
v___x_1009_ = l_Lean_Environment_header(v_env_984_);
lean_dec_ref(v_env_984_);
v___x_1010_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1009_);
v_mod_1011_ = lean_array_get(v___x_982_, v___x_1010_, v_val_1005_);
lean_dec(v_val_1005_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l_Lean_isPrivateName(v_declHint_979_);
lean_dec(v_declHint_979_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_c_996_);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofName(v_mod_1011_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_MessageData_note(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_msg_978_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set_tag(v___x_1007_, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1022_);
v___x_1024_ = v___x_1007_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1026_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_c_996_);
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Lean_MessageData_ofName(v_mod_1011_);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_MessageData_note(v___x_1033_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_msg_978_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set_tag(v___x_1007_, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1035_);
v___x_1037_ = v___x_1007_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1040_; 
lean_dec_ref(v_env_984_);
lean_dec(v_declHint_979_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_msg_978_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1041_, lean_object* v_declHint_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_1041_, v_declHint_1042_, v___y_1043_);
lean_dec(v___y_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_msg_1046_, lean_object* v_declHint_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v___x_1051_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_1046_, v_declHint_1047_, v___y_1049_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = l_Lean_unknownIdentifierMessageTag;
v___x_1057_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msg_1062_, lean_object* v_declHint_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_1062_, v_declHint_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1068_, lean_object* v_msg_1069_, lean_object* v_declHint_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_1069_, v_declHint_1070_, v___y_1071_, v___y_1072_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1068_, v_a_1075_, v___y_1071_, v___y_1072_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1077_, lean_object* v_msg_1078_, lean_object* v_declHint_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1077_, v_msg_1078_, v_declHint_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v_ref_1077_);
return v_res_1083_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1090_, lean_object* v_constName_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1095_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1096_ = 0;
lean_inc(v_constName_1091_);
v___x_1097_ = l_Lean_MessageData_ofConstName(v_constName_1091_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1095_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1090_, v___x_1100_, v_constName_1091_, v___y_1092_, v___y_1093_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1102_, lean_object* v_constName_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_1102_, v_constName_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v_ref_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_ref_1112_; lean_object* v___x_1113_; 
v_ref_1112_ = lean_ctor_get(v___y_1109_, 2);
v___x_1113_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_1112_, v_constName_1108_, v___y_1109_, v___y_1110_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v_env_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = lean_st_ref_get(v___y_1121_);
v_env_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc_ref(v_env_1124_);
lean_dec(v___x_1123_);
v___x_1125_ = 0;
lean_inc(v_constName_1119_);
v___x_1126_ = l_Lean_Environment_find_x3f(v_env_1124_, v_constName_1119_, v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_1119_, v___y_1120_, v___y_1121_);
return v___x_1127_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_constName_1119_);
v_val_1128_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_val_1128_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0___boxed(lean_object* v_constName_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(v_constName_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1140_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__4(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__3));
v___x_1152_ = l_Lean_mkConst(v___x_1151_, v___x_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object* v_declName_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
lean_inc(v_declName_1153_);
v___x_1157_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(v_declName_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___x_1166_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1166_ = l_Lean_ConstantInfo_type(v_a_1158_);
if (lean_obj_tag(v___x_1166_) == 4)
{
lean_object* v_declName_1167_; 
v_declName_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_declName_1167_);
lean_dec_ref_known(v___x_1166_, 2);
if (lean_obj_tag(v_declName_1167_) == 1)
{
lean_object* v_pre_1168_; 
v_pre_1168_ = lean_ctor_get(v_declName_1167_, 0);
lean_inc(v_pre_1168_);
if (lean_obj_tag(v_pre_1168_) == 1)
{
lean_object* v_pre_1169_; 
v_pre_1169_ = lean_ctor_get(v_pre_1168_, 0);
lean_inc(v_pre_1169_);
if (lean_obj_tag(v_pre_1169_) == 1)
{
lean_object* v_pre_1170_; 
v_pre_1170_ = lean_ctor_get(v_pre_1169_, 0);
lean_inc(v_pre_1170_);
if (lean_obj_tag(v_pre_1170_) == 1)
{
lean_object* v_pre_1171_; 
v_pre_1171_ = lean_ctor_get(v_pre_1170_, 0);
lean_inc(v_pre_1171_);
if (lean_obj_tag(v_pre_1171_) == 0)
{
lean_object* v_str_1172_; lean_object* v_str_1173_; lean_object* v_str_1174_; lean_object* v_str_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_str_1172_ = lean_ctor_get(v_declName_1167_, 1);
lean_inc_ref(v_str_1172_);
lean_dec_ref_known(v_declName_1167_, 2);
v_str_1173_ = lean_ctor_get(v_pre_1168_, 1);
lean_inc_ref(v_str_1173_);
lean_dec_ref_known(v_pre_1168_, 2);
v_str_1174_ = lean_ctor_get(v_pre_1169_, 1);
lean_inc_ref(v_str_1174_);
lean_dec_ref_known(v_pre_1169_, 2);
v_str_1175_ = lean_ctor_get(v_pre_1170_, 1);
lean_inc_ref(v_str_1175_);
lean_dec_ref_known(v_pre_1170_, 2);
v___x_1176_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_1177_ = lean_string_dec_eq(v_str_1175_, v___x_1176_);
lean_dec_ref(v_str_1175_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_str_1174_);
lean_dec_ref(v_str_1173_);
lean_dec_ref(v_str_1172_);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_1179_ = lean_string_dec_eq(v_str_1174_, v___x_1178_);
lean_dec_ref(v_str_1174_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v_str_1173_);
lean_dec_ref(v_str_1172_);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_));
v___x_1181_ = lean_string_dec_eq(v_str_1173_, v___x_1180_);
lean_dec_ref(v_str_1173_);
if (v___x_1181_ == 0)
{
lean_dec_ref(v_str_1172_);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__2));
v___x_1183_ = lean_string_dec_eq(v_str_1172_, v___x_1182_);
lean_dec_ref(v_str_1172_);
if (v___x_1183_ == 0)
{
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1184_; lean_object* v_a_1185_; lean_object* v___x_1186_; 
lean_dec(v_a_1158_);
v___x_1184_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_1155_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1184_);
lean_inc(v_declName_1153_);
v___x_1186_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_a_1185_, v_declName_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1220_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1220_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1220_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v_nextMacroScope_1193_; lean_object* v_ngen_1194_; lean_object* v_auxDeclNGen_1195_; lean_object* v_traceState_1196_; lean_object* v_recordedDeps_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1218_; 
v___x_1191_ = lean_st_ref_take(v_a_1155_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1193_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1194_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1195_ = lean_ctor_get(v___x_1191_, 3);
v_traceState_1196_ = lean_ctor_get(v___x_1191_, 4);
v_recordedDeps_1197_ = lean_ctor_get(v___x_1191_, 6);
v_messages_1198_ = lean_ctor_get(v___x_1191_, 7);
v_infoState_1199_ = lean_ctor_get(v___x_1191_, 8);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1191_, 9);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v___x_1191_, 5);
lean_dec(v_unused_1219_);
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1218_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_recordedDeps_1197_);
lean_inc(v_traceState_1196_);
lean_inc(v_auxDeclNGen_1195_);
lean_inc(v_ngen_1194_);
lean_inc(v_nextMacroScope_1193_);
lean_inc(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1218_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v_toEnvExtension_1205_; lean_object* v_asyncMode_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1204_ = l_Lean_Compiler_LCNF_passManagerExt;
v_toEnvExtension_1205_ = lean_ctor_get(v___x_1204_, 0);
v_asyncMode_1206_ = lean_ctor_get(v_toEnvExtension_1205_, 2);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_declName_1153_);
lean_ctor_set(v___x_1208_, 1, v_a_1187_);
v___x_1209_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1204_, v_env_1192_, v___x_1208_, v_asyncMode_1206_, v_pre_1171_);
v___x_1210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 5, v___x_1210_);
lean_ctor_set(v___x_1202_, 0, v___x_1209_);
v___x_1212_ = v___x_1202_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_nextMacroScope_1193_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_ngen_1194_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_auxDeclNGen_1195_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_traceState_1196_);
lean_ctor_set(v_reuseFailAlloc_1217_, 5, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_recordedDeps_1197_);
lean_ctor_set(v_reuseFailAlloc_1217_, 7, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1217_, 8, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1217_, 9, v_snapshotTasks_1200_);
v___x_1212_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_st_ref_put(v_a_1155_, v___x_1212_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1207_);
v___x_1215_ = v___x_1189_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1207_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_declName_1153_);
v_a_1221_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1186_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1186_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
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
lean_dec_ref_known(v_pre_1170_, 2);
lean_dec(v_pre_1171_);
lean_dec_ref_known(v_pre_1169_, 2);
lean_dec_ref_known(v_pre_1168_, 2);
lean_dec_ref_known(v_declName_1167_, 2);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
}
else
{
lean_dec(v_pre_1170_);
lean_dec_ref_known(v_pre_1169_, 2);
lean_dec_ref_known(v_pre_1168_, 2);
lean_dec_ref_known(v_declName_1167_, 2);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
}
else
{
lean_dec_ref_known(v_pre_1168_, 2);
lean_dec(v_pre_1169_);
lean_dec_ref_known(v_declName_1167_, 2);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
}
else
{
lean_dec_ref_known(v_declName_1167_, 2);
lean_dec(v_pre_1168_);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
}
else
{
lean_dec(v_declName_1167_);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
}
else
{
lean_dec_ref(v___x_1166_);
v___y_1160_ = v_a_1154_;
v___y_1161_ = v_a_1155_;
goto v___jp_1159_;
}
v___jp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__1));
v___x_1163_ = l_Lean_ConstantInfo_type(v_a_1158_);
lean_dec(v_a_1158_);
v___x_1164_ = lean_obj_once(&l_Lean_Compiler_LCNF_addPass___closed__4, &l_Lean_Compiler_LCNF_addPass___closed__4_once, _init_l_Lean_Compiler_LCNF_addPass___closed__4);
v___x_1165_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v___x_1162_, v_declName_1153_, v___x_1163_, v___x_1164_, v___y_1160_, v___y_1161_);
return v___x_1165_;
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_declName_1153_);
v_a_1229_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1157_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1157_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___boxed(lean_object* v_declName_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Compiler_LCNF_addPass(v_declName_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(lean_object* v_00_u03b1_1242_, lean_object* v_attrName_1243_, lean_object* v_declName_1244_, lean_object* v_givenType_1245_, lean_object* v_expectedType_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v_attrName_1243_, v_declName_1244_, v_givenType_1245_, v_expectedType_1246_, v___y_1247_, v___y_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_attrName_1252_, lean_object* v_declName_1253_, lean_object* v_givenType_1254_, lean_object* v_expectedType_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(v_00_u03b1_1251_, v_attrName_1252_, v_declName_1253_, v_givenType_1254_, v_expectedType_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(lean_object* v_00_u03b1_1260_, lean_object* v_constName_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(v_00_u03b1_1266_, v_constName_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(lean_object* v_00_u03b1_1272_, lean_object* v_msg_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_1273_, v___y_1274_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_msg_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(v_00_u03b1_1278_, v_msg_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1284_, lean_object* v_ref_1285_, lean_object* v_constName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_1285_, v_constName_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_ref_1292_, lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(v_00_u03b1_1291_, v_ref_1292_, v_constName_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v_ref_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1298_, lean_object* v_ref_1299_, lean_object* v_msg_1300_, lean_object* v_declHint_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1299_, v_msg_1300_, v_declHint_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_ref_1307_, lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1306_, v_ref_1307_, v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_ref_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(lean_object* v_msg_1314_, lean_object* v_declHint_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_1314_, v_declHint_1315_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___boxed(lean_object* v_msg_1320_, lean_object* v_declHint_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(v_msg_1320_, v_declHint_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b1_1326_, lean_object* v_ref_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1327_, v_msg_1328_, v___y_1329_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_ref_1334_, lean_object* v_msg_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_1333_, v_ref_1334_, v_msg_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v_ref_1334_);
return v_res_1339_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_1342_ = l_Lean_stringToMessageData(v___x_1341_);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_1345_ = l_Lean_stringToMessageData(v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_1349_, uint8_t v_kind_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___y_1360_; 
v___x_1354_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_1355_ = l_Lean_MessageData_ofName(v_name_1349_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
switch(v_kind_1350_)
{
case 0:
{
lean_object* v___x_1367_; 
v___x_1367_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_1360_ = v___x_1367_;
goto v___jp_1359_;
}
case 1:
{
lean_object* v___x_1368_; 
v___x_1368_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_1360_ = v___x_1368_;
goto v___jp_1359_;
}
default: 
{
lean_object* v___x_1369_; 
v___x_1369_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_1360_ = v___x_1369_;
goto v___jp_1359_;
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc_ref(v___y_1360_);
v___x_1361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1360_);
v___x_1362_ = l_Lean_MessageData_ofFormat(v___x_1361_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1358_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_1365_, v___y_1351_, v___y_1352_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_1370_, lean_object* v_kind_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_kind_boxed_1375_; lean_object* v_res_1376_; 
v_kind_boxed_1375_ = lean_unbox(v_kind_1371_);
v_res_1376_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v_name_1370_, v_kind_boxed_1375_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(lean_object* v___x_1377_, lean_object* v_declName_1378_, lean_object* v_stx_1379_, uint8_t v_kind_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1379_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1396_) == 0)
{
uint8_t v___x_1397_; uint8_t v___x_1398_; 
lean_dec_ref_known(v___x_1396_, 1);
v___x_1397_ = 0;
v___x_1398_ = l_Lean_instBEqAttributeKind_beq(v_kind_1380_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_dec(v_declName_1378_);
v___x_1399_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v___x_1377_, v_kind_1380_, v___y_1381_, v___y_1382_);
return v___x_1399_;
}
else
{
goto v___jp_1384_;
}
}
else
{
lean_dec(v_declName_1378_);
lean_dec(v___x_1377_);
return v___x_1396_;
}
v___jp_1384_:
{
lean_object* v___x_1385_; 
lean_inc(v_declName_1378_);
v___x_1385_ = l_Lean_ensureAttrDeclIsMeta(v___x_1377_, v_declName_1378_, v_kind_1380_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref_known(v___x_1385_, 1);
v___x_1386_ = lean_box(0);
v___x_1387_ = l_Lean_Compiler_LCNF_addPass(v_declName_1378_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1387_, 0);
lean_dec(v_unused_1395_);
v___x_1389_ = v___x_1387_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v___x_1387_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1386_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1386_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
return v___x_1387_;
}
}
else
{
lean_dec(v_declName_1378_);
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object* v___x_1400_, lean_object* v_declName_1401_, lean_object* v_stx_1402_, lean_object* v_kind_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_kind_boxed_1407_; lean_object* v_res_1408_; 
v_kind_boxed_1407_ = lean_unbox(v_kind_1403_);
v_res_1408_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(v___x_1400_, v_declName_1401_, v_stx_1402_, v_kind_boxed_1407_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1408_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(lean_object* v___x_1415_, lean_object* v_decl_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1421_ = l_Lean_MessageData_ofName(v___x_1415_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_1424_, v___y_1417_, v___y_1418_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object* v___x_1426_, lean_object* v_decl_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(v___x_1426_, v_decl_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v_decl_1427_);
return v_res_1431_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_unsigned_to_nat(3159741348u);
v___x_1482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1483_ = l_Lean_Name_num___override(v___x_1482_, v___x_1481_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1486_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1487_ = l_Lean_Name_str___override(v___x_1486_, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1490_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1491_ = l_Lean_Name_str___override(v___x_1490_, v___x_1489_);
return v___x_1491_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_unsigned_to_nat(2u);
v___x_1493_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1494_ = l_Lean_Name_num___override(v___x_1493_, v___x_1492_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1500_ = 1;
v___x_1501_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1502_ = ((lean_object*)(l_Lean_Compiler_LCNF_addPass___closed__1));
v___x_1503_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1504_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v___x_1501_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*3, v___x_1500_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___f_1505_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___f_1506_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_));
v___x_1507_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___f_1506_);
lean_ctor_set(v___x_1508_, 2, v___f_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
v___x_1511_ = l_Lean_registerBuiltinAttribute(v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_();
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1514_, lean_object* v_name_1515_, uint8_t v_kind_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v_name_1515_, v_kind_1516_, v___y_1517_, v___y_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_name_1522_, lean_object* v_kind_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v_kind_boxed_1527_; lean_object* v_res_1528_; 
v_kind_boxed_1527_ = lean_unbox(v_kind_1523_);
v_res_1528_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(v_00_u03b1_1521_, v_name_1522_, v_kind_boxed_1527_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1555_ = 1;
v___x_1556_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1557_ = l_Lean_registerTraceClass(v___x_1554_, v___x_1555_, v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref_known(v___x_1557_, 1);
v___x_1558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1559_ = l_Lean_registerTraceClass(v___x_1558_, v___x_1555_, v___x_1556_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref_known(v___x_1559_, 1);
v___x_1560_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1561_ = l_Lean_registerTraceClass(v___x_1560_, v___x_1555_, v___x_1556_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1561_, 1);
v___x_1562_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_));
v___x_1563_ = l_Lean_registerTraceClass(v___x_1562_, v___x_1555_, v___x_1556_);
return v___x_1563_;
}
else
{
return v___x_1561_;
}
}
else
{
return v___x_1559_;
}
}
else
{
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2____boxed(lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_();
return v_res_1565_;
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
lean_object* runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Toposort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
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
res = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
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
lean_object* initialize_Lean_Compiler_LCNF_CoalesceRC(uint8_t builtin);
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
res = initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
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
