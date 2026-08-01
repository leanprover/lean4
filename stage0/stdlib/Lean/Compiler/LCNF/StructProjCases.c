// Lean compiler output
// Module: Lean.Compiler.LCNF.StructProjCases
// Imports: public import Lean.Compiler.LCNF.PrettyPrinter public import Lean.Compiler.LCNF.MonoTypes public import Lean.Compiler.InductiveOverride
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isCtorOverride_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default(uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.StructProjCases"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Lean.Compiler.LCNF.StructProjCases.mkFieldParamsForCtorType"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7;
static const lean_array_object l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1_value;
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Compiler.LCNF.StructProjCases.visitLetValue"};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected struct constructor"};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Compiler.LCNF.StructProjCases.visitCode"};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: projVars.size == params.size\n        "};
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_StructProjCases_visitCode___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_structProjCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_structProjCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_structProjCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_structProjCases___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_structProjCases___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_structProjCases___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_structProjCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structProjCases"};
static const lean_object* l_Lean_Compiler_LCNF_structProjCases___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_structProjCases___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_structProjCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_structProjCases___closed__1_value),LEAN_SCALAR_PTR_LITERAL(182, 117, 202, 29, 170, 173, 9, 143)}};
static const lean_object* l_Lean_Compiler_LCNF_structProjCases___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_structProjCases___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_structProjCases___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_structProjCases___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_structProjCases;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_structProjCases___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 177, 55, 137, 85, 224, 144, 123)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "StructProjCases"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 52, 219, 237, 255, 101, 81, 119)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(105, 251, 133, 248, 241, 140, 104, 7)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 187, 225, 124, 5, 217, 134, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 71, 96, 120, 248, 64, 254, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 189, 223, 162, 94, 57, 84, 248)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 233, 182, 191, 162, 193, 174, 237)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 217, 62, 86, 118, 236, 144, 206)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 28, 180, 213, 68, 181, 122, 243)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 178, 191, 112, 254, 9, 222, 75)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 170, 244, 110, 195, 160, 161, 86)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 235, 8, 140, 62, 66, 155, 79)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)(((size_t)(268537386) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(224, 31, 109, 253, 23, 81, 178, 221)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 204, 205, 14, 107, 184, 70, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 138, 197, 173, 71, 107, 204, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(218, 192, 121, 22, 171, 229, 44, 19)}};
static const lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(lean_object* v_typeName_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_8_; lean_object* v_env_9_; lean_object* v___x_10_; 
v___x_8_ = lean_st_ref_get(v_a_3_);
v_env_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_env_9_);
lean_dec(v___x_8_);
v___x_10_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_9_, v_typeName_1_);
if (lean_obj_tag(v___x_10_) == 1)
{
lean_object* v_val_11_; lean_object* v_ctors_12_; 
v_val_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_val_11_);
lean_dec_ref_known(v___x_10_, 1);
v_ctors_12_ = lean_ctor_get(v_val_11_, 1);
lean_inc(v_ctors_12_);
lean_dec(v_val_11_);
if (lean_obj_tag(v_ctors_12_) == 1)
{
lean_object* v_tail_13_; 
v_tail_13_ = lean_ctor_get(v_ctors_12_, 1);
if (lean_obj_tag(v_tail_13_) == 0)
{
lean_object* v_head_14_; lean_object* v___x_15_; 
v_head_14_ = lean_ctor_get(v_ctors_12_, 0);
lean_inc(v_head_14_);
lean_dec_ref_known(v_ctors_12_, 2);
v___x_15_ = l_Lean_Compiler_isCtorOverride_x3f(v_head_14_, v_a_2_, v_a_3_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
if (lean_obj_tag(v_a_16_) == 1)
{
lean_dec_ref_known(v_a_16_, 1);
return v___x_15_;
}
else
{
lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_24_; 
lean_dec(v_a_16_);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_15_, 0);
lean_dec(v_unused_25_);
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
else
{
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = lean_box(0);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_20_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
return v___x_15_;
}
}
else
{
lean_dec_ref_known(v_ctors_12_, 2);
goto v___jp_5_;
}
}
else
{
lean_dec(v_ctors_12_);
goto v___jp_5_;
}
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_10_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
v___jp_5_:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_box(0);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f___boxed(lean_object* v_typeName_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(v_typeName_28_, v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_32_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_instMonadEIO(lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(lean_object* v_msg_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_77_; 
v___x_42_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0);
v___x_43_ = l_StateRefT_x27_instMonad___redArg(v___x_42_);
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; 
v_unused_78_ = lean_ctor_get(v___x_43_, 1);
lean_dec(v_unused_78_);
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_77_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_toApplicative_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_77_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_toFunctor_48_; lean_object* v_toSeq_49_; lean_object* v_toSeqLeft_50_; lean_object* v_toSeqRight_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_75_; 
v_toFunctor_48_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toSeq_49_ = lean_ctor_get(v_toApplicative_44_, 2);
v_toSeqLeft_50_ = lean_ctor_get(v_toApplicative_44_, 3);
v_toSeqRight_51_ = lean_ctor_get(v_toApplicative_44_, 4);
v_isSharedCheck_75_ = !lean_is_exclusive(v_toApplicative_44_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; 
v_unused_76_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_dec(v_unused_76_);
v___x_53_ = v_toApplicative_44_;
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_toSeqRight_51_);
lean_inc(v_toSeqLeft_50_);
lean_inc(v_toSeq_49_);
lean_inc(v_toFunctor_48_);
lean_dec(v_toApplicative_44_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_64_; 
v___f_55_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1));
v___f_56_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_48_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_57_, 0, v_toFunctor_48_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_58_, 0, v_toFunctor_48_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___f_57_);
lean_ctor_set(v___x_59_, 1, v___f_58_);
v___f_60_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_60_, 0, v_toSeqRight_51_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_61_, 0, v_toSeqLeft_50_);
v___f_62_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_62_, 0, v_toSeq_49_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 4, v___f_60_);
lean_ctor_set(v___x_53_, 3, v___f_61_);
lean_ctor_set(v___x_53_, 2, v___f_62_);
lean_ctor_set(v___x_53_, 1, v___f_55_);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___f_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v___f_62_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v___f_61_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v___f_60_);
v___x_64_ = v_reuseFailAlloc_74_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___f_56_);
lean_ctor_set(v___x_46_, 0, v___x_64_);
v___x_66_ = v___x_46_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___f_56_);
v___x_66_ = v_reuseFailAlloc_73_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___f_70_; lean_object* v___x_3876__overap_71_; lean_object* v___x_72_; 
v___x_67_ = l_StateRefT_x27_instMonad___redArg(v___x_66_);
v___x_68_ = lean_box(0);
v___x_69_ = l_instInhabitedOfMonad___redArg(v___x_67_, v___x_68_);
v___f_70_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_70_, 0, v___x_69_);
v___x_3876__overap_71_ = lean_panic_fn_borrowed(v___f_70_, v_msg_36_);
lean_dec_ref(v___f_70_);
lean_inc(v___y_40_);
lean_inc_ref(v___y_39_);
lean_inc(v___y_38_);
lean_inc_ref(v___y_37_);
v___x_72_ = lean_apply_5(v___x_3876__overap_71_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, lean_box(0));
return v___x_72_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___boxed(lean_object* v_msg_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(v_msg_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_85_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2));
v___x_90_ = lean_unsigned_to_nat(11u);
v___x_91_ = lean_unsigned_to_nat(40u);
v___x_92_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1));
v___x_93_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0));
v___x_94_ = l_mkPanicMessageWithDecl(v___x_93_, v___x_92_, v___x_91_, v___x_90_, v___x_89_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(lean_object* v_upperBound_95_, lean_object* v_a_96_, lean_object* v_b_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_a_104_; uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_lt(v_a_96_, v_upperBound_95_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec(v_a_96_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v_b_97_);
return v___x_109_;
}
else
{
lean_object* v_fst_110_; 
v_fst_110_ = lean_ctor_get(v_b_97_, 0);
lean_inc(v_fst_110_);
if (lean_obj_tag(v_fst_110_) == 7)
{
lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_134_; 
v_snd_111_ = lean_ctor_get(v_b_97_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_b_97_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_b_97_, 0);
lean_dec(v_unused_135_);
v___x_113_ = v_b_97_;
v_isShared_114_ = v_isSharedCheck_134_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_dec(v_b_97_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_134_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_binderName_115_; lean_object* v_binderType_116_; lean_object* v_body_117_; uint8_t v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; 
v_binderName_115_ = lean_ctor_get(v_fst_110_, 0);
lean_inc(v_binderName_115_);
v_binderType_116_ = lean_ctor_get(v_fst_110_, 1);
lean_inc_ref(v_binderType_116_);
v_body_117_ = lean_ctor_get(v_fst_110_, 2);
lean_inc_ref(v_body_117_);
lean_dec_ref_known(v_fst_110_, 3);
v___x_118_ = 0;
v___x_119_ = 0;
v___x_120_ = l_Lean_Compiler_LCNF_mkParam(v___x_119_, v_binderName_115_, v_binderType_116_, v___x_118_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_122_ = lean_array_push(v_snd_111_, v_a_121_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_122_);
lean_ctor_set(v___x_113_, 0, v_body_117_);
v___x_124_ = v___x_113_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_body_117_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
v_a_104_ = v___x_124_;
goto v___jp_103_;
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
lean_dec_ref(v_body_117_);
lean_del_object(v___x_113_);
lean_dec(v_snd_111_);
lean_dec(v_a_96_);
v_a_126_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_120_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_120_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_snd_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_153_; 
v_snd_136_ = lean_ctor_get(v_b_97_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_b_97_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v_b_97_, 0);
lean_dec(v_unused_154_);
v___x_138_ = v_b_97_;
v_isShared_139_ = v_isSharedCheck_153_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_snd_136_);
lean_dec(v_b_97_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_153_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3);
v___x_141_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(v___x_140_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v___x_143_; 
lean_dec_ref_known(v___x_141_, 1);
if (v_isShared_139_ == 0)
{
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_fst_110_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_snd_136_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
v_a_104_ = v___x_143_;
goto v___jp_103_;
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_del_object(v___x_138_);
lean_dec(v_snd_136_);
lean_dec(v_fst_110_);
lean_dec(v_a_96_);
v_a_145_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_141_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_141_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_a_96_, v___x_105_);
lean_dec(v_a_96_);
v_a_96_ = v___x_106_;
v_b_97_ = v_a_104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___boxed(lean_object* v_upperBound_155_, lean_object* v_a_156_, lean_object* v_b_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(v_upperBound_155_, v_a_156_, v_b_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v_upperBound_155_);
return v_res_163_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_164_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2));
v___x_165_ = lean_unsigned_to_nat(11u);
v___x_166_ = lean_unsigned_to_nat(32u);
v___x_167_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1));
v___x_168_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0));
v___x_169_ = l_mkPanicMessageWithDecl(v___x_168_, v___x_167_, v___x_166_, v___x_165_, v___x_164_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(lean_object* v_upperBound_170_, lean_object* v_a_171_, lean_object* v_b_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_a_179_; uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_lt(v_a_171_, v_upperBound_170_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec(v_a_171_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_b_172_);
return v___x_184_;
}
else
{
if (lean_obj_tag(v_b_172_) == 7)
{
lean_object* v_body_185_; 
v_body_185_ = lean_ctor_get(v_b_172_, 2);
lean_inc_ref(v_body_185_);
lean_dec_ref_known(v_b_172_, 3);
v_a_179_ = v_body_185_;
goto v___jp_178_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0);
v___x_187_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(v___x_186_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_dec_ref_known(v___x_187_, 1);
v_a_179_ = v_b_172_;
goto v___jp_178_;
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v_b_172_);
lean_dec(v_a_171_);
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_a_171_, v___x_180_);
lean_dec(v_a_171_);
v_a_171_ = v___x_181_;
v_b_172_ = v_a_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___boxed(lean_object* v_upperBound_196_, lean_object* v_a_197_, lean_object* v_b_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(v_upperBound_196_, v_a_197_, v_b_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v_upperBound_196_);
return v_res_204_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1(void){
_start:
{
lean_object* v___x_211_; uint64_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0));
v___x_212_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2(void){
_start:
{
uint64_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_uint64_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1);
v___x_214_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0));
v___x_215_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set_uint64(v___x_215_, sizeof(void*)*1, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(32u);
v___x_220_ = lean_mk_empty_array_with_capacity(v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6(void){
_start:
{
size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_unsigned_to_nat(32u);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
v___x_226_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5);
v___x_227_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_223_);
lean_ctor_set(v___x_227_, 3, v___x_223_);
lean_ctor_set_usize(v___x_227_, 4, v___x_222_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_box(1);
v___x_229_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6);
v___x_230_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_228_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9(void){
_start:
{
uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_234_ = 1;
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_box(0);
v___x_237_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8));
v___x_238_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7);
v___x_239_ = lean_box(1);
v___x_240_ = 0;
v___x_241_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2);
v___x_242_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_239_);
lean_ctor_set(v___x_242_, 2, v___x_238_);
lean_ctor_set(v___x_242_, 3, v___x_237_);
lean_ctor_set(v___x_242_, 4, v___x_236_);
lean_ctor_set(v___x_242_, 5, v___x_235_);
lean_ctor_set(v___x_242_, 6, v___x_236_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7 + 1, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7 + 2, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7 + 3, v___x_234_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
lean_ctor_set(v___x_245_, 3, v___x_244_);
lean_ctor_set(v___x_245_, 4, v___x_243_);
lean_ctor_set(v___x_245_, 5, v___x_243_);
lean_ctor_set(v___x_245_, 6, v___x_243_);
lean_ctor_set(v___x_245_, 7, v___x_243_);
lean_ctor_set(v___x_245_, 8, v___x_243_);
lean_ctor_set(v___x_245_, 9, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4);
v___x_247_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
lean_ctor_set(v___x_247_, 4, v___x_246_);
lean_ctor_set(v___x_247_, 5, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__12(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4);
v___x_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_ctor_set(v___x_249_, 2, v___x_248_);
lean_ctor_set(v___x_249_, 3, v___x_248_);
lean_ctor_set(v___x_249_, 4, v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__13(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_250_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__12, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__12_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__12);
v___x_251_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6);
v___x_252_ = lean_box(1);
v___x_253_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11);
v___x_254_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10);
v___x_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
lean_ctor_set(v___x_255_, 3, v___x_251_);
lean_ctor_set(v___x_255_, 4, v___x_250_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(lean_object* v_ctorType_256_, lean_object* v_numParams_257_, lean_object* v_numFields_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_a_265_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9);
v___x_308_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__13, &l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__13_once, _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__13);
v___x_309_ = lean_st_mk_ref(v___x_308_);
v___x_310_ = l_Lean_Compiler_LCNF_toLCNFType(v_ctorType_256_, v___x_307_, v___x_309_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = lean_st_ref_get(v___x_309_);
lean_dec(v___x_309_);
lean_dec(v___x_312_);
v_a_265_ = v_a_311_;
goto v___jp_264_;
}
else
{
lean_dec(v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_313_; 
v_a_313_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_310_, 1);
v_a_265_ = v_a_313_;
goto v___jp_264_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_310_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_310_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
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
v___jp_264_:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Compiler_LCNF_toMonoType(v_a_265_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(v_numParams_257_, v___x_268_, v_a_267_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
v___x_271_ = lean_mk_empty_array_with_capacity(v_numFields_258_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_a_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(v_numFields_258_, v___x_268_, v___x_272_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_snd_278_; lean_object* v___x_280_; 
v_snd_278_ = lean_ctor_get(v_a_274_, 1);
lean_inc(v_snd_278_);
lean_dec(v_a_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_snd_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_snd_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_273_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_269_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_269_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_266_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_266_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___boxed(lean_object* v_ctorType_322_, lean_object* v_numParams_323_, lean_object* v_numFields_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(v_ctorType_322_, v_numParams_323_, v_numFields_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_numFields_324_);
lean_dec(v_numParams_323_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1(lean_object* v_upperBound_331_, lean_object* v_inst_332_, lean_object* v_R_333_, lean_object* v_a_334_, lean_object* v_b_335_, lean_object* v_c_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(v_upperBound_331_, v_a_334_, v_b_335_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___boxed(lean_object* v_upperBound_343_, lean_object* v_inst_344_, lean_object* v_R_345_, lean_object* v_a_346_, lean_object* v_b_347_, lean_object* v_c_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1(v_upperBound_343_, v_inst_344_, v_R_345_, v_a_346_, v_b_347_, v_c_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v_upperBound_343_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2(lean_object* v_upperBound_355_, lean_object* v_inst_356_, lean_object* v_R_357_, lean_object* v_a_358_, lean_object* v_b_359_, lean_object* v_c_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(v_upperBound_355_, v_a_358_, v_b_359_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___boxed(lean_object* v_upperBound_367_, lean_object* v_inst_368_, lean_object* v_R_369_, lean_object* v_a_370_, lean_object* v_b_371_, lean_object* v_c_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2(v_upperBound_367_, v_inst_368_, v_R_369_, v_a_370_, v_b_371_, v_c_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v_upperBound_367_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_unsigned_to_nat(16u);
v___x_381_ = lean_mk_array(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0, &l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1, &l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(lean_object* v_x_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2, &l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2);
v___x_394_ = lean_st_mk_ref(v___x_393_);
lean_inc(v_a_391_);
lean_inc_ref(v_a_390_);
lean_inc(v_a_389_);
lean_inc_ref(v_a_388_);
lean_inc(v___x_394_);
v___x_395_ = lean_apply_6(v_x_387_, v___x_394_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, lean_box(0));
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_st_ref_get(v___x_394_);
lean_dec(v___x_394_);
lean_dec(v___x_400_);
if (v_isShared_399_ == 0)
{
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_396_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_dec(v___x_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___boxed(lean_object* v_x_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(v_x_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run(lean_object* v_00_u03b1_412_, lean_object* v_x_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(v_x_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_M_run___boxed(lean_object* v_00_u03b1_420_, lean_object* v_x_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Compiler_LCNF_StructProjCases_M_run(v_00_u03b1_420_, v_x_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_value_432_; lean_object* v_tail_433_; uint8_t v___x_434_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_value_432_ = lean_ctor_get(v_x_429_, 1);
v_tail_433_ = lean_ctor_get(v_x_429_, 2);
v___x_434_ = l_Lean_instBEqFVarId_beq(v_key_431_, v_a_428_);
if (v___x_434_ == 0)
{
v_x_429_ = v_tail_433_;
goto _start;
}
else
{
lean_object* v___x_436_; 
lean_inc(v_value_432_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_value_432_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_437_, lean_object* v_x_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(v_a_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec(v_a_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_buckets_442_; lean_object* v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v_fold_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_buckets_442_ = lean_ctor_get(v_m_440_, 1);
v___x_443_ = lean_array_get_size(v_buckets_442_);
v___x_444_ = l_Lean_instHashableFVarId_hash(v_a_441_);
v___x_445_ = 32ULL;
v___x_446_ = lean_uint64_shift_right(v___x_444_, v___x_445_);
v_fold_447_ = lean_uint64_xor(v___x_444_, v___x_446_);
v___x_448_ = 16ULL;
v___x_449_ = lean_uint64_shift_right(v_fold_447_, v___x_448_);
v___x_450_ = lean_uint64_xor(v_fold_447_, v___x_449_);
v___x_451_ = lean_uint64_to_usize(v___x_450_);
v___x_452_ = lean_usize_of_nat(v___x_443_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_sub(v___x_452_, v___x_453_);
v___x_455_ = lean_usize_land(v___x_451_, v___x_454_);
v___x_456_ = lean_array_uget_borrowed(v_buckets_442_, v___x_455_);
v___x_457_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(v_a_441_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg___boxed(lean_object* v_m_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_m_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_m_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(lean_object* v_fvarId_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; lean_object* v_fvarMap_465_; lean_object* v___x_466_; 
v___x_464_ = lean_st_ref_get(v_a_462_);
v_fvarMap_465_ = lean_ctor_get(v___x_464_, 1);
lean_inc_ref(v_fvarMap_465_);
lean_dec(v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_fvarMap_465_, v_fvarId_461_);
lean_dec_ref(v_fvarMap_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_fvarId_461_);
return v___x_467_;
}
else
{
lean_object* v_val_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_fvarId_461_);
v_val_468_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_466_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_val_468_);
lean_dec(v___x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 0);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_val_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg___boxed(lean_object* v_fvarId_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_476_, v_a_477_);
lean_dec(v_a_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar(lean_object* v_fvarId_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_480_, v_a_481_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_remapFVar___boxed(lean_object* v_fvarId_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar(v_fvarId_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0(lean_object* v_00_u03b2_496_, lean_object* v_m_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_m_497_, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___boxed(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0(v_00_u03b2_500_, v_m_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_m_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0(lean_object* v_00_u03b2_504_, lean_object* v_a_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(v_a_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_508_, lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0(v_00_u03b2_508_, v_a_509_, v_x_510_);
lean_dec(v_x_510_);
lean_dec(v_a_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(lean_object* v_arg_512_, lean_object* v_a_513_){
_start:
{
if (lean_obj_tag(v_arg_512_) == 1)
{
lean_object* v_fvarId_515_; lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_fvarId_515_ = lean_ctor_get(v_arg_512_, 0);
lean_inc(v_fvarId_515_);
v___x_516_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_515_, v_a_513_);
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_512_, v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_arg_512_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg___boxed(lean_object* v_arg_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(v_arg_527_, v_a_528_);
lean_dec(v_a_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg(lean_object* v_arg_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(v_arg_531_, v_a_532_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitArg___boxed(lean_object* v_arg_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg(v_arg_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
return v_res_546_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2(void){
_start:
{
uint8_t v___x_549_; lean_object* v___x_550_; 
v___x_549_ = 0;
v___x_550_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(lean_object* v_msg_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_toApplicative_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_622_; 
v___x_558_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0);
v___x_559_ = l_StateRefT_x27_instMonad___redArg(v___x_558_);
v_toApplicative_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_559_, 1);
lean_dec(v_unused_623_);
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_622_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_toApplicative_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_622_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_toFunctor_564_; lean_object* v_toSeq_565_; lean_object* v_toSeqLeft_566_; lean_object* v_toSeqRight_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_620_; 
v_toFunctor_564_ = lean_ctor_get(v_toApplicative_560_, 0);
v_toSeq_565_ = lean_ctor_get(v_toApplicative_560_, 2);
v_toSeqLeft_566_ = lean_ctor_get(v_toApplicative_560_, 3);
v_toSeqRight_567_ = lean_ctor_get(v_toApplicative_560_, 4);
v_isSharedCheck_620_ = !lean_is_exclusive(v_toApplicative_560_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_toApplicative_560_, 1);
lean_dec(v_unused_621_);
v___x_569_ = v_toApplicative_560_;
v_isShared_570_ = v_isSharedCheck_620_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_toSeqRight_567_);
lean_inc(v_toSeqLeft_566_);
lean_inc(v_toSeq_565_);
lean_inc(v_toFunctor_564_);
lean_dec(v_toApplicative_560_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_620_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___x_580_; 
v___f_571_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1));
v___f_572_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_564_);
v___f_573_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_573_, 0, v_toFunctor_564_);
v___f_574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_574_, 0, v_toFunctor_564_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___f_573_);
lean_ctor_set(v___x_575_, 1, v___f_574_);
v___f_576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_576_, 0, v_toSeqRight_567_);
v___f_577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_577_, 0, v_toSeqLeft_566_);
v___f_578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_578_, 0, v_toSeq_565_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 4, v___f_576_);
lean_ctor_set(v___x_569_, 3, v___f_577_);
lean_ctor_set(v___x_569_, 2, v___f_578_);
lean_ctor_set(v___x_569_, 1, v___f_571_);
lean_ctor_set(v___x_569_, 0, v___x_575_);
v___x_580_ = v___x_569_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___f_571_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v___f_578_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v___f_577_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v___f_576_);
v___x_580_ = v_reuseFailAlloc_619_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___f_572_);
lean_ctor_set(v___x_562_, 0, v___x_580_);
v___x_582_ = v___x_562_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___f_572_);
v___x_582_ = v_reuseFailAlloc_618_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v_toApplicative_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_616_; 
v___x_583_ = l_StateRefT_x27_instMonad___redArg(v___x_582_);
v_toApplicative_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_583_, 1);
lean_dec(v_unused_617_);
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_616_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_toApplicative_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_616_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_toFunctor_588_; lean_object* v_toSeq_589_; lean_object* v_toSeqLeft_590_; lean_object* v_toSeqRight_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_toFunctor_588_ = lean_ctor_get(v_toApplicative_584_, 0);
v_toSeq_589_ = lean_ctor_get(v_toApplicative_584_, 2);
v_toSeqLeft_590_ = lean_ctor_get(v_toApplicative_584_, 3);
v_toSeqRight_591_ = lean_ctor_get(v_toApplicative_584_, 4);
v_isSharedCheck_614_ = !lean_is_exclusive(v_toApplicative_584_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_toApplicative_584_, 1);
lean_dec(v_unused_615_);
v___x_593_ = v_toApplicative_584_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_toSeqRight_591_);
lean_inc(v_toSeqLeft_590_);
lean_inc(v_toSeq_589_);
lean_inc(v_toFunctor_588_);
lean_dec(v_toApplicative_584_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_604_; 
v___f_595_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0));
v___f_596_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1));
lean_inc_ref(v_toFunctor_588_);
v___f_597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_597_, 0, v_toFunctor_588_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_598_, 0, v_toFunctor_588_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___f_597_);
lean_ctor_set(v___x_599_, 1, v___f_598_);
v___f_600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_600_, 0, v_toSeqRight_591_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeqLeft_590_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_602_, 0, v_toSeq_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v___f_600_);
lean_ctor_set(v___x_593_, 3, v___f_601_);
lean_ctor_set(v___x_593_, 2, v___f_602_);
lean_ctor_set(v___x_593_, 1, v___f_595_);
lean_ctor_set(v___x_593_, 0, v___x_599_);
v___x_604_ = v___x_593_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___f_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v___f_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___f_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___f_600_);
v___x_604_ = v_reuseFailAlloc_613_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___f_596_);
lean_ctor_set(v___x_586_, 0, v___x_604_);
v___x_606_ = v___x_586_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___f_596_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_1167__overap_610_; lean_object* v___x_611_; 
v___x_607_ = l_StateRefT_x27_instMonad___redArg(v___x_606_);
v___x_608_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2, &l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2_once, _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2);
v___x_609_ = l_instInhabitedOfMonad___redArg(v___x_607_, v___x_608_);
v___x_1167__overap_610_ = lean_panic_fn_borrowed(v___x_609_, v_msg_551_);
lean_dec(v___x_609_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
v___x_611_ = lean_apply_6(v___x_1167__overap_610_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, lean_box(0));
return v___x_611_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___boxed(lean_object* v_msg_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(v_msg_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(size_t v_sz_632_, size_t v_i_633_, lean_object* v_bs_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_lt(v_i_633_, v_sz_632_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_bs_634_);
return v___x_638_;
}
else
{
lean_object* v_v_639_; lean_object* v___x_640_; 
v_v_639_ = lean_array_uget_borrowed(v_bs_634_, v_i_633_);
lean_inc(v_v_639_);
v___x_640_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(v_v_639_, v___y_635_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v_bs_x27_643_; size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = lean_unsigned_to_nat(0u);
v_bs_x27_643_ = lean_array_uset(v_bs_634_, v_i_633_, v___x_642_);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_633_, v___x_644_);
v___x_646_ = lean_array_uset(v_bs_x27_643_, v_i_633_, v_a_641_);
v_i_633_ = v___x_645_;
v_bs_634_ = v___x_646_;
goto _start;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_bs_634_);
v_a_648_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_640_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_640_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg___boxed(lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_bs_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
size_t v_sz_boxed_661_; size_t v_i_boxed_662_; lean_object* v_res_663_; 
v_sz_boxed_661_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_662_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_boxed_661_, v_i_boxed_662_, v_bs_658_, v___y_659_);
lean_dec(v___y_659_);
return v_res_663_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_665_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2));
v___x_666_ = lean_unsigned_to_nat(16u);
v___x_667_ = lean_unsigned_to_nat(118u);
v___x_668_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0));
v___x_669_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0));
v___x_670_ = l_mkPanicMessageWithDecl(v___x_669_, v___x_668_, v___x_667_, v___x_666_, v___x_665_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(lean_object* v_v_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
switch(lean_obj_tag(v_v_671_))
{
case 2:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref_known(v_v_671_, 3);
v___x_678_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1, &l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1_once, _init_l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1);
v___x_679_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(v___x_678_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_679_;
}
case 3:
{
lean_object* v_args_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v___x_683_; 
v_args_680_ = lean_ctor_get(v_v_671_, 2);
v_sz_681_ = lean_array_size(v_args_680_);
v___x_682_ = ((size_t)0ULL);
lean_inc_ref(v_args_680_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_681_, v___x_682_, v_args_680_, v_a_672_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_693_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = 0;
v___x_689_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_688_, v_v_671_, v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref_known(v_v_671_, 3);
v_a_694_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_683_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_683_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_702_; lean_object* v_args_703_; lean_object* v___x_704_; lean_object* v_a_705_; size_t v_sz_706_; size_t v___x_707_; lean_object* v___x_708_; 
v_fvarId_702_ = lean_ctor_get(v_v_671_, 0);
v_args_703_ = lean_ctor_get(v_v_671_, 1);
lean_inc(v_fvarId_702_);
v___x_704_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_702_, v_a_672_);
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
v_sz_706_ = lean_array_size(v_args_703_);
v___x_707_ = ((size_t)0ULL);
lean_inc_ref(v_args_703_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_706_, v___x_707_, v_args_703_, v_a_672_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = 0;
v___x_714_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v___x_713_, v_v_671_, v_a_705_, v_a_709_);
lean_dec_ref_known(v_v_671_, 2);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_705_);
lean_dec_ref_known(v_v_671_, 2);
v_a_719_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_708_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
default: 
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_v_671_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___boxed(lean_object* v_v_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(v_v_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1(size_t v_sz_736_, size_t v_i_737_, lean_object* v_bs_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_736_, v_i_737_, v_bs_738_, v___y_739_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___boxed(lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_bs_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v_sz_boxed_755_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_756_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1(v_sz_boxed_755_, v_i_boxed_756_, v_bs_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(lean_object* v_a_758_, lean_object* v_b_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_dec(v_b_759_);
lean_dec(v_a_758_);
return v_x_760_;
}
else
{
lean_object* v_key_761_; lean_object* v_value_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_775_; 
v_key_761_ = lean_ctor_get(v_x_760_, 0);
v_value_762_ = lean_ctor_get(v_x_760_, 1);
v_tail_763_ = lean_ctor_get(v_x_760_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_775_ == 0)
{
v___x_765_ = v_x_760_;
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_value_762_);
lean_inc(v_key_761_);
lean_dec(v_x_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_instBEqFVarId_beq(v_key_761_, v_a_758_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(v_a_758_, v_b_759_, v_tail_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 2, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_key_761_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_value_762_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_value_762_);
lean_dec(v_key_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_b_759_);
lean_ctor_set(v___x_765_, 0, v_a_758_);
v___x_773_ = v___x_765_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_b_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_tail_763_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
return v_x_776_;
}
else
{
lean_object* v_key_778_; lean_object* v_value_779_; lean_object* v_tail_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_803_; 
v_key_778_ = lean_ctor_get(v_x_777_, 0);
v_value_779_ = lean_ctor_get(v_x_777_, 1);
v_tail_780_ = lean_ctor_get(v_x_777_, 2);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_803_ == 0)
{
v___x_782_ = v_x_777_;
v_isShared_783_ = v_isSharedCheck_803_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_tail_780_);
lean_inc(v_value_779_);
lean_inc(v_key_778_);
lean_dec(v_x_777_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_803_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v_fold_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_784_ = lean_array_get_size(v_x_776_);
v___x_785_ = l_Lean_instHashableFVarId_hash(v_key_778_);
v___x_786_ = 32ULL;
v___x_787_ = lean_uint64_shift_right(v___x_785_, v___x_786_);
v_fold_788_ = lean_uint64_xor(v___x_785_, v___x_787_);
v___x_789_ = 16ULL;
v___x_790_ = lean_uint64_shift_right(v_fold_788_, v___x_789_);
v___x_791_ = lean_uint64_xor(v_fold_788_, v___x_790_);
v___x_792_ = lean_uint64_to_usize(v___x_791_);
v___x_793_ = lean_usize_of_nat(v___x_784_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_sub(v___x_793_, v___x_794_);
v___x_796_ = lean_usize_land(v___x_792_, v___x_795_);
v___x_797_ = lean_array_uget_borrowed(v_x_776_, v___x_796_);
lean_inc(v___x_797_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 2, v___x_797_);
v___x_799_ = v___x_782_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_key_778_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_value_779_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v___x_797_);
v___x_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_array_uset(v_x_776_, v___x_796_, v___x_799_);
v_x_776_ = v___x_800_;
v_x_777_ = v_tail_780_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(lean_object* v_i_804_, lean_object* v_source_805_, lean_object* v_target_806_){
_start:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_array_get_size(v_source_805_);
v___x_808_ = lean_nat_dec_lt(v_i_804_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v_source_805_);
lean_dec(v_i_804_);
return v_target_806_;
}
else
{
lean_object* v_es_809_; lean_object* v___x_810_; lean_object* v_source_811_; lean_object* v_target_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_es_809_ = lean_array_fget(v_source_805_, v_i_804_);
v___x_810_ = lean_box(0);
v_source_811_ = lean_array_fset(v_source_805_, v_i_804_, v___x_810_);
v_target_812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(v_target_806_, v_es_809_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_i_804_, v___x_813_);
lean_dec(v_i_804_);
v_i_804_ = v___x_814_;
v_source_805_ = v_source_811_;
v_target_806_ = v_target_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(lean_object* v_data_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_nbuckets_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_817_ = lean_array_get_size(v_data_816_);
v___x_818_ = lean_unsigned_to_nat(2u);
v_nbuckets_819_ = lean_nat_mul(v___x_817_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_box(0);
v___x_822_ = lean_mk_array(v_nbuckets_819_, v___x_821_);
v___x_823_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(v___x_820_, v_data_816_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(lean_object* v_a_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
else
{
lean_object* v_key_827_; lean_object* v_tail_828_; uint8_t v___x_829_; 
v_key_827_ = lean_ctor_get(v_x_825_, 0);
v_tail_828_ = lean_ctor_get(v_x_825_, 2);
v___x_829_ = l_Lean_instBEqFVarId_beq(v_key_827_, v_a_824_);
if (v___x_829_ == 0)
{
v_x_825_ = v_tail_828_;
goto _start;
}
else
{
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg___boxed(lean_object* v_a_831_, lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_831_, v_x_832_);
lean_dec(v_x_832_);
lean_dec(v_a_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(lean_object* v_m_835_, lean_object* v_a_836_, lean_object* v_b_837_){
_start:
{
lean_object* v_size_838_; lean_object* v_buckets_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_882_; 
v_size_838_ = lean_ctor_get(v_m_835_, 0);
v_buckets_839_ = lean_ctor_get(v_m_835_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_m_835_);
if (v_isSharedCheck_882_ == 0)
{
v___x_841_ = v_m_835_;
v_isShared_842_ = v_isSharedCheck_882_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_buckets_839_);
lean_inc(v_size_838_);
lean_dec(v_m_835_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_882_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v_fold_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v_bkt_856_; uint8_t v___x_857_; 
v___x_843_ = lean_array_get_size(v_buckets_839_);
v___x_844_ = l_Lean_instHashableFVarId_hash(v_a_836_);
v___x_845_ = 32ULL;
v___x_846_ = lean_uint64_shift_right(v___x_844_, v___x_845_);
v_fold_847_ = lean_uint64_xor(v___x_844_, v___x_846_);
v___x_848_ = 16ULL;
v___x_849_ = lean_uint64_shift_right(v_fold_847_, v___x_848_);
v___x_850_ = lean_uint64_xor(v_fold_847_, v___x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = lean_usize_of_nat(v___x_843_);
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_sub(v___x_852_, v___x_853_);
v___x_855_ = lean_usize_land(v___x_851_, v___x_854_);
v_bkt_856_ = lean_array_uget_borrowed(v_buckets_839_, v___x_855_);
v___x_857_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_836_, v_bkt_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v_size_x27_859_; lean_object* v___x_860_; lean_object* v_buckets_x27_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v_size_x27_859_ = lean_nat_add(v_size_838_, v___x_858_);
lean_dec(v_size_838_);
lean_inc(v_bkt_856_);
v___x_860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_860_, 0, v_a_836_);
lean_ctor_set(v___x_860_, 1, v_b_837_);
lean_ctor_set(v___x_860_, 2, v_bkt_856_);
v_buckets_x27_861_ = lean_array_uset(v_buckets_839_, v___x_855_, v___x_860_);
v___x_862_ = lean_unsigned_to_nat(4u);
v___x_863_ = lean_nat_mul(v_size_x27_859_, v___x_862_);
v___x_864_ = lean_unsigned_to_nat(3u);
v___x_865_ = lean_nat_div(v___x_863_, v___x_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_array_get_size(v_buckets_x27_861_);
v___x_867_ = lean_nat_dec_le(v___x_865_, v___x_866_);
lean_dec(v___x_865_);
if (v___x_867_ == 0)
{
lean_object* v_val_868_; lean_object* v___x_870_; 
v_val_868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(v_buckets_x27_861_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_val_868_);
lean_ctor_set(v___x_841_, 0, v_size_x27_859_);
v___x_870_ = v___x_841_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_size_x27_859_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_val_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
lean_object* v___x_873_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_buckets_x27_861_);
lean_ctor_set(v___x_841_, 0, v_size_x27_859_);
v___x_873_ = v___x_841_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_size_x27_859_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_buckets_x27_861_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v___x_875_; lean_object* v_buckets_x27_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
lean_inc(v_bkt_856_);
v___x_875_ = lean_box(0);
v_buckets_x27_876_ = lean_array_uset(v_buckets_839_, v___x_855_, v___x_875_);
v___x_877_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(v_a_836_, v_b_837_, v_bkt_856_);
v___x_878_ = lean_array_uset(v_buckets_x27_876_, v___x_855_, v___x_877_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_878_);
v___x_880_ = v___x_841_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_size_838_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(lean_object* v_as_883_, size_t v_sz_884_, size_t v_i_885_, lean_object* v_b_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = lean_usize_dec_lt(v_i_885_, v_sz_884_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_b_886_);
return v___x_891_;
}
else
{
lean_object* v_array_892_; lean_object* v_start_893_; lean_object* v_stop_894_; uint8_t v___x_895_; 
v_array_892_ = lean_ctor_get(v_b_886_, 0);
v_start_893_ = lean_ctor_get(v_b_886_, 1);
v_stop_894_ = lean_ctor_get(v_b_886_, 2);
v___x_895_ = lean_nat_dec_lt(v_start_893_, v_stop_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_b_886_);
return v___x_896_;
}
else
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_933_; 
lean_inc(v_stop_894_);
lean_inc(v_start_893_);
lean_inc_ref(v_array_892_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_b_886_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; lean_object* v_unused_936_; 
v_unused_934_ = lean_ctor_get(v_b_886_, 2);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_b_886_, 1);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_b_886_, 0);
lean_dec(v_unused_936_);
v___x_898_ = v_b_886_;
v_isShared_899_ = v_isSharedCheck_933_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_b_886_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_933_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v_projMap_901_; lean_object* v_fvarMap_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_932_; 
v___x_900_ = lean_st_ref_take(v___y_887_);
v_projMap_901_ = lean_ctor_get(v___x_900_, 0);
v_fvarMap_902_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_932_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_932_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_fvarMap_902_);
lean_inc(v_projMap_901_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_932_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_a_906_; lean_object* v_fvarId_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_a_906_ = lean_array_uget_borrowed(v_as_883_, v_i_885_);
v_fvarId_907_ = lean_ctor_get(v_a_906_, 0);
v___x_908_ = lean_array_fget_borrowed(v_array_892_, v_start_893_);
lean_inc(v___x_908_);
lean_inc(v_fvarId_907_);
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_fvarMap_902_, v_fvarId_907_, v___x_908_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_909_);
v___x_911_ = v___x_904_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_projMap_901_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_931_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_st_ref_set(v___y_887_, v___x_911_);
v___x_913_ = 0;
v___x_914_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_913_, v_a_906_, v___y_888_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec_ref_known(v___x_914_, 1);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_start_893_, v___x_915_);
lean_dec(v_start_893_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_916_);
v___x_918_ = v___x_898_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_array_892_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_stop_894_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
size_t v___x_919_; size_t v___x_920_; 
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_885_, v___x_919_);
v_i_885_ = v___x_920_;
v_b_886_ = v___x_918_;
goto _start;
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_898_);
lean_dec(v_stop_894_);
lean_dec(v_start_893_);
lean_dec_ref(v_array_892_);
v_a_923_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_914_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_914_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg___boxed(lean_object* v_as_937_, lean_object* v_sz_938_, lean_object* v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_938_);
lean_dec(v_sz_938_);
v_i_boxed_945_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(v_as_937_, v_sz_boxed_944_, v_i_boxed_945_, v_b_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v_as_937_);
return v_res_946_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0(void){
_start:
{
uint8_t v___x_947_; lean_object* v___x_948_; 
v___x_947_ = 0;
v___x_948_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_toApplicative_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1020_; 
v___x_956_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0);
v___x_957_ = l_StateRefT_x27_instMonad___redArg(v___x_956_);
v_toApplicative_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_957_, 1);
lean_dec(v_unused_1021_);
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_1020_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_toApplicative_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1020_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_toFunctor_962_; lean_object* v_toSeq_963_; lean_object* v_toSeqLeft_964_; lean_object* v_toSeqRight_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1018_; 
v_toFunctor_962_ = lean_ctor_get(v_toApplicative_958_, 0);
v_toSeq_963_ = lean_ctor_get(v_toApplicative_958_, 2);
v_toSeqLeft_964_ = lean_ctor_get(v_toApplicative_958_, 3);
v_toSeqRight_965_ = lean_ctor_get(v_toApplicative_958_, 4);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_toApplicative_958_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_toApplicative_958_, 1);
lean_dec(v_unused_1019_);
v___x_967_ = v_toApplicative_958_;
v_isShared_968_ = v_isSharedCheck_1018_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_toSeqRight_965_);
lean_inc(v_toSeqLeft_964_);
lean_inc(v_toSeq_963_);
lean_inc(v_toFunctor_962_);
lean_dec(v_toApplicative_958_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1018_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___f_969_; lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_978_; 
v___f_969_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1));
v___f_970_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_962_);
v___f_971_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_971_, 0, v_toFunctor_962_);
v___f_972_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_972_, 0, v_toFunctor_962_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___f_971_);
lean_ctor_set(v___x_973_, 1, v___f_972_);
v___f_974_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_974_, 0, v_toSeqRight_965_);
v___f_975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_975_, 0, v_toSeqLeft_964_);
v___f_976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_976_, 0, v_toSeq_963_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v___f_974_);
lean_ctor_set(v___x_967_, 3, v___f_975_);
lean_ctor_set(v___x_967_, 2, v___f_976_);
lean_ctor_set(v___x_967_, 1, v___f_969_);
lean_ctor_set(v___x_967_, 0, v___x_973_);
v___x_978_ = v___x_967_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___f_969_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___f_976_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v___f_975_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v___f_974_);
v___x_978_ = v_reuseFailAlloc_1017_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___f_970_);
lean_ctor_set(v___x_960_, 0, v___x_978_);
v___x_980_ = v___x_960_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___f_970_);
v___x_980_ = v_reuseFailAlloc_1016_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v_toApplicative_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1014_; 
v___x_981_ = l_StateRefT_x27_instMonad___redArg(v___x_980_);
v_toApplicative_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_981_, 1);
lean_dec(v_unused_1015_);
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1014_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_toApplicative_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1014_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_toFunctor_986_; lean_object* v_toSeq_987_; lean_object* v_toSeqLeft_988_; lean_object* v_toSeqRight_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1012_; 
v_toFunctor_986_ = lean_ctor_get(v_toApplicative_982_, 0);
v_toSeq_987_ = lean_ctor_get(v_toApplicative_982_, 2);
v_toSeqLeft_988_ = lean_ctor_get(v_toApplicative_982_, 3);
v_toSeqRight_989_ = lean_ctor_get(v_toApplicative_982_, 4);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_toApplicative_982_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_toApplicative_982_, 1);
lean_dec(v_unused_1013_);
v___x_991_ = v_toApplicative_982_;
v_isShared_992_ = v_isSharedCheck_1012_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_toSeqRight_989_);
lean_inc(v_toSeqLeft_988_);
lean_inc(v_toSeq_987_);
lean_inc(v_toFunctor_986_);
lean_dec(v_toApplicative_982_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1012_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1002_; 
v___f_993_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0));
v___f_994_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1));
lean_inc_ref(v_toFunctor_986_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_995_, 0, v_toFunctor_986_);
v___f_996_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_996_, 0, v_toFunctor_986_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___f_995_);
lean_ctor_set(v___x_997_, 1, v___f_996_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_998_, 0, v_toSeqRight_989_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_999_, 0, v_toSeqLeft_988_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toSeq_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 4, v___f_998_);
lean_ctor_set(v___x_991_, 3, v___f_999_);
lean_ctor_set(v___x_991_, 2, v___f_1000_);
lean_ctor_set(v___x_991_, 1, v___f_993_);
lean_ctor_set(v___x_991_, 0, v___x_997_);
v___x_1002_ = v___x_991_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___f_993_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v___f_1000_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v___f_999_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v___f_998_);
v___x_1002_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___f_994_);
lean_ctor_set(v___x_984_, 0, v___x_1002_);
v___x_1004_ = v___x_984_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___f_994_);
v___x_1004_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_14859__overap_1008_; lean_object* v___x_1009_; 
v___x_1005_ = l_StateRefT_x27_instMonad___redArg(v___x_1004_);
v___x_1006_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0);
v___x_1007_ = l_instInhabitedOfMonad___redArg(v___x_1005_, v___x_1006_);
v___x_14859__overap_1008_ = lean_panic_fn_borrowed(v___x_1007_, v_msg_949_);
lean_dec(v___x_1007_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
v___x_1009_ = lean_apply_6(v___x_14859__overap_1008_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, lean_box(0));
return v___x_1009_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___boxed(lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__0(lean_object* v_msg_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0);
v___x_1032_ = lean_panic_fn_borrowed(v___x_1031_, v_msg_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(size_t v_sz_1033_, size_t v_i_1034_, lean_object* v_bs_1035_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_usize_dec_lt(v_i_1034_, v_sz_1033_);
if (v___x_1036_ == 0)
{
return v_bs_1035_;
}
else
{
lean_object* v_v_1037_; lean_object* v_fvarId_1038_; lean_object* v___x_1039_; lean_object* v_bs_x27_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v_v_1037_ = lean_array_uget_borrowed(v_bs_1035_, v_i_1034_);
v_fvarId_1038_ = lean_ctor_get(v_v_1037_, 0);
lean_inc(v_fvarId_1038_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v_bs_x27_1040_ = lean_array_uset(v_bs_1035_, v_i_1034_, v___x_1039_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1034_, v___x_1041_);
v___x_1043_ = lean_array_uset(v_bs_x27_1040_, v_i_1034_, v_fvarId_1038_);
v_i_1034_ = v___x_1042_;
v_bs_1035_ = v___x_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2___boxed(lean_object* v_sz_1045_, lean_object* v_i_1046_, lean_object* v_bs_1047_){
_start:
{
size_t v_sz_boxed_1048_; size_t v_i_boxed_1049_; lean_object* v_res_1050_; 
v_sz_boxed_1048_ = lean_unbox_usize(v_sz_1045_);
lean_dec(v_sz_1045_);
v_i_boxed_1049_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(v_sz_boxed_1048_, v_i_boxed_1049_, v_bs_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(lean_object* v_a_1051_, lean_object* v_x_1052_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
return v_x_1052_;
}
else
{
lean_object* v_key_1053_; lean_object* v_value_1054_; lean_object* v_tail_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_key_1053_ = lean_ctor_get(v_x_1052_, 0);
v_value_1054_ = lean_ctor_get(v_x_1052_, 1);
v_tail_1055_ = lean_ctor_get(v_x_1052_, 2);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v_x_1052_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_tail_1055_);
lean_inc(v_value_1054_);
lean_inc(v_key_1053_);
lean_dec(v_x_1052_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
uint8_t v___x_1059_; 
v___x_1059_ = l_Lean_instBEqFVarId_beq(v_key_1053_, v_a_1051_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_1051_, v_tail_1055_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 2, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_key_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_value_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_del_object(v___x_1057_);
lean_dec(v_value_1054_);
lean_dec(v_key_1053_);
return v_tail_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg___boxed(lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_1065_, v_x_1066_);
lean_dec(v_a_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(lean_object* v_m_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_size_1070_; lean_object* v_buckets_1071_; lean_object* v___x_1072_; uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v_fold_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v_bkt_1085_; uint8_t v___x_1086_; 
v_size_1070_ = lean_ctor_get(v_m_1068_, 0);
v_buckets_1071_ = lean_ctor_get(v_m_1068_, 1);
v___x_1072_ = lean_array_get_size(v_buckets_1071_);
v___x_1073_ = l_Lean_instHashableFVarId_hash(v_a_1069_);
v___x_1074_ = 32ULL;
v___x_1075_ = lean_uint64_shift_right(v___x_1073_, v___x_1074_);
v_fold_1076_ = lean_uint64_xor(v___x_1073_, v___x_1075_);
v___x_1077_ = 16ULL;
v___x_1078_ = lean_uint64_shift_right(v_fold_1076_, v___x_1077_);
v___x_1079_ = lean_uint64_xor(v_fold_1076_, v___x_1078_);
v___x_1080_ = lean_uint64_to_usize(v___x_1079_);
v___x_1081_ = lean_usize_of_nat(v___x_1072_);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_sub(v___x_1081_, v___x_1082_);
v___x_1084_ = lean_usize_land(v___x_1080_, v___x_1083_);
v_bkt_1085_ = lean_array_uget_borrowed(v_buckets_1071_, v___x_1084_);
v___x_1086_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_1069_, v_bkt_1085_);
if (v___x_1086_ == 0)
{
return v_m_1068_;
}
else
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
lean_inc(v_bkt_1085_);
lean_inc_ref(v_buckets_1071_);
lean_inc(v_size_1070_);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_m_1068_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1100_ = lean_ctor_get(v_m_1068_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_m_1068_, 0);
lean_dec(v_unused_1101_);
v___x_1088_ = v_m_1068_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v_m_1068_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v_buckets_x27_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1090_ = lean_box(0);
v_buckets_x27_1091_ = lean_array_uset(v_buckets_1071_, v___x_1084_, v___x_1090_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_sub(v_size_1070_, v___x_1092_);
lean_dec(v_size_1070_);
v___x_1094_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_1069_, v_bkt_1085_);
v___x_1095_ = lean_array_uset(v_buckets_x27_1091_, v___x_1084_, v___x_1094_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1095_);
lean_ctor_set(v___x_1088_, 0, v___x_1093_);
v___x_1097_ = v___x_1088_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg___boxed(lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_m_1102_, v_a_1103_);
lean_dec(v_a_1103_);
return v_res_1104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1107_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2));
v___x_1108_ = lean_unsigned_to_nat(9u);
v___x_1109_ = lean_unsigned_to_nat(641u);
v___x_1110_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1));
v___x_1111_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0));
v___x_1112_ = l_mkPanicMessageWithDecl(v___x_1111_, v___x_1110_, v___x_1109_, v___x_1108_, v___x_1107_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1115_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4));
v___x_1116_ = lean_unsigned_to_nat(59u);
v___x_1117_ = lean_unsigned_to_nat(68u);
v___x_1118_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3));
v___x_1119_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0));
v___x_1120_ = l_mkPanicMessageWithDecl(v___x_1119_, v___x_1118_, v___x_1117_, v___x_1116_, v___x_1115_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(lean_object* v_i_1121_, lean_object* v_as_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_array_get_size(v_as_1122_);
v___x_1130_ = lean_nat_dec_lt(v_i_1121_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec(v_i_1121_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_as_1122_);
return v___x_1131_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1133_; 
v_a_1132_ = lean_array_fget_borrowed(v_as_1122_, v_i_1121_);
lean_inc(v_a_1132_);
v___x_1133_ = l_Lean_Compiler_LCNF_StructProjCases_visitAlt(v_a_1132_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; size_t v___x_1135_; size_t v___x_1136_; uint8_t v___x_1137_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = lean_ptr_addr(v_a_1132_);
v___x_1136_ = lean_ptr_addr(v_a_1134_);
v___x_1137_ = lean_usize_dec_eq(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_add(v_i_1121_, v___x_1138_);
v___x_1140_ = lean_array_fset(v_as_1122_, v_i_1121_, v_a_1134_);
lean_dec(v_i_1121_);
v_i_1121_ = v___x_1139_;
v_as_1122_ = v___x_1140_;
goto _start;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_a_1134_);
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_add(v_i_1121_, v___x_1142_);
lean_dec(v_i_1121_);
v_i_1121_ = v___x_1143_;
goto _start;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_as_1122_);
lean_dec(v_i_1121_);
v_a_1145_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1133_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1133_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6));
v___x_1155_ = lean_unsigned_to_nat(8u);
v___x_1156_ = lean_unsigned_to_nat(91u);
v___x_1157_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3));
v___x_1158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0));
v___x_1159_ = l_mkPanicMessageWithDecl(v___x_1158_, v___x_1157_, v___x_1156_, v___x_1155_, v___x_1154_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode(lean_object* v_code_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___y_1168_; lean_object* v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v___y_1177_; lean_object* v_decl_1182_; lean_object* v_k_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; 
switch(lean_obj_tag(v_code_1160_))
{
case 0:
{
lean_object* v_decl_1234_; lean_object* v_value_1235_; 
v_decl_1234_ = lean_ctor_get(v_code_1160_, 0);
lean_inc_ref(v_decl_1234_);
v_value_1235_ = lean_ctor_get(v_decl_1234_, 3);
if (lean_obj_tag(v_value_1235_) == 2)
{
lean_object* v_k_1236_; lean_object* v_fvarId_1237_; lean_object* v_typeName_1238_; lean_object* v_idx_1239_; lean_object* v_struct_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1390_; 
v_k_1236_ = lean_ctor_get(v_code_1160_, 1);
lean_inc_ref(v_k_1236_);
lean_dec_ref_known(v_code_1160_, 2);
v_fvarId_1237_ = lean_ctor_get(v_decl_1234_, 0);
lean_inc(v_fvarId_1237_);
v_typeName_1238_ = lean_ctor_get(v_value_1235_, 0);
lean_inc(v_typeName_1238_);
v_idx_1239_ = lean_ctor_get(v_value_1235_, 1);
lean_inc(v_idx_1239_);
v_struct_1240_ = lean_ctor_get(v_value_1235_, 2);
lean_inc(v_struct_1240_);
v___x_1241_ = 0;
v___x_1242_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1241_, v_decl_1234_, v_a_1163_);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_decl_1234_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1391_ = lean_ctor_get(v_decl_1234_, 3);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_decl_1234_, 2);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_decl_1234_, 1);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_decl_1234_, 0);
lean_dec(v_unused_1394_);
v___x_1244_ = v_decl_1234_;
v_isShared_1245_ = v_isSharedCheck_1390_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v_decl_1234_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1390_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref_known(v___x_1242_, 1);
v___x_1246_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_struct_1240_, v_a_1161_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v_projMap_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = lean_st_ref_get(v_a_1161_);
v_projMap_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_projMap_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_projMap_1249_, v_a_1247_);
lean_dec_ref(v_projMap_1249_);
if (lean_obj_tag(v___x_1251_) == 1)
{
lean_object* v_val_1252_; lean_object* v___x_1253_; lean_object* v_projMap_1254_; lean_object* v_fvarMap_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_typeName_1238_);
v_val_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_st_ref_take(v_a_1161_);
v_projMap_1254_ = lean_ctor_get(v___x_1253_, 0);
v_fvarMap_1255_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1257_ = v___x_1253_;
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_fvarMap_1255_);
lean_inc(v_projMap_1254_);
lean_dec(v___x_1253_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1259_ = lean_array_get(v___x_1250_, v_val_1252_, v_idx_1239_);
lean_dec(v_idx_1239_);
lean_dec(v_val_1252_);
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_fvarMap_1255_, v_fvarId_1237_, v___x_1259_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_projMap_1254_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_st_ref_set(v_a_1161_, v___x_1262_);
v_code_1160_ = v_k_1236_;
goto _start;
}
}
}
else
{
lean_object* v___x_1267_; 
lean_dec(v___x_1251_);
lean_inc(v_typeName_1238_);
v___x_1267_ = l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(v_typeName_1238_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
if (lean_obj_tag(v_a_1268_) == 1)
{
lean_object* v_val_1269_; lean_object* v_toConstantVal_1270_; lean_object* v_numParams_1271_; lean_object* v_numFields_1272_; lean_object* v_name_1273_; lean_object* v_type_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1362_; 
v_val_1269_ = lean_ctor_get(v_a_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v_a_1268_, 1);
v_toConstantVal_1270_ = lean_ctor_get(v_val_1269_, 0);
lean_inc_ref(v_toConstantVal_1270_);
v_numParams_1271_ = lean_ctor_get(v_val_1269_, 3);
lean_inc(v_numParams_1271_);
v_numFields_1272_ = lean_ctor_get(v_val_1269_, 4);
lean_inc(v_numFields_1272_);
lean_dec(v_val_1269_);
v_name_1273_ = lean_ctor_get(v_toConstantVal_1270_, 0);
v_type_1274_ = lean_ctor_get(v_toConstantVal_1270_, 2);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_toConstantVal_1270_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v_toConstantVal_1270_, 1);
lean_dec(v_unused_1363_);
v___x_1276_ = v_toConstantVal_1270_;
v_isShared_1277_ = v_isSharedCheck_1362_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_type_1274_);
lean_inc(v_name_1273_);
lean_dec(v_toConstantVal_1270_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1362_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(v_type_1274_, v_numParams_1271_, v_numFields_1272_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_numFields_1272_);
lean_dec(v_numParams_1271_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v_projMap_1281_; lean_object* v_fvarMap_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1353_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_st_ref_take(v_a_1161_);
v_projMap_1281_ = lean_ctor_get(v___x_1280_, 0);
v_fvarMap_1282_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1284_ = v___x_1280_;
v_isShared_1285_ = v_isSharedCheck_1353_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_fvarMap_1282_);
lean_inc(v_projMap_1281_);
lean_dec(v___x_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1353_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_sz_1286_ = lean_array_size(v_a_1279_);
v___x_1287_ = ((size_t)0ULL);
lean_inc(v_a_1279_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(v_sz_1286_, v___x_1287_, v_a_1279_);
lean_inc_ref(v___x_1288_);
lean_inc(v_a_1247_);
v___x_1289_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_projMap_1281_, v_a_1247_, v___x_1288_);
v___x_1290_ = lean_array_get(v___x_1250_, v___x_1288_, v_idx_1239_);
lean_dec(v_idx_1239_);
lean_dec_ref(v___x_1288_);
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_fvarMap_1282_, v_fvarId_1237_, v___x_1290_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1291_);
lean_ctor_set(v___x_1284_, 0, v___x_1289_);
v___x_1293_ = v___x_1284_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_st_ref_set(v_a_1161_, v___x_1293_);
v___x_1295_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v_k_1236_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1351_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1351_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1351_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v_projMap_1301_; lean_object* v_fvarMap_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1350_; 
v___x_1300_ = lean_st_ref_take(v_a_1161_);
v_projMap_1301_ = lean_ctor_get(v___x_1300_, 0);
v_fvarMap_1302_ = lean_ctor_get(v___x_1300_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1304_ = v___x_1300_;
v_isShared_1305_ = v_isSharedCheck_1350_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_fvarMap_1302_);
lean_inc(v_projMap_1301_);
lean_dec(v___x_1300_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1350_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_projMap_1301_, v_a_1247_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_fvarMap_1302_);
v___x_1308_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_st_ref_set(v_a_1161_, v___x_1308_);
lean_inc(v_a_1296_);
v___x_1310_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1241_, v_a_1296_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Compiler_LCNF_toMonoType(v_a_1311_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1332_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1332_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1332_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 2, v_a_1296_);
lean_ctor_set(v___x_1276_, 1, v_a_1279_);
v___x_1318_ = v___x_1276_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_name_1273_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_a_1296_);
v___x_1318_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_mk_empty_array_with_capacity(v___x_1319_);
v___x_1321_ = lean_array_push(v___x_1320_, v___x_1318_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 3, v___x_1321_);
lean_ctor_set(v___x_1244_, 2, v_a_1247_);
lean_ctor_set(v___x_1244_, 1, v_a_1313_);
lean_ctor_set(v___x_1244_, 0, v_typeName_1238_);
v___x_1323_ = v___x_1244_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_typeName_1238_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_a_1313_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_a_1247_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 4);
lean_ctor_set(v___x_1298_, 0, v___x_1323_);
v___x_1325_ = v___x_1298_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1327_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1325_);
v___x_1327_ = v___x_1315_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_del_object(v___x_1298_);
lean_dec(v_a_1296_);
lean_dec(v_a_1279_);
lean_del_object(v___x_1276_);
lean_dec(v_name_1273_);
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_typeName_1238_);
v_a_1333_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1312_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1312_);
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
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_del_object(v___x_1298_);
lean_dec(v_a_1296_);
lean_dec(v_a_1279_);
lean_del_object(v___x_1276_);
lean_dec(v_name_1273_);
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_typeName_1238_);
v_a_1341_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1310_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1310_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1279_);
lean_del_object(v___x_1276_);
lean_dec(v_name_1273_);
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_typeName_1238_);
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_del_object(v___x_1276_);
lean_dec(v_name_1273_);
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_idx_1239_);
lean_dec(v_typeName_1238_);
lean_dec(v_fvarId_1237_);
lean_dec_ref(v_k_1236_);
v_a_1354_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1278_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1278_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_a_1268_);
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_idx_1239_);
lean_dec(v_typeName_1238_);
lean_dec(v_fvarId_1237_);
lean_dec_ref(v_k_1236_);
v___x_1364_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5, &l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5_once, _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5);
v___x_1365_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(v___x_1364_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1365_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1247_);
lean_del_object(v___x_1244_);
lean_dec(v_idx_1239_);
lean_dec(v_typeName_1238_);
lean_dec(v_fvarId_1237_);
lean_dec_ref(v_k_1236_);
v_a_1366_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1267_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1267_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1244_);
lean_dec(v_idx_1239_);
lean_dec(v_typeName_1238_);
lean_dec(v_fvarId_1237_);
lean_dec_ref(v_k_1236_);
v_a_1374_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1246_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1246_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_del_object(v___x_1244_);
lean_dec(v_struct_1240_);
lean_dec(v_idx_1239_);
lean_dec(v_typeName_1238_);
lean_dec(v_fvarId_1237_);
lean_dec_ref(v_k_1236_);
v_a_1382_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1242_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1242_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
else
{
lean_object* v_k_1395_; lean_object* v___x_1396_; 
v_k_1395_ = lean_ctor_get(v_code_1160_, 1);
lean_inc(v_value_1235_);
v___x_1396_ = l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(v_value_1235_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = 0;
lean_inc_ref(v_decl_1234_);
v___x_1399_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1398_, v_decl_1234_, v_a_1397_, v_a_1163_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
lean_inc_ref(v_k_1395_);
v___x_1401_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v_k_1395_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1429_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1429_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1429_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___y_1407_; size_t v___x_1423_; size_t v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_ptr_addr(v_k_1395_);
v___x_1424_ = lean_ptr_addr(v_a_1402_);
v___x_1425_ = lean_usize_dec_eq(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v_decl_1234_);
v___y_1407_ = v___x_1425_;
goto v___jp_1406_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_ptr_addr(v_decl_1234_);
lean_dec_ref(v_decl_1234_);
v___x_1427_ = lean_ptr_addr(v_a_1400_);
v___x_1428_ = lean_usize_dec_eq(v___x_1426_, v___x_1427_);
v___y_1407_ = v___x_1428_;
goto v___jp_1406_;
}
v___jp_1406_:
{
if (v___y_1407_ == 0)
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1417_; 
v_isSharedCheck_1417_ = !lean_is_exclusive(v_code_1160_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; lean_object* v_unused_1419_; 
v_unused_1418_ = lean_ctor_get(v_code_1160_, 1);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_code_1160_, 0);
lean_dec(v_unused_1419_);
v___x_1409_ = v_code_1160_;
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_code_1160_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v_a_1402_);
lean_ctor_set(v___x_1409_, 0, v_a_1400_);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1400_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1402_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v___x_1421_; 
lean_dec(v_a_1402_);
lean_dec(v_a_1400_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_code_1160_);
v___x_1421_ = v___x_1404_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_code_1160_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_dec(v_a_1400_);
lean_dec_ref_known(v_code_1160_, 2);
lean_dec_ref(v_decl_1234_);
return v___x_1401_;
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref_known(v_code_1160_, 2);
lean_dec_ref(v_decl_1234_);
v_a_1430_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1399_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1399_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref_known(v_code_1160_, 2);
lean_dec_ref(v_decl_1234_);
v_a_1438_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1396_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1396_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_1446_; lean_object* v_args_1447_; lean_object* v___x_1448_; 
v_fvarId_1446_ = lean_ctor_get(v_code_1160_, 0);
v_args_1447_ = lean_ctor_get(v_code_1160_, 1);
lean_inc(v_fvarId_1446_);
v___x_1448_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_1446_, v_a_1161_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; size_t v_sz_1450_; size_t v___x_1451_; lean_object* v___x_1452_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v_sz_1450_ = lean_array_size(v_args_1447_);
v___x_1451_ = ((size_t)0ULL);
lean_inc_ref(v_args_1447_);
v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_1450_, v___x_1451_, v_args_1447_, v_a_1161_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1478_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1478_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1478_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint8_t v___y_1458_; uint8_t v___x_1474_; 
v___x_1474_ = l_Lean_instBEqFVarId_beq(v_fvarId_1446_, v_a_1449_);
if (v___x_1474_ == 0)
{
v___y_1458_ = v___x_1474_;
goto v___jp_1457_;
}
else
{
size_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = lean_ptr_addr(v_args_1447_);
v___x_1476_ = lean_ptr_addr(v_a_1453_);
v___x_1477_ = lean_usize_dec_eq(v___x_1475_, v___x_1476_);
v___y_1458_ = v___x_1477_;
goto v___jp_1457_;
}
v___jp_1457_:
{
if (v___y_1458_ == 0)
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v_code_1160_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; 
v_unused_1469_ = lean_ctor_get(v_code_1160_, 1);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_code_1160_, 0);
lean_dec(v_unused_1470_);
v___x_1460_ = v_code_1160_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_code_1160_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_a_1453_);
lean_ctor_set(v___x_1460_, 0, v_a_1449_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_a_1453_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1463_);
v___x_1465_ = v___x_1455_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v___x_1472_; 
lean_dec(v_a_1453_);
lean_dec(v_a_1449_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_code_1160_);
v___x_1472_ = v___x_1455_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_code_1160_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1449_);
lean_dec_ref_known(v_code_1160_, 2);
v_a_1479_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1452_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1452_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref_known(v_code_1160_, 2);
v_a_1487_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1448_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1448_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
case 4:
{
lean_object* v_cases_1495_; lean_object* v_typeName_1496_; lean_object* v_resultType_1497_; lean_object* v_discr_1498_; lean_object* v_alts_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1640_; 
v_cases_1495_ = lean_ctor_get(v_code_1160_, 0);
lean_inc_ref(v_cases_1495_);
v_typeName_1496_ = lean_ctor_get(v_cases_1495_, 0);
v_resultType_1497_ = lean_ctor_get(v_cases_1495_, 1);
v_discr_1498_ = lean_ctor_get(v_cases_1495_, 2);
v_alts_1499_ = lean_ctor_get(v_cases_1495_, 3);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_cases_1495_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1501_ = v_cases_1495_;
v_isShared_1502_ = v_isSharedCheck_1640_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_alts_1499_);
lean_inc(v_discr_1498_);
lean_inc(v_resultType_1497_);
lean_inc(v_typeName_1496_);
lean_dec(v_cases_1495_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1640_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; 
lean_inc(v_discr_1498_);
v___x_1503_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_discr_1498_, v_a_1161_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1631_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1631_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1631_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___y_1509_; lean_object* v___y_1518_; uint8_t v___y_1519_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_array_get_size(v_alts_1499_);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_dec_eq(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
v___y_1523_ = v_a_1161_;
v___y_1524_ = v_a_1162_;
v___y_1525_ = v_a_1163_;
v___y_1526_ = v_a_1164_;
v___y_1527_ = v_a_1165_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_array_fget(v_alts_1499_, v___x_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_ctorName_1549_; lean_object* v_params_1550_; lean_object* v_code_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1630_; 
lean_del_object(v___x_1506_);
lean_del_object(v___x_1501_);
v_ctorName_1549_ = lean_ctor_get(v___x_1548_, 0);
v_params_1550_ = lean_ctor_get(v___x_1548_, 1);
v_code_1551_ = lean_ctor_get(v___x_1548_, 2);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1553_ = v___x_1548_;
v_isShared_1554_ = v_isSharedCheck_1630_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_code_1551_);
lean_inc(v_params_1550_);
lean_inc(v_ctorName_1549_);
lean_dec(v___x_1548_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1630_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v_projMap_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_st_ref_get(v_a_1161_);
v_projMap_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_ref(v_projMap_1556_);
lean_dec(v___x_1555_);
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_projMap_1556_, v_a_1504_);
lean_dec_ref(v_projMap_1556_);
if (lean_obj_tag(v___x_1557_) == 1)
{
lean_object* v_val_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
lean_del_object(v___x_1553_);
lean_dec(v_ctorName_1549_);
lean_dec(v_a_1504_);
lean_dec_ref(v_alts_1499_);
lean_dec(v_discr_1498_);
lean_dec_ref(v_resultType_1497_);
lean_dec(v_typeName_1496_);
lean_dec_ref_known(v_code_1160_, 1);
v_val_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = lean_array_get_size(v_val_1558_);
v___x_1560_ = lean_array_get_size(v_params_1550_);
v___x_1561_ = lean_nat_dec_eq(v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_val_1558_);
lean_dec_ref(v_code_1551_);
lean_dec_ref(v_params_1550_);
v___x_1562_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7, &l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7_once, _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7);
v___x_1563_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(v___x_1562_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; size_t v_sz_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = l_Array_toSubarray___redArg(v_val_1558_, v___x_1547_, v___x_1559_);
v_sz_1565_ = lean_array_size(v_params_1550_);
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(v_params_1550_, v_sz_1565_, v___x_1566_, v___x_1564_, v_a_1161_, v_a_1163_);
lean_dec_ref(v_params_1550_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_dec_ref_known(v___x_1567_, 1);
v_code_1160_ = v_code_1551_;
goto _start;
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_code_1551_);
v_a_1569_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1567_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v_projMap_1578_; lean_object* v_fvarMap_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v___x_1557_);
v___x_1577_ = lean_st_ref_take(v_a_1161_);
v_projMap_1578_ = lean_ctor_get(v___x_1577_, 0);
v_fvarMap_1579_ = lean_ctor_get(v___x_1577_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1581_ = v___x_1577_;
v_isShared_1582_ = v_isSharedCheck_1629_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_fvarMap_1579_);
lean_inc(v_projMap_1578_);
lean_dec(v___x_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1629_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
size_t v_sz_1583_; size_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_sz_1583_ = lean_array_size(v_params_1550_);
v___x_1584_ = ((size_t)0ULL);
lean_inc_ref(v_params_1550_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(v_sz_1583_, v___x_1584_, v_params_1550_);
lean_inc(v_a_1504_);
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_projMap_1578_, v_a_1504_, v___x_1585_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1586_);
v___x_1588_ = v___x_1581_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_fvarMap_1579_);
v___x_1588_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_st_ref_set(v_a_1161_, v___x_1588_);
v___x_1590_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v_code_1551_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1627_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1627_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1627_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v_projMap_1596_; lean_object* v_fvarMap_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1626_; 
v___x_1595_ = lean_st_ref_take(v_a_1161_);
v_projMap_1596_ = lean_ctor_get(v___x_1595_, 0);
v_fvarMap_1597_ = lean_ctor_get(v___x_1595_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1599_ = v___x_1595_;
v_isShared_1600_ = v_isSharedCheck_1626_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_fvarMap_1597_);
lean_inc(v_projMap_1596_);
lean_dec(v___x_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1626_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_projMap_1596_, v_a_1504_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_fvarMap_1597_);
v___x_1603_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_st_ref_set(v_a_1161_, v___x_1603_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 2, v_a_1591_);
v___x_1606_ = v___x_1553_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_ctorName_1549_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_params_1550_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_a_1591_);
v___x_1606_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___y_1616_; size_t v___x_1619_; size_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1607_ = lean_mk_empty_array_with_capacity(v___x_1545_);
v___x_1608_ = lean_array_push(v___x_1607_, v___x_1606_);
v___x_1619_ = lean_ptr_addr(v_alts_1499_);
lean_dec_ref(v_alts_1499_);
v___x_1620_ = lean_ptr_addr(v___x_1608_);
v___x_1621_ = lean_usize_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1616_ = v___x_1621_;
goto v___jp_1615_;
}
else
{
size_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_ptr_addr(v_resultType_1497_);
v___x_1623_ = lean_usize_dec_eq(v___x_1622_, v___x_1622_);
v___y_1616_ = v___x_1623_;
goto v___jp_1615_;
}
v___jp_1609_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1610_, 0, v_typeName_1496_);
lean_ctor_set(v___x_1610_, 1, v_resultType_1497_);
lean_ctor_set(v___x_1610_, 2, v_a_1504_);
lean_ctor_set(v___x_1610_, 3, v___x_1608_);
v___x_1611_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1611_);
v___x_1613_ = v___x_1593_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
v___jp_1615_:
{
if (v___y_1616_ == 0)
{
lean_dec(v_discr_1498_);
lean_dec_ref_known(v_code_1160_, 1);
goto v___jp_1609_;
}
else
{
uint8_t v___x_1617_; 
v___x_1617_ = l_Lean_instBEqFVarId_beq(v_discr_1498_, v_a_1504_);
lean_dec(v_discr_1498_);
if (v___x_1617_ == 0)
{
lean_dec_ref_known(v_code_1160_, 1);
goto v___jp_1609_;
}
else
{
lean_object* v___x_1618_; 
lean_dec_ref(v___x_1608_);
lean_del_object(v___x_1593_);
lean_dec(v_a_1504_);
lean_dec_ref(v_resultType_1497_);
lean_dec(v_typeName_1496_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_code_1160_);
return v___x_1618_;
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
lean_del_object(v___x_1553_);
lean_dec_ref(v_params_1550_);
lean_dec(v_ctorName_1549_);
lean_dec(v_a_1504_);
lean_dec_ref(v_alts_1499_);
lean_dec(v_discr_1498_);
lean_dec_ref(v_resultType_1497_);
lean_dec(v_typeName_1496_);
lean_dec_ref_known(v_code_1160_, 1);
return v___x_1590_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1548_);
v___y_1523_ = v_a_1161_;
v___y_1524_ = v_a_1162_;
v___y_1525_ = v_a_1163_;
v___y_1526_ = v_a_1164_;
v___y_1527_ = v_a_1165_;
goto v___jp_1522_;
}
}
v___jp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 3, v___y_1509_);
lean_ctor_set(v___x_1501_, 2, v_a_1504_);
v___x_1511_ = v___x_1501_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_typeName_1496_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_resultType_1497_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v___y_1509_);
v___x_1511_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1512_);
v___x_1514_ = v___x_1506_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
v___jp_1517_:
{
if (v___y_1519_ == 0)
{
lean_dec(v_discr_1498_);
lean_dec_ref_known(v_code_1160_, 1);
v___y_1509_ = v___y_1518_;
goto v___jp_1508_;
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_instBEqFVarId_beq(v_discr_1498_, v_a_1504_);
lean_dec(v_discr_1498_);
if (v___x_1520_ == 0)
{
lean_dec_ref_known(v_code_1160_, 1);
v___y_1509_ = v___y_1518_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1521_; 
lean_dec_ref(v___y_1518_);
lean_del_object(v___x_1506_);
lean_dec(v_a_1504_);
lean_del_object(v___x_1501_);
lean_dec_ref(v_resultType_1497_);
lean_dec(v_typeName_1496_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_code_1160_);
return v___x_1521_;
}
}
}
v___jp_1522_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1499_);
v___x_1529_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(v___x_1528_, v_alts_1499_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; size_t v___x_1531_; size_t v___x_1532_; uint8_t v___x_1533_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = lean_ptr_addr(v_alts_1499_);
lean_dec_ref(v_alts_1499_);
v___x_1532_ = lean_ptr_addr(v_a_1530_);
v___x_1533_ = lean_usize_dec_eq(v___x_1531_, v___x_1532_);
if (v___x_1533_ == 0)
{
v___y_1518_ = v_a_1530_;
v___y_1519_ = v___x_1533_;
goto v___jp_1517_;
}
else
{
size_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = lean_ptr_addr(v_resultType_1497_);
v___x_1535_ = lean_usize_dec_eq(v___x_1534_, v___x_1534_);
v___y_1518_ = v_a_1530_;
v___y_1519_ = v___x_1535_;
goto v___jp_1517_;
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_del_object(v___x_1506_);
lean_dec(v_a_1504_);
lean_del_object(v___x_1501_);
lean_dec_ref(v_alts_1499_);
lean_dec(v_discr_1498_);
lean_dec_ref(v_resultType_1497_);
lean_dec(v_typeName_1496_);
lean_dec_ref_known(v_code_1160_, 1);
v_a_1536_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1529_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1529_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_del_object(v___x_1501_);
lean_dec_ref(v_alts_1499_);
lean_dec(v_discr_1498_);
lean_dec_ref(v_resultType_1497_);
lean_dec(v_typeName_1496_);
lean_dec_ref_known(v_code_1160_, 1);
v_a_1632_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1503_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1503_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1641_; lean_object* v___x_1642_; 
v_fvarId_1641_ = lean_ctor_get(v_code_1160_, 0);
lean_inc(v_fvarId_1641_);
v___x_1642_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_1641_, v_a_1161_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1662_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1662_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1662_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
uint8_t v___x_1647_; 
v___x_1647_ = l_Lean_instBEqFVarId_beq(v_fvarId_1641_, v_a_1643_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1657_; 
v_isSharedCheck_1657_ = !lean_is_exclusive(v_code_1160_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_code_1160_, 0);
lean_dec(v_unused_1658_);
v___x_1649_ = v_code_1160_;
v_isShared_1650_ = v_isSharedCheck_1657_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_code_1160_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1657_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_a_1643_);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1643_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1654_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1652_);
v___x_1654_ = v___x_1645_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec(v_a_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_code_1160_);
v___x_1660_ = v___x_1645_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_code_1160_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec_ref_known(v_code_1160_, 1);
v_a_1663_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1642_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1642_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
case 6:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_code_1160_);
return v___x_1671_;
}
default: 
{
lean_object* v_decl_1672_; lean_object* v_k_1673_; 
v_decl_1672_ = lean_ctor_get(v_code_1160_, 0);
v_k_1673_ = lean_ctor_get(v_code_1160_, 1);
lean_inc_ref(v_k_1673_);
lean_inc_ref(v_decl_1672_);
v_decl_1182_ = v_decl_1672_;
v_k_1183_ = v_k_1673_;
v___y_1184_ = v_a_1161_;
v___y_1185_ = v_a_1162_;
v___y_1186_ = v_a_1163_;
v___y_1187_ = v_a_1164_;
v___y_1188_ = v_a_1165_;
goto v___jp_1181_;
}
}
v___jp_1167_:
{
if (v___y_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec_ref(v_code_1160_);
v___x_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___y_1168_);
lean_ctor_set(v___x_1171_, 1, v___y_1169_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec_ref(v___y_1169_);
lean_dec_ref(v___y_1168_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_code_1160_);
return v___x_1173_;
}
}
v___jp_1174_:
{
if (v___y_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_code_1160_);
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___y_1175_);
lean_ctor_set(v___x_1178_, 1, v___y_1176_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; 
lean_dec_ref(v___y_1176_);
lean_dec_ref(v___y_1175_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_code_1160_);
return v___x_1180_;
}
}
v___jp_1181_:
{
lean_object* v_params_1189_; lean_object* v_type_1190_; lean_object* v_value_1191_; lean_object* v___x_1192_; 
v_params_1189_ = lean_ctor_get(v_decl_1182_, 2);
lean_inc_ref(v_params_1189_);
v_type_1190_ = lean_ctor_get(v_decl_1182_, 3);
lean_inc_ref(v_type_1190_);
v_value_1191_ = lean_ctor_get(v_decl_1182_, 4);
lean_inc_ref(v_value_1191_);
v___x_1192_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v_value_1191_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = 0;
v___x_1195_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1194_, v_decl_1182_, v_type_1190_, v_params_1189_, v_a_1193_, v___y_1186_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v_k_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1197_) == 0)
{
switch(lean_obj_tag(v_code_1160_))
{
case 1:
{
lean_object* v_a_1198_; lean_object* v_decl_1199_; lean_object* v_k_1200_; size_t v___x_1201_; size_t v___x_1202_; uint8_t v___x_1203_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v_decl_1199_ = lean_ctor_get(v_code_1160_, 0);
v_k_1200_ = lean_ctor_get(v_code_1160_, 1);
v___x_1201_ = lean_ptr_addr(v_k_1200_);
v___x_1202_ = lean_ptr_addr(v_a_1198_);
v___x_1203_ = lean_usize_dec_eq(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
v___y_1168_ = v_a_1196_;
v___y_1169_ = v_a_1198_;
v___y_1170_ = v___x_1203_;
goto v___jp_1167_;
}
else
{
size_t v___x_1204_; size_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1204_ = lean_ptr_addr(v_decl_1199_);
v___x_1205_ = lean_ptr_addr(v_a_1196_);
v___x_1206_ = lean_usize_dec_eq(v___x_1204_, v___x_1205_);
v___y_1168_ = v_a_1196_;
v___y_1169_ = v_a_1198_;
v___y_1170_ = v___x_1206_;
goto v___jp_1167_;
}
}
case 2:
{
lean_object* v_a_1207_; lean_object* v_decl_1208_; lean_object* v_k_1209_; size_t v___x_1210_; size_t v___x_1211_; uint8_t v___x_1212_; 
v_a_1207_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1197_, 1);
v_decl_1208_ = lean_ctor_get(v_code_1160_, 0);
v_k_1209_ = lean_ctor_get(v_code_1160_, 1);
v___x_1210_ = lean_ptr_addr(v_k_1209_);
v___x_1211_ = lean_ptr_addr(v_a_1207_);
v___x_1212_ = lean_usize_dec_eq(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
v___y_1175_ = v_a_1196_;
v___y_1176_ = v_a_1207_;
v___y_1177_ = v___x_1212_;
goto v___jp_1174_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_ptr_addr(v_decl_1208_);
v___x_1214_ = lean_ptr_addr(v_a_1196_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
v___y_1175_ = v_a_1196_;
v___y_1176_ = v_a_1207_;
v___y_1177_ = v___x_1215_;
goto v___jp_1174_;
}
}
default: 
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1196_);
lean_dec_ref(v_code_1160_);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1197_, 0);
lean_dec(v_unused_1225_);
v___x_1217_ = v___x_1197_;
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v___x_1197_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1219_ = lean_obj_once(&l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2, &l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2_once, _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2);
v___x_1220_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__0(v___x_1219_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1222_ = v___x_1217_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_dec(v_a_1196_);
lean_dec_ref(v_code_1160_);
return v___x_1197_;
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_k_1183_);
lean_dec_ref(v_code_1160_);
v_a_1226_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1195_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1195_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_dec_ref(v_type_1190_);
lean_dec_ref(v_params_1189_);
lean_dec_ref(v_k_1183_);
lean_dec_ref(v_decl_1182_);
lean_dec_ref(v_code_1160_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitAlt(lean_object* v_alt_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___y_1682_; 
switch(lean_obj_tag(v_alt_1674_))
{
case 0:
{
lean_object* v_code_1701_; 
v_code_1701_ = lean_ctor_get(v_alt_1674_, 2);
lean_inc_ref(v_code_1701_);
v___y_1682_ = v_code_1701_;
goto v___jp_1681_;
}
case 1:
{
lean_object* v_code_1702_; 
v_code_1702_ = lean_ctor_get(v_alt_1674_, 1);
lean_inc_ref(v_code_1702_);
v___y_1682_ = v_code_1702_;
goto v___jp_1681_;
}
default: 
{
lean_object* v_code_1703_; 
v_code_1703_ = lean_ctor_get(v_alt_1674_, 0);
lean_inc_ref(v_code_1703_);
v___y_1682_ = v_code_1703_;
goto v___jp_1681_;
}
}
v___jp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v___y_1682_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1674_, v_a_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v_alt_1674_);
v_a_1693_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitAlt___boxed(lean_object* v_alt_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Compiler_LCNF_StructProjCases_visitAlt(v_alt_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5___boxed(lean_object* v_i_1712_, lean_object* v_as_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(v_i_1712_, v_as_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitCode___boxed(lean_object* v_code_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(v_code_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1(lean_object* v_00_u03b2_1729_, lean_object* v_m_1730_, lean_object* v_a_1731_, lean_object* v_b_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_m_1730_, v_a_1731_, v_b_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3(lean_object* v_00_u03b2_1734_, lean_object* v_m_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_m_1735_, v_a_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___boxed(lean_object* v_00_u03b2_1738_, lean_object* v_m_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3(v_00_u03b2_1738_, v_m_1739_, v_a_1740_);
lean_dec(v_a_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6(lean_object* v_as_1742_, size_t v_sz_1743_, size_t v_i_1744_, lean_object* v_b_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(v_as_1742_, v_sz_1743_, v_i_1744_, v_b_1745_, v___y_1746_, v___y_1748_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___boxed(lean_object* v_as_1753_, lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6(v_as_1753_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v_as_1753_);
return v_res_1765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2(lean_object* v_00_u03b2_1766_, lean_object* v_a_1767_, lean_object* v_x_1768_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_1767_, v_x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1770_, lean_object* v_a_1771_, lean_object* v_x_1772_){
_start:
{
uint8_t v_res_1773_; lean_object* v_r_1774_; 
v_res_1773_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2(v_00_u03b2_1770_, v_a_1771_, v_x_1772_);
lean_dec(v_x_1772_);
lean_dec(v_a_1771_);
v_r_1774_ = lean_box(v_res_1773_);
return v_r_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3(lean_object* v_00_u03b2_1775_, lean_object* v_data_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(v_data_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4(lean_object* v_00_u03b2_1778_, lean_object* v_a_1779_, lean_object* v_b_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(v_a_1779_, v_b_1780_, v_x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7(lean_object* v_00_u03b2_1783_, lean_object* v_a_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_1784_, v_x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1787_, lean_object* v_a_1788_, lean_object* v_x_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7(v_00_u03b2_1787_, v_a_1788_, v_x_1789_);
lean_dec(v_a_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1791_, lean_object* v_i_1792_, lean_object* v_source_1793_, lean_object* v_target_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(v_i_1792_, v_source_1793_, v_target_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(v_x_1797_, v_x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(lean_object* v_f_1800_, lean_object* v_v_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
if (lean_obj_tag(v_v_1801_) == 0)
{
lean_object* v_code_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1832_; 
v_code_1808_ = lean_ctor_get(v_v_1801_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_v_1801_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1810_ = v_v_1801_;
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_code_1808_);
lean_dec(v_v_1801_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; 
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
v___x_1812_ = lean_apply_7(v_f_1800_, v_code_1808_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, lean_box(0));
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_a_1813_);
v___x_1818_ = v___x_1810_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1818_);
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_del_object(v___x_1810_);
v_a_1824_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1812_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1812_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref(v_f_1800_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_v_1801_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg___boxed(lean_object* v_f_1834_, lean_object* v_v_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(v_f_1834_, v_v_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0(uint8_t v_pu_1843_, lean_object* v_f_1844_, lean_object* v_v_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(v_f_1844_, v_v_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___boxed(lean_object* v_pu_1853_, lean_object* v_f_1854_, lean_object* v_v_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v_pu_boxed_1862_; lean_object* v_res_1863_; 
v_pu_boxed_1862_ = lean_unbox(v_pu_1853_);
v_res_1863_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0(v_pu_boxed_1862_, v_f_1854_, v_v_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitDecl(lean_object* v_decl_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_toSignature_1872_; lean_object* v_value_1873_; uint8_t v_recursive_1874_; lean_object* v_inlineAttr_x3f_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1900_; 
v_toSignature_1872_ = lean_ctor_get(v_decl_1865_, 0);
v_value_1873_ = lean_ctor_get(v_decl_1865_, 1);
v_recursive_1874_ = lean_ctor_get_uint8(v_decl_1865_, sizeof(void*)*3);
v_inlineAttr_x3f_1875_ = lean_ctor_get(v_decl_1865_, 2);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_decl_1865_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1877_ = v_decl_1865_;
v_isShared_1878_ = v_isSharedCheck_1900_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_inlineAttr_x3f_1875_);
lean_inc(v_value_1873_);
lean_inc(v_toSignature_1872_);
lean_dec(v_decl_1865_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1900_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___f_1879_; lean_object* v___x_1880_; 
v___f_1879_ = ((lean_object*)(l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0));
v___x_1880_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(v___f_1879_, v_value_1873_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1891_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v_a_1881_);
v___x_1886_ = v___x_1877_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_toSignature_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_a_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_inlineAttr_x3f_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*3, v_recursive_1874_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_del_object(v___x_1877_);
lean_dec(v_inlineAttr_x3f_1875_);
lean_dec_ref(v_toSignature_1872_);
v_a_1892_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1880_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1880_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_StructProjCases_visitDecl___boxed(lean_object* v_decl_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Compiler_LCNF_StructProjCases_visitDecl(v_decl_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_structProjCases___lam__0(lean_object* v_x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_StructProjCases_visitDecl___boxed), 7, 1);
lean_closure_set(v___x_1915_, 0, v_x_1909_);
v___x_1916_ = l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(v___x_1915_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_structProjCases___lam__0___boxed(lean_object* v_x_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Compiler_LCNF_structProjCases___lam__0(v_x_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_structProjCases___closed__3(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___f_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___f_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_structProjCases___closed__0));
v___x_1930_ = 1;
v___x_1931_ = ((lean_object*)(l_Lean_Compiler_LCNF_structProjCases___closed__2));
v___x_1932_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1931_, v___x_1930_, v___f_1929_, v___x_1928_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_structProjCases(void){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_obj_once(&l_Lean_Compiler_LCNF_structProjCases___closed__3, &l_Lean_Compiler_LCNF_structProjCases___closed__3_once, _init_l_Lean_Compiler_LCNF_structProjCases___closed__3);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_));
v___x_2005_ = 1;
v___x_2006_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_));
v___x_2007_ = l_Lean_registerTraceClass(v___x_2004_, v___x_2005_, v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2____boxed(lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_();
return v_res_2009_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_StructProjCases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_structProjCases = _init_l_Lean_Compiler_LCNF_structProjCases();
lean_mark_persistent(l_Lean_Compiler_LCNF_structProjCases);
res = l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_StructProjCases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_StructProjCases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
}
#ifdef __cplusplus
}
#endif
