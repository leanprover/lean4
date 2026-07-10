// Lean compiler output
// Module: Lean.MonadEnv
// Imports: import Init.Control.Do public import Lean.Elab.Exception public import Lean.Log public import Lean.AuxRecursor public import Lean.Compiler.Old
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
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_throwUnknownConstant___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_allM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_withEnv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withEnv___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_withEnv___redArg___closed__0 = (const lean_object*)&l_Lean_withEnv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductiveCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_withoutModifyingEnv_x27___redArg___closed__0 = (const lean_object*)&l_Lean_withoutModifyingEnv_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isInductiveCore_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_isInductiveCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isInductiveCore_x3f___closed__0 = (const lean_object*)&l_Lean_isInductiveCore_x3f___closed__0_value;
static const lean_string_object l_Lean_isInductiveCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.isInductiveCore\?"};
static const lean_object* l_Lean_isInductiveCore_x3f___closed__1 = (const lean_object*)&l_Lean_isInductiveCore_x3f___closed__1_value;
static const lean_string_object l_Lean_isInductiveCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_isInductiveCore_x3f___closed__2 = (const lean_object*)&l_Lean_isInductiveCore_x3f___closed__2_value;
static lean_once_cell_t l_Lean_isInductiveCore_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isInductiveCore_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_isDefn_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_isDefn_x3f___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isDefn_x3f___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_isCtor_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isCtor_x3f___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isRec_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_isRec_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_isRec_x3f___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_isRec_x3f___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isRec_x3f___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLevelParam, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoDefn___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoDefn___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not a recursor"};
static const lean_object* l_Lean_getConstInfoRec___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoRec___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasCompileError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_evalConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_stringToMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_evalConst___redArg___closed__0 = (const lean_object*)&l_Lean_evalConst___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_evalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0(lean_object* v_env_1_, lean_object* v_x_2_){
_start:
{
lean_inc_ref(v_env_1_);
return v_env_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0___boxed(lean_object* v_env_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_setEnv___redArg___lam__0(v_env_3_, v_x_4_);
lean_dec_ref(v_x_4_);
lean_dec_ref(v_env_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg(lean_object* v_inst_6_, lean_object* v_env_7_){
_start:
{
lean_object* v_modifyEnv_8_; lean_object* v___f_9_; lean_object* v___x_10_; 
v_modifyEnv_8_ = lean_ctor_get(v_inst_6_, 1);
lean_inc(v_modifyEnv_8_);
lean_dec_ref(v_inst_6_);
v___f_9_ = lean_alloc_closure((void*)(l_Lean_setEnv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_9_, 0, v_env_7_);
v___x_10_ = lean_apply_1(v_modifyEnv_8_, v___f_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv(lean_object* v_m_11_, lean_object* v_inst_12_, lean_object* v_env_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_setEnv___redArg(v_inst_12_, v_env_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0(lean_object* v_x_15_){
_start:
{
lean_object* v_fst_16_; 
v_fst_16_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_fst_16_);
return v_fst_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0___boxed(lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_withEnv___redArg___lam__0(v_x_17_);
lean_dec_ref(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1(lean_object* v_x_19_, lean_object* v_____r_20_){
_start:
{
lean_inc(v_x_19_);
return v_x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1___boxed(lean_object* v_x_21_, lean_object* v_____r_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_withEnv___redArg___lam__1(v_x_21_, v_____r_22_);
lean_dec(v_x_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2(lean_object* v___x_24_, lean_object* v_x_25_){
_start:
{
lean_inc(v___x_24_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2___boxed(lean_object* v___x_26_, lean_object* v_x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_withEnv___redArg___lam__2(v___x_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v___x_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__3(lean_object* v_toFunctor_29_, lean_object* v_inst_30_, lean_object* v_env_31_, lean_object* v_toBind_32_, lean_object* v___f_33_, lean_object* v_inst_34_, lean_object* v___f_35_, lean_object* v_saved_36_){
_start:
{
lean_object* v_map_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v_y_42_; lean_object* v___x_43_; 
v_map_37_ = lean_ctor_get(v_toFunctor_29_, 0);
lean_inc(v_map_37_);
lean_dec_ref(v_toFunctor_29_);
lean_inc_ref(v_inst_30_);
v___x_38_ = l_Lean_setEnv___redArg(v_inst_30_, v_env_31_);
v___x_39_ = lean_apply_4(v_toBind_32_, lean_box(0), lean_box(0), v___x_38_, v___f_33_);
v___x_40_ = l_Lean_setEnv___redArg(v_inst_30_, v_saved_36_);
v___f_41_ = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_41_, 0, v___x_40_);
v_y_42_ = lean_apply_4(v_inst_34_, lean_box(0), lean_box(0), v___x_39_, v___f_41_);
v___x_43_ = lean_apply_4(v_map_37_, lean_box(0), lean_box(0), v___f_35_, v_y_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg(lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_env_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_toApplicative_50_; lean_object* v_toBind_51_; lean_object* v_getEnv_52_; lean_object* v_toFunctor_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; 
v_toApplicative_50_ = lean_ctor_get(v_inst_45_, 0);
lean_inc_ref(v_toApplicative_50_);
v_toBind_51_ = lean_ctor_get(v_inst_45_, 1);
lean_inc_n(v_toBind_51_, 2);
lean_dec_ref(v_inst_45_);
v_getEnv_52_ = lean_ctor_get(v_inst_47_, 0);
lean_inc(v_getEnv_52_);
v_toFunctor_53_ = lean_ctor_get(v_toApplicative_50_, 0);
lean_inc_ref(v_toFunctor_53_);
lean_dec_ref(v_toApplicative_50_);
v___f_54_ = ((lean_object*)(l_Lean_withEnv___redArg___closed__0));
v___f_55_ = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_55_, 0, v_x_49_);
v___f_56_ = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__3), 8, 7);
lean_closure_set(v___f_56_, 0, v_toFunctor_53_);
lean_closure_set(v___f_56_, 1, v_inst_47_);
lean_closure_set(v___f_56_, 2, v_env_48_);
lean_closure_set(v___f_56_, 3, v_toBind_51_);
lean_closure_set(v___f_56_, 4, v___f_55_);
lean_closure_set(v___f_56_, 5, v_inst_46_);
lean_closure_set(v___f_56_, 6, v___f_54_);
v___x_57_ = lean_apply_4(v_toBind_51_, lean_box(0), lean_box(0), v_getEnv_52_, v___f_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv(lean_object* v_m_58_, lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_env_63_, lean_object* v_x_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_withEnv___redArg(v_inst_60_, v_inst_61_, v_inst_62_, v_env_63_, v_x_64_);
return v___x_65_;
}
}
LEAN_EXPORT uint8_t l_Lean_isInductiveCore(lean_object* v_env_66_, lean_object* v_declName_67_){
_start:
{
uint8_t v___x_68_; lean_object* v___x_69_; 
v___x_68_ = 0;
v___x_69_ = l_Lean_Environment_findAsync_x3f(v_env_66_, v_declName_67_, v___x_68_);
if (lean_obj_tag(v___x_69_) == 1)
{
lean_object* v_val_70_; uint8_t v_kind_71_; 
v_val_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_70_);
lean_dec_ref_known(v___x_69_, 1);
v_kind_71_ = lean_ctor_get_uint8(v_val_70_, sizeof(void*)*3);
lean_dec(v_val_70_);
if (v_kind_71_ == 5)
{
uint8_t v___x_72_; 
v___x_72_ = 1;
return v___x_72_;
}
else
{
return v___x_68_;
}
}
else
{
lean_dec(v___x_69_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductiveCore___boxed(lean_object* v_env_73_, lean_object* v_declName_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_isInductiveCore(v_env_73_, v_declName_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg___lam__0(lean_object* v_declName_77_, lean_object* v_toPure_78_, lean_object* v_____do__lift_79_){
_start:
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = l_Lean_isInductiveCore(v_____do__lift_79_, v_declName_77_);
v___x_81_ = lean_box(v___x_80_);
v___x_82_ = lean_apply_2(v_toPure_78_, lean_box(0), v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg(lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_declName_85_){
_start:
{
lean_object* v_toApplicative_86_; lean_object* v_toBind_87_; lean_object* v_getEnv_88_; lean_object* v_toPure_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
v_toApplicative_86_ = lean_ctor_get(v_inst_83_, 0);
lean_inc_ref(v_toApplicative_86_);
v_toBind_87_ = lean_ctor_get(v_inst_83_, 1);
lean_inc(v_toBind_87_);
lean_dec_ref(v_inst_83_);
v_getEnv_88_ = lean_ctor_get(v_inst_84_, 0);
lean_inc(v_getEnv_88_);
lean_dec_ref(v_inst_84_);
v_toPure_89_ = lean_ctor_get(v_toApplicative_86_, 1);
lean_inc(v_toPure_89_);
lean_dec_ref(v_toApplicative_86_);
v___f_90_ = lean_alloc_closure((void*)(l_Lean_isInductive___redArg___lam__0), 3, 2);
lean_closure_set(v___f_90_, 0, v_declName_85_);
lean_closure_set(v___f_90_, 1, v_toPure_89_);
v___x_91_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v_getEnv_88_, v___f_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object* v_m_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_declName_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_isInductive___redArg(v_inst_93_, v_inst_94_, v_declName_95_);
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_isRecCore(lean_object* v_env_97_, lean_object* v_declName_98_){
_start:
{
uint8_t v___x_99_; lean_object* v___x_100_; 
v___x_99_ = 0;
v___x_100_ = l_Lean_Environment_findAsync_x3f(v_env_97_, v_declName_98_, v___x_99_);
if (lean_obj_tag(v___x_100_) == 1)
{
lean_object* v_val_101_; uint8_t v_kind_102_; 
v_val_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_101_);
lean_dec_ref_known(v___x_100_, 1);
v_kind_102_ = lean_ctor_get_uint8(v_val_101_, sizeof(void*)*3);
lean_dec(v_val_101_);
if (v_kind_102_ == 7)
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
else
{
return v___x_99_;
}
}
else
{
lean_dec(v___x_100_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object* v_env_104_, lean_object* v_declName_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Lean_isRecCore(v_env_104_, v_declName_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___redArg___lam__0(lean_object* v_declName_108_, lean_object* v_toPure_109_, lean_object* v_____do__lift_110_){
_start:
{
uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = l_Lean_isRecCore(v_____do__lift_110_, v_declName_108_);
v___x_112_ = lean_box(v___x_111_);
v___x_113_ = lean_apply_2(v_toPure_109_, lean_box(0), v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___redArg(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_declName_116_){
_start:
{
lean_object* v_toApplicative_117_; lean_object* v_toBind_118_; lean_object* v_getEnv_119_; lean_object* v_toPure_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
v_toApplicative_117_ = lean_ctor_get(v_inst_114_, 0);
lean_inc_ref(v_toApplicative_117_);
v_toBind_118_ = lean_ctor_get(v_inst_114_, 1);
lean_inc(v_toBind_118_);
lean_dec_ref(v_inst_114_);
v_getEnv_119_ = lean_ctor_get(v_inst_115_, 0);
lean_inc(v_getEnv_119_);
lean_dec_ref(v_inst_115_);
v_toPure_120_ = lean_ctor_get(v_toApplicative_117_, 1);
lean_inc(v_toPure_120_);
lean_dec_ref(v_toApplicative_117_);
v___f_121_ = lean_alloc_closure((void*)(l_Lean_isRec___redArg___lam__0), 3, 2);
lean_closure_set(v___f_121_, 0, v_declName_116_);
lean_closure_set(v___f_121_, 1, v_toPure_120_);
v___x_122_ = lean_apply_4(v_toBind_118_, lean_box(0), lean_box(0), v_getEnv_119_, v___f_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object* v_m_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_declName_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_isRec___redArg(v_inst_124_, v_inst_125_, v_declName_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg___lam__0(lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_x_131_, lean_object* v_____do__lift_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = l_Lean_Environment_unlockAsync(v_____do__lift_132_);
v___x_134_ = l_Lean_withEnv___redArg(v_inst_128_, v_inst_129_, v_inst_130_, v___x_133_, v_x_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg(lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_toBind_139_; lean_object* v_getEnv_140_; lean_object* v___f_141_; lean_object* v___x_142_; 
v_toBind_139_ = lean_ctor_get(v_inst_135_, 1);
lean_inc(v_toBind_139_);
v_getEnv_140_ = lean_ctor_get(v_inst_136_, 0);
lean_inc(v_getEnv_140_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___redArg___lam__0), 5, 4);
lean_closure_set(v___f_141_, 0, v_inst_135_);
lean_closure_set(v___f_141_, 1, v_inst_137_);
lean_closure_set(v___f_141_, 2, v_inst_136_);
lean_closure_set(v___f_141_, 3, v_x_138_);
v___x_142_ = lean_apply_4(v_toBind_139_, lean_box(0), lean_box(0), v_getEnv_140_, v___f_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object* v_m_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_00_u03b1_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_toBind_149_; lean_object* v_getEnv_150_; lean_object* v___f_151_; lean_object* v___x_152_; 
v_toBind_149_ = lean_ctor_get(v_inst_144_, 1);
lean_inc(v_toBind_149_);
v_getEnv_150_ = lean_ctor_get(v_inst_145_, 0);
lean_inc(v_getEnv_150_);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___redArg___lam__0), 5, 4);
lean_closure_set(v___f_151_, 0, v_inst_144_);
lean_closure_set(v___f_151_, 1, v_inst_146_);
lean_closure_set(v___f_151_, 2, v_inst_145_);
lean_closure_set(v___f_151_, 3, v_x_148_);
v___x_152_ = lean_apply_4(v_toBind_149_, lean_box(0), lean_box(0), v_getEnv_150_, v___f_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0(lean_object* v_x_153_){
_start:
{
lean_object* v_fst_154_; 
v_fst_154_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_fst_154_);
return v_fst_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__0(v_x_155_);
lean_dec_ref(v_x_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__1(lean_object* v_a_157_, lean_object* v_toPure_158_, lean_object* v_____do__lift_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_a_157_);
lean_ctor_set(v___x_160_, 1, v_____do__lift_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
v___x_162_ = lean_apply_2(v_toPure_158_, lean_box(0), v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__2(lean_object* v_toPure_163_, lean_object* v_toBind_164_, lean_object* v_getEnv_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_168_; 
v___f_167_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_167_, 0, v_a_166_);
lean_closure_set(v___f_167_, 1, v_toPure_163_);
v___x_168_ = lean_apply_4(v_toBind_164_, lean_box(0), lean_box(0), v_getEnv_165_, v___f_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__3(lean_object* v_toPure_169_, lean_object* v_e_170_){
_start:
{
lean_object* v_a_171_; lean_object* v___x_172_; 
v_a_171_ = lean_ctor_get(v_e_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v_e_170_);
v___x_172_ = lean_apply_2(v_toPure_169_, lean_box(0), v_a_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4(lean_object* v___x_173_, lean_object* v_x_174_){
_start:
{
lean_inc(v___x_173_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(lean_object* v___x_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__4(v___x_175_, v_x_176_);
lean_dec(v_x_176_);
lean_dec(v___x_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__5(lean_object* v_toFunctor_178_, lean_object* v_toBind_179_, lean_object* v_x_180_, lean_object* v___f_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v___f_184_, lean_object* v___f_185_, lean_object* v_env_186_){
_start:
{
lean_object* v_map_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v_y_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_map_187_ = lean_ctor_get(v_toFunctor_178_, 0);
lean_inc(v_map_187_);
lean_dec_ref(v_toFunctor_178_);
lean_inc(v_toBind_179_);
v___x_188_ = lean_apply_4(v_toBind_179_, lean_box(0), lean_box(0), v_x_180_, v___f_181_);
v___x_189_ = l_Lean_setEnv___redArg(v_inst_182_, v_env_186_);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_190_, 0, v___x_189_);
v_y_191_ = lean_apply_4(v_inst_183_, lean_box(0), lean_box(0), v___x_188_, v___f_190_);
v___x_192_ = lean_apply_4(v_map_187_, lean_box(0), lean_box(0), v___f_184_, v_y_191_);
v___x_193_ = lean_apply_4(v_toBind_179_, lean_box(0), lean_box(0), v___x_192_, v___f_185_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_x_198_){
_start:
{
lean_object* v_toApplicative_199_; lean_object* v_toBind_200_; lean_object* v_getEnv_201_; lean_object* v_toFunctor_202_; lean_object* v_toPure_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v_toApplicative_199_ = lean_ctor_get(v_inst_195_, 0);
lean_inc_ref(v_toApplicative_199_);
v_toBind_200_ = lean_ctor_get(v_inst_195_, 1);
lean_inc_n(v_toBind_200_, 3);
lean_dec_ref(v_inst_195_);
v_getEnv_201_ = lean_ctor_get(v_inst_196_, 0);
lean_inc_n(v_getEnv_201_, 2);
v_toFunctor_202_ = lean_ctor_get(v_toApplicative_199_, 0);
lean_inc_ref(v_toFunctor_202_);
v_toPure_203_ = lean_ctor_get(v_toApplicative_199_, 1);
lean_inc_n(v_toPure_203_, 2);
lean_dec_ref(v_toApplicative_199_);
v___f_204_ = ((lean_object*)(l_Lean_withoutModifyingEnv_x27___redArg___closed__0));
v___f_205_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_205_, 0, v_toPure_203_);
lean_closure_set(v___f_205_, 1, v_toBind_200_);
lean_closure_set(v___f_205_, 2, v_getEnv_201_);
v___f_206_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_206_, 0, v_toPure_203_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_207_, 0, v_toFunctor_202_);
lean_closure_set(v___f_207_, 1, v_toBind_200_);
lean_closure_set(v___f_207_, 2, v_x_198_);
lean_closure_set(v___f_207_, 3, v___f_205_);
lean_closure_set(v___f_207_, 4, v_inst_196_);
lean_closure_set(v___f_207_, 5, v_inst_197_);
lean_closure_set(v___f_207_, 6, v___f_204_);
lean_closure_set(v___f_207_, 7, v___f_206_);
v___x_208_ = lean_apply_4(v_toBind_200_, lean_box(0), lean_box(0), v_getEnv_201_, v___f_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object* v_m_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_00_u03b1_213_, lean_object* v_x_214_){
_start:
{
lean_object* v_toApplicative_215_; lean_object* v_toBind_216_; lean_object* v_getEnv_217_; lean_object* v_toFunctor_218_; lean_object* v_toPure_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_224_; 
v_toApplicative_215_ = lean_ctor_get(v_inst_210_, 0);
lean_inc_ref(v_toApplicative_215_);
v_toBind_216_ = lean_ctor_get(v_inst_210_, 1);
lean_inc_n(v_toBind_216_, 3);
lean_dec_ref(v_inst_210_);
v_getEnv_217_ = lean_ctor_get(v_inst_211_, 0);
lean_inc_n(v_getEnv_217_, 2);
v_toFunctor_218_ = lean_ctor_get(v_toApplicative_215_, 0);
lean_inc_ref(v_toFunctor_218_);
v_toPure_219_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc_n(v_toPure_219_, 2);
lean_dec_ref(v_toApplicative_215_);
v___f_220_ = ((lean_object*)(l_Lean_withoutModifyingEnv_x27___redArg___closed__0));
v___f_221_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_221_, 0, v_toPure_219_);
lean_closure_set(v___f_221_, 1, v_toBind_216_);
lean_closure_set(v___f_221_, 2, v_getEnv_217_);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_222_, 0, v_toPure_219_);
v___f_223_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_223_, 0, v_toFunctor_218_);
lean_closure_set(v___f_223_, 1, v_toBind_216_);
lean_closure_set(v___f_223_, 2, v_x_214_);
lean_closure_set(v___f_223_, 3, v___f_221_);
lean_closure_set(v___f_223_, 4, v_inst_211_);
lean_closure_set(v___f_223_, 5, v_inst_212_);
lean_closure_set(v___f_223_, 6, v___f_220_);
lean_closure_set(v___f_223_, 7, v___f_222_);
v___x_224_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v_getEnv_217_, v___f_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg___lam__0(lean_object* v_declName_225_, lean_object* v_failK_226_, lean_object* v_k_227_, lean_object* v_us_228_, lean_object* v_____do__lift_229_){
_start:
{
uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 0;
v___x_231_ = l_Lean_Environment_find_x3f(v_____do__lift_229_, v_declName_225_, v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_us_228_);
lean_dec(v_k_227_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_failK_226_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_235_; 
lean_dec(v_failK_226_);
v_val_234_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_231_, 1);
v___x_235_ = lean_apply_2(v_k_227_, v_val_234_, v_us_228_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_e_238_, lean_object* v_failK_239_, lean_object* v_k_240_){
_start:
{
if (lean_obj_tag(v_e_238_) == 4)
{
lean_object* v_toBind_241_; lean_object* v_declName_242_; lean_object* v_us_243_; lean_object* v_getEnv_244_; lean_object* v___f_245_; lean_object* v___x_246_; 
v_toBind_241_ = lean_ctor_get(v_inst_236_, 1);
lean_inc(v_toBind_241_);
lean_dec_ref(v_inst_236_);
v_declName_242_ = lean_ctor_get(v_e_238_, 0);
lean_inc(v_declName_242_);
v_us_243_ = lean_ctor_get(v_e_238_, 1);
lean_inc(v_us_243_);
lean_dec_ref_known(v_e_238_, 2);
v_getEnv_244_ = lean_ctor_get(v_inst_237_, 0);
lean_inc(v_getEnv_244_);
lean_dec_ref(v_inst_237_);
v___f_245_ = lean_alloc_closure((void*)(l_Lean_matchConst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_245_, 0, v_declName_242_);
lean_closure_set(v___f_245_, 1, v_failK_239_);
lean_closure_set(v___f_245_, 2, v_k_240_);
lean_closure_set(v___f_245_, 3, v_us_243_);
v___x_246_ = lean_apply_4(v_toBind_241_, lean_box(0), lean_box(0), v_getEnv_244_, v___f_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_k_240_);
lean_dec_ref(v_e_238_);
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_failK_239_, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object* v_m_249_, lean_object* v_00_u03b1_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_e_253_, lean_object* v_failK_254_, lean_object* v_k_255_){
_start:
{
if (lean_obj_tag(v_e_253_) == 4)
{
lean_object* v_toBind_256_; lean_object* v_declName_257_; lean_object* v_us_258_; lean_object* v_getEnv_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v_toBind_256_ = lean_ctor_get(v_inst_251_, 1);
lean_inc(v_toBind_256_);
lean_dec_ref(v_inst_251_);
v_declName_257_ = lean_ctor_get(v_e_253_, 0);
lean_inc(v_declName_257_);
v_us_258_ = lean_ctor_get(v_e_253_, 1);
lean_inc(v_us_258_);
lean_dec_ref_known(v_e_253_, 2);
v_getEnv_259_ = lean_ctor_get(v_inst_252_, 0);
lean_inc(v_getEnv_259_);
lean_dec_ref(v_inst_252_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_matchConst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_260_, 0, v_declName_257_);
lean_closure_set(v___f_260_, 1, v_failK_254_);
lean_closure_set(v___f_260_, 2, v_k_255_);
lean_closure_set(v___f_260_, 3, v_us_258_);
v___x_261_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v_getEnv_259_, v___f_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_k_255_);
lean_dec_ref(v_e_253_);
lean_dec_ref(v_inst_252_);
lean_dec_ref(v_inst_251_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_apply_1(v_failK_254_, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg___lam__0(lean_object* v_declName_264_, lean_object* v_failK_265_, lean_object* v_k_266_, lean_object* v_us_267_, lean_object* v_____do__lift_268_){
_start:
{
uint8_t v___x_269_; lean_object* v___x_270_; 
v___x_269_ = 0;
v___x_270_ = l_Lean_Environment_find_x3f(v_____do__lift_268_, v_declName_264_, v___x_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_us_267_);
lean_dec(v_k_266_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_apply_1(v_failK_265_, v___x_271_);
return v___x_272_;
}
else
{
lean_object* v_val_273_; 
v_val_273_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v___x_270_, 1);
if (lean_obj_tag(v_val_273_) == 5)
{
lean_object* v_val_274_; lean_object* v___x_275_; 
lean_dec(v_failK_265_);
v_val_274_ = lean_ctor_get(v_val_273_, 0);
lean_inc_ref(v_val_274_);
lean_dec_ref_known(v_val_273_, 1);
v___x_275_ = lean_apply_2(v_k_266_, v_val_274_, v_us_267_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_val_273_);
lean_dec(v_us_267_);
lean_dec(v_k_266_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_1(v_failK_265_, v___x_276_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_e_280_, lean_object* v_failK_281_, lean_object* v_k_282_){
_start:
{
if (lean_obj_tag(v_e_280_) == 4)
{
lean_object* v_toBind_283_; lean_object* v_declName_284_; lean_object* v_us_285_; lean_object* v_getEnv_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v_toBind_283_ = lean_ctor_get(v_inst_278_, 1);
lean_inc(v_toBind_283_);
lean_dec_ref(v_inst_278_);
v_declName_284_ = lean_ctor_get(v_e_280_, 0);
lean_inc(v_declName_284_);
v_us_285_ = lean_ctor_get(v_e_280_, 1);
lean_inc(v_us_285_);
lean_dec_ref_known(v_e_280_, 2);
v_getEnv_286_ = lean_ctor_get(v_inst_279_, 0);
lean_inc(v_getEnv_286_);
lean_dec_ref(v_inst_279_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_matchConstInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_287_, 0, v_declName_284_);
lean_closure_set(v___f_287_, 1, v_failK_281_);
lean_closure_set(v___f_287_, 2, v_k_282_);
lean_closure_set(v___f_287_, 3, v_us_285_);
v___x_288_ = lean_apply_4(v_toBind_283_, lean_box(0), lean_box(0), v_getEnv_286_, v___f_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_k_282_);
lean_dec_ref(v_e_280_);
lean_dec_ref(v_inst_279_);
lean_dec_ref(v_inst_278_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_failK_281_, v___x_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object* v_m_291_, lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_e_295_, lean_object* v_failK_296_, lean_object* v_k_297_){
_start:
{
if (lean_obj_tag(v_e_295_) == 4)
{
lean_object* v_toBind_298_; lean_object* v_declName_299_; lean_object* v_us_300_; lean_object* v_getEnv_301_; lean_object* v___f_302_; lean_object* v___x_303_; 
v_toBind_298_ = lean_ctor_get(v_inst_293_, 1);
lean_inc(v_toBind_298_);
lean_dec_ref(v_inst_293_);
v_declName_299_ = lean_ctor_get(v_e_295_, 0);
lean_inc(v_declName_299_);
v_us_300_ = lean_ctor_get(v_e_295_, 1);
lean_inc(v_us_300_);
lean_dec_ref_known(v_e_295_, 2);
v_getEnv_301_ = lean_ctor_get(v_inst_294_, 0);
lean_inc(v_getEnv_301_);
lean_dec_ref(v_inst_294_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_matchConstInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_302_, 0, v_declName_299_);
lean_closure_set(v___f_302_, 1, v_failK_296_);
lean_closure_set(v___f_302_, 2, v_k_297_);
lean_closure_set(v___f_302_, 3, v_us_300_);
v___x_303_ = lean_apply_4(v_toBind_298_, lean_box(0), lean_box(0), v_getEnv_301_, v___f_302_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_k_297_);
lean_dec_ref(v_e_295_);
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_failK_296_, v___x_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg___lam__0(lean_object* v_declName_306_, lean_object* v_failK_307_, lean_object* v_k_308_, lean_object* v_us_309_, lean_object* v_____do__lift_310_){
_start:
{
uint8_t v___x_311_; lean_object* v___x_312_; 
v___x_311_ = 0;
v___x_312_ = l_Lean_Environment_find_x3f(v_____do__lift_310_, v_declName_306_, v___x_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_us_309_);
lean_dec(v_k_308_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_apply_1(v_failK_307_, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v_val_315_; 
v_val_315_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___x_312_, 1);
if (lean_obj_tag(v_val_315_) == 6)
{
lean_object* v_val_316_; lean_object* v___x_317_; 
lean_dec(v_failK_307_);
v_val_316_ = lean_ctor_get(v_val_315_, 0);
lean_inc_ref(v_val_316_);
lean_dec_ref_known(v_val_315_, 1);
v___x_317_ = lean_apply_2(v_k_308_, v_val_316_, v_us_309_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_val_315_);
lean_dec(v_us_309_);
lean_dec(v_k_308_);
v___x_318_ = lean_box(0);
v___x_319_ = lean_apply_1(v_failK_307_, v___x_318_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg(lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_e_322_, lean_object* v_failK_323_, lean_object* v_k_324_){
_start:
{
if (lean_obj_tag(v_e_322_) == 4)
{
lean_object* v_toBind_325_; lean_object* v_declName_326_; lean_object* v_us_327_; lean_object* v_getEnv_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
v_toBind_325_ = lean_ctor_get(v_inst_320_, 1);
lean_inc(v_toBind_325_);
lean_dec_ref(v_inst_320_);
v_declName_326_ = lean_ctor_get(v_e_322_, 0);
lean_inc(v_declName_326_);
v_us_327_ = lean_ctor_get(v_e_322_, 1);
lean_inc(v_us_327_);
lean_dec_ref_known(v_e_322_, 2);
v_getEnv_328_ = lean_ctor_get(v_inst_321_, 0);
lean_inc(v_getEnv_328_);
lean_dec_ref(v_inst_321_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_matchConstCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_329_, 0, v_declName_326_);
lean_closure_set(v___f_329_, 1, v_failK_323_);
lean_closure_set(v___f_329_, 2, v_k_324_);
lean_closure_set(v___f_329_, 3, v_us_327_);
v___x_330_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v_getEnv_328_, v___f_329_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_k_324_);
lean_dec_ref(v_e_322_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_inst_320_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_apply_1(v_failK_323_, v___x_331_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object* v_m_333_, lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_e_337_, lean_object* v_failK_338_, lean_object* v_k_339_){
_start:
{
if (lean_obj_tag(v_e_337_) == 4)
{
lean_object* v_toBind_340_; lean_object* v_declName_341_; lean_object* v_us_342_; lean_object* v_getEnv_343_; lean_object* v___f_344_; lean_object* v___x_345_; 
v_toBind_340_ = lean_ctor_get(v_inst_335_, 1);
lean_inc(v_toBind_340_);
lean_dec_ref(v_inst_335_);
v_declName_341_ = lean_ctor_get(v_e_337_, 0);
lean_inc(v_declName_341_);
v_us_342_ = lean_ctor_get(v_e_337_, 1);
lean_inc(v_us_342_);
lean_dec_ref_known(v_e_337_, 2);
v_getEnv_343_ = lean_ctor_get(v_inst_336_, 0);
lean_inc(v_getEnv_343_);
lean_dec_ref(v_inst_336_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_matchConstCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_344_, 0, v_declName_341_);
lean_closure_set(v___f_344_, 1, v_failK_338_);
lean_closure_set(v___f_344_, 2, v_k_339_);
lean_closure_set(v___f_344_, 3, v_us_342_);
v___x_345_ = lean_apply_4(v_toBind_340_, lean_box(0), lean_box(0), v_getEnv_343_, v___f_344_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_k_339_);
lean_dec_ref(v_e_337_);
lean_dec_ref(v_inst_336_);
lean_dec_ref(v_inst_335_);
v___x_346_ = lean_box(0);
v___x_347_ = lean_apply_1(v_failK_338_, v___x_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg___lam__0(lean_object* v_declName_348_, lean_object* v_failK_349_, lean_object* v_k_350_, lean_object* v_us_351_, lean_object* v_____do__lift_352_){
_start:
{
uint8_t v___x_353_; lean_object* v___x_354_; 
v___x_353_ = 0;
v___x_354_ = l_Lean_Environment_find_x3f(v_____do__lift_352_, v_declName_348_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_us_351_);
lean_dec(v_k_350_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_apply_1(v_failK_349_, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v_val_357_; 
v_val_357_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_354_, 1);
if (lean_obj_tag(v_val_357_) == 7)
{
lean_object* v_val_358_; lean_object* v___x_359_; 
lean_dec(v_failK_349_);
v_val_358_ = lean_ctor_get(v_val_357_, 0);
lean_inc_ref(v_val_358_);
lean_dec_ref_known(v_val_357_, 1);
v___x_359_ = lean_apply_2(v_k_350_, v_val_358_, v_us_351_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_val_357_);
lean_dec(v_us_351_);
lean_dec(v_k_350_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_apply_1(v_failK_349_, v___x_360_);
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg(lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_e_364_, lean_object* v_failK_365_, lean_object* v_k_366_){
_start:
{
if (lean_obj_tag(v_e_364_) == 4)
{
lean_object* v_toBind_367_; lean_object* v_declName_368_; lean_object* v_us_369_; lean_object* v_getEnv_370_; lean_object* v___f_371_; lean_object* v___x_372_; 
v_toBind_367_ = lean_ctor_get(v_inst_362_, 1);
lean_inc(v_toBind_367_);
lean_dec_ref(v_inst_362_);
v_declName_368_ = lean_ctor_get(v_e_364_, 0);
lean_inc(v_declName_368_);
v_us_369_ = lean_ctor_get(v_e_364_, 1);
lean_inc(v_us_369_);
lean_dec_ref_known(v_e_364_, 2);
v_getEnv_370_ = lean_ctor_get(v_inst_363_, 0);
lean_inc(v_getEnv_370_);
lean_dec_ref(v_inst_363_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_matchConstRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_371_, 0, v_declName_368_);
lean_closure_set(v___f_371_, 1, v_failK_365_);
lean_closure_set(v___f_371_, 2, v_k_366_);
lean_closure_set(v___f_371_, 3, v_us_369_);
v___x_372_ = lean_apply_4(v_toBind_367_, lean_box(0), lean_box(0), v_getEnv_370_, v___f_371_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_k_366_);
lean_dec_ref(v_e_364_);
lean_dec_ref(v_inst_363_);
lean_dec_ref(v_inst_362_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_apply_1(v_failK_365_, v___x_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object* v_m_375_, lean_object* v_00_u03b1_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_e_379_, lean_object* v_failK_380_, lean_object* v_k_381_){
_start:
{
if (lean_obj_tag(v_e_379_) == 4)
{
lean_object* v_toBind_382_; lean_object* v_declName_383_; lean_object* v_us_384_; lean_object* v_getEnv_385_; lean_object* v___f_386_; lean_object* v___x_387_; 
v_toBind_382_ = lean_ctor_get(v_inst_377_, 1);
lean_inc(v_toBind_382_);
lean_dec_ref(v_inst_377_);
v_declName_383_ = lean_ctor_get(v_e_379_, 0);
lean_inc(v_declName_383_);
v_us_384_ = lean_ctor_get(v_e_379_, 1);
lean_inc(v_us_384_);
lean_dec_ref_known(v_e_379_, 2);
v_getEnv_385_ = lean_ctor_get(v_inst_378_, 0);
lean_inc(v_getEnv_385_);
lean_dec_ref(v_inst_378_);
v___f_386_ = lean_alloc_closure((void*)(l_Lean_matchConstRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_386_, 0, v_declName_383_);
lean_closure_set(v___f_386_, 1, v_failK_380_);
lean_closure_set(v___f_386_, 2, v_k_381_);
lean_closure_set(v___f_386_, 3, v_us_384_);
v___x_387_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v_getEnv_385_, v___f_386_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_k_381_);
lean_dec_ref(v_e_379_);
lean_dec_ref(v_inst_378_);
lean_dec_ref(v_inst_377_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_apply_1(v_failK_380_, v___x_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0(lean_object* v_constName_390_, uint8_t v_skipRealize_391_, lean_object* v_toPure_392_, lean_object* v_____do__lift_393_){
_start:
{
uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = l_Lean_Environment_contains(v_____do__lift_393_, v_constName_390_, v_skipRealize_391_);
v___x_395_ = lean_box(v___x_394_);
v___x_396_ = lean_apply_2(v_toPure_392_, lean_box(0), v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0___boxed(lean_object* v_constName_397_, lean_object* v_skipRealize_398_, lean_object* v_toPure_399_, lean_object* v_____do__lift_400_){
_start:
{
uint8_t v_skipRealize_boxed_401_; lean_object* v_res_402_; 
v_skipRealize_boxed_401_ = lean_unbox(v_skipRealize_398_);
v_res_402_ = l_Lean_hasConst___redArg___lam__0(v_constName_397_, v_skipRealize_boxed_401_, v_toPure_399_, v_____do__lift_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg(lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_constName_405_, uint8_t v_skipRealize_406_){
_start:
{
lean_object* v_toApplicative_407_; lean_object* v_toBind_408_; lean_object* v_getEnv_409_; lean_object* v_toPure_410_; lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___x_413_; 
v_toApplicative_407_ = lean_ctor_get(v_inst_403_, 0);
lean_inc_ref(v_toApplicative_407_);
v_toBind_408_ = lean_ctor_get(v_inst_403_, 1);
lean_inc(v_toBind_408_);
lean_dec_ref(v_inst_403_);
v_getEnv_409_ = lean_ctor_get(v_inst_404_, 0);
lean_inc(v_getEnv_409_);
lean_dec_ref(v_inst_404_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_407_, 1);
lean_inc(v_toPure_410_);
lean_dec_ref(v_toApplicative_407_);
v___x_411_ = lean_box(v_skipRealize_406_);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_hasConst___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_412_, 0, v_constName_405_);
lean_closure_set(v___f_412_, 1, v___x_411_);
lean_closure_set(v___f_412_, 2, v_toPure_410_);
v___x_413_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v_getEnv_409_, v___f_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___boxed(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_constName_416_, lean_object* v_skipRealize_417_){
_start:
{
uint8_t v_skipRealize_boxed_418_; lean_object* v_res_419_; 
v_skipRealize_boxed_418_ = lean_unbox(v_skipRealize_417_);
v_res_419_ = l_Lean_hasConst___redArg(v_inst_414_, v_inst_415_, v_constName_416_, v_skipRealize_boxed_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object* v_m_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_constName_423_, uint8_t v_skipRealize_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_hasConst___redArg(v_inst_421_, v_inst_422_, v_constName_423_, v_skipRealize_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___boxed(lean_object* v_m_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_constName_429_, lean_object* v_skipRealize_430_){
_start:
{
uint8_t v_skipRealize_boxed_431_; lean_object* v_res_432_; 
v_skipRealize_boxed_431_ = lean_unbox(v_skipRealize_430_);
v_res_432_ = l_Lean_hasConst(v_m_426_, v_inst_427_, v_inst_428_, v_constName_429_, v_skipRealize_boxed_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg___lam__0(lean_object* v_constName_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_toPure_437_, lean_object* v_____do__lift_438_){
_start:
{
uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_439_ = 0;
lean_inc(v_constName_433_);
v___x_440_ = l_Lean_Environment_find_x3f(v_____do__lift_438_, v_constName_433_, v___x_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v___x_441_; 
lean_dec(v_toPure_437_);
v___x_441_ = l_Lean_throwUnknownConstant___redArg(v_inst_434_, v_inst_435_, v_inst_436_, v_constName_433_);
return v___x_441_;
}
else
{
lean_object* v_val_442_; lean_object* v___x_443_; 
lean_dec_ref(v_inst_436_);
lean_dec_ref(v_inst_435_);
lean_dec_ref(v_inst_434_);
lean_dec(v_constName_433_);
v_val_442_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v___x_440_, 1);
v___x_443_ = lean_apply_2(v_toPure_437_, lean_box(0), v_val_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg(lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_constName_447_){
_start:
{
lean_object* v_toApplicative_448_; lean_object* v_toBind_449_; lean_object* v_getEnv_450_; lean_object* v_toPure_451_; lean_object* v___f_452_; lean_object* v___x_453_; 
v_toApplicative_448_ = lean_ctor_get(v_inst_444_, 0);
v_toBind_449_ = lean_ctor_get(v_inst_444_, 1);
lean_inc(v_toBind_449_);
v_getEnv_450_ = lean_ctor_get(v_inst_445_, 0);
lean_inc(v_getEnv_450_);
v_toPure_451_ = lean_ctor_get(v_toApplicative_448_, 1);
lean_inc(v_toPure_451_);
v___f_452_ = lean_alloc_closure((void*)(l_Lean_getConstInfo___redArg___lam__0), 6, 5);
lean_closure_set(v___f_452_, 0, v_constName_447_);
lean_closure_set(v___f_452_, 1, v_inst_444_);
lean_closure_set(v___f_452_, 2, v_inst_445_);
lean_closure_set(v___f_452_, 3, v_inst_446_);
lean_closure_set(v___f_452_, 4, v_toPure_451_);
v___x_453_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v_getEnv_450_, v___f_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_constName_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_getConstInfo___redArg(v_inst_455_, v_inst_456_, v_inst_457_, v_constName_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg___lam__0(lean_object* v_constName_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_toPure_464_, lean_object* v_____do__lift_465_){
_start:
{
uint8_t v___x_466_; lean_object* v___x_467_; 
v___x_466_ = 0;
lean_inc(v_constName_460_);
v___x_467_ = l_Lean_Environment_findConstVal_x3f(v_____do__lift_465_, v_constName_460_, v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; 
lean_dec(v_toPure_464_);
v___x_468_ = l_Lean_throwUnknownConstant___redArg(v_inst_461_, v_inst_462_, v_inst_463_, v_constName_460_);
return v___x_468_;
}
else
{
lean_object* v_val_469_; lean_object* v___x_470_; 
lean_dec_ref(v_inst_463_);
lean_dec_ref(v_inst_462_);
lean_dec_ref(v_inst_461_);
lean_dec(v_constName_460_);
v_val_469_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_467_, 1);
v___x_470_ = lean_apply_2(v_toPure_464_, lean_box(0), v_val_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg(lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_constName_474_){
_start:
{
lean_object* v_toApplicative_475_; lean_object* v_toBind_476_; lean_object* v_getEnv_477_; lean_object* v_toPure_478_; lean_object* v___f_479_; lean_object* v___x_480_; 
v_toApplicative_475_ = lean_ctor_get(v_inst_471_, 0);
v_toBind_476_ = lean_ctor_get(v_inst_471_, 1);
lean_inc(v_toBind_476_);
v_getEnv_477_ = lean_ctor_get(v_inst_472_, 0);
lean_inc(v_getEnv_477_);
v_toPure_478_ = lean_ctor_get(v_toApplicative_475_, 1);
lean_inc(v_toPure_478_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_getConstVal___redArg___lam__0), 6, 5);
lean_closure_set(v___f_479_, 0, v_constName_474_);
lean_closure_set(v___f_479_, 1, v_inst_471_);
lean_closure_set(v___f_479_, 2, v_inst_472_);
lean_closure_set(v___f_479_, 3, v_inst_473_);
lean_closure_set(v___f_479_, 4, v_toPure_478_);
v___x_480_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v_getEnv_477_, v___f_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal(lean_object* v_m_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_constName_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_getConstVal___redArg(v_inst_482_, v_inst_483_, v_inst_484_, v_constName_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0(lean_object* v_constName_487_, uint8_t v_skipRealize_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_toPure_492_, lean_object* v_____do__lift_493_){
_start:
{
lean_object* v___x_494_; 
lean_inc(v_constName_487_);
v___x_494_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_493_, v_constName_487_, v_skipRealize_488_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_dec(v_toPure_492_);
v___x_495_ = l_Lean_throwUnknownConstant___redArg(v_inst_489_, v_inst_490_, v_inst_491_, v_constName_487_);
return v___x_495_;
}
else
{
lean_object* v_val_496_; lean_object* v___x_497_; 
lean_dec_ref(v_inst_491_);
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec(v_constName_487_);
v_val_496_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v___x_494_, 1);
v___x_497_ = lean_apply_2(v_toPure_492_, lean_box(0), v_val_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(lean_object* v_constName_498_, lean_object* v_skipRealize_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_toPure_503_, lean_object* v_____do__lift_504_){
_start:
{
uint8_t v_skipRealize_boxed_505_; lean_object* v_res_506_; 
v_skipRealize_boxed_505_ = lean_unbox(v_skipRealize_499_);
v_res_506_ = l_Lean_getAsyncConstInfo___redArg___lam__0(v_constName_498_, v_skipRealize_boxed_505_, v_inst_500_, v_inst_501_, v_inst_502_, v_toPure_503_, v_____do__lift_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg(lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_constName_510_, uint8_t v_skipRealize_511_){
_start:
{
lean_object* v_toApplicative_512_; lean_object* v_toBind_513_; lean_object* v_getEnv_514_; lean_object* v_toPure_515_; lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
v_toApplicative_512_ = lean_ctor_get(v_inst_507_, 0);
v_toBind_513_ = lean_ctor_get(v_inst_507_, 1);
lean_inc(v_toBind_513_);
v_getEnv_514_ = lean_ctor_get(v_inst_508_, 0);
lean_inc(v_getEnv_514_);
v_toPure_515_ = lean_ctor_get(v_toApplicative_512_, 1);
lean_inc(v_toPure_515_);
v___x_516_ = lean_box(v_skipRealize_511_);
v___f_517_ = lean_alloc_closure((void*)(l_Lean_getAsyncConstInfo___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_517_, 0, v_constName_510_);
lean_closure_set(v___f_517_, 1, v___x_516_);
lean_closure_set(v___f_517_, 2, v_inst_507_);
lean_closure_set(v___f_517_, 3, v_inst_508_);
lean_closure_set(v___f_517_, 4, v_inst_509_);
lean_closure_set(v___f_517_, 5, v_toPure_515_);
v___x_518_ = lean_apply_4(v_toBind_513_, lean_box(0), lean_box(0), v_getEnv_514_, v___f_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___boxed(lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_constName_522_, lean_object* v_skipRealize_523_){
_start:
{
uint8_t v_skipRealize_boxed_524_; lean_object* v_res_525_; 
v_skipRealize_boxed_524_ = lean_unbox(v_skipRealize_523_);
v_res_525_ = l_Lean_getAsyncConstInfo___redArg(v_inst_519_, v_inst_520_, v_inst_521_, v_constName_522_, v_skipRealize_boxed_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo(lean_object* v_m_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_constName_530_, uint8_t v_skipRealize_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_getAsyncConstInfo___redArg(v_inst_527_, v_inst_528_, v_inst_529_, v_constName_530_, v_skipRealize_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___boxed(lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_constName_537_, lean_object* v_skipRealize_538_){
_start:
{
uint8_t v_skipRealize_boxed_539_; lean_object* v_res_540_; 
v_skipRealize_boxed_539_ = lean_unbox(v_skipRealize_538_);
v_res_540_ = l_Lean_getAsyncConstInfo(v_m_533_, v_inst_534_, v_inst_535_, v_inst_536_, v_constName_537_, v_skipRealize_boxed_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isInductiveCore_x3f_spec__0(lean_object* v_msg_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(0);
v___x_543_ = lean_panic_fn_borrowed(v___x_542_, v_msg_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_isInductiveCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_547_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_548_ = lean_unsigned_to_nat(11u);
v___x_549_ = lean_unsigned_to_nat(105u);
v___x_550_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__1));
v___x_551_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_552_ = l_mkPanicMessageWithDecl(v___x_551_, v___x_550_, v___x_549_, v___x_548_, v___x_547_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductiveCore_x3f(lean_object* v_env_553_, lean_object* v_declName_554_){
_start:
{
uint8_t v___x_555_; lean_object* v___x_556_; 
v___x_555_ = 0;
v___x_556_ = l_Lean_Environment_findAsync_x3f(v_env_553_, v_declName_554_, v___x_555_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_570_; 
v_val_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_570_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v_kind_561_; 
v_kind_561_ = lean_ctor_get_uint8(v_val_557_, sizeof(void*)*3);
if (v_kind_561_ == 5)
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_557_);
if (lean_obj_tag(v___x_562_) == 5)
{
lean_object* v_val_563_; lean_object* v___x_565_; 
v_val_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_val_563_);
lean_dec_ref_known(v___x_562_, 1);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v_val_563_);
v___x_565_ = v___x_559_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_val_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v___x_562_);
lean_del_object(v___x_559_);
v___x_567_ = lean_obj_once(&l_Lean_isInductiveCore_x3f___closed__3, &l_Lean_isInductiveCore_x3f___closed__3_once, _init_l_Lean_isInductiveCore_x3f___closed__3);
v___x_568_ = l_panic___at___00Lean_isInductiveCore_x3f_spec__0(v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; 
lean_del_object(v___x_559_);
lean_dec(v_val_557_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
}
else
{
lean_object* v___x_571_; 
lean_dec(v___x_556_);
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg___lam__0(lean_object* v_declName_572_, lean_object* v_toPure_573_, lean_object* v_____do__lift_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = l_Lean_isInductiveCore_x3f(v_____do__lift_574_, v_declName_572_);
v___x_576_ = lean_apply_2(v_toPure_573_, lean_box(0), v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg(lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_declName_579_){
_start:
{
lean_object* v_toApplicative_580_; lean_object* v_toBind_581_; lean_object* v_getEnv_582_; lean_object* v_toPure_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_toApplicative_580_ = lean_ctor_get(v_inst_577_, 0);
lean_inc_ref(v_toApplicative_580_);
v_toBind_581_ = lean_ctor_get(v_inst_577_, 1);
lean_inc(v_toBind_581_);
lean_dec_ref(v_inst_577_);
v_getEnv_582_ = lean_ctor_get(v_inst_578_, 0);
lean_inc(v_getEnv_582_);
lean_dec_ref(v_inst_578_);
v_toPure_583_ = lean_ctor_get(v_toApplicative_580_, 1);
lean_inc(v_toPure_583_);
lean_dec_ref(v_toApplicative_580_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_isInductive_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_584_, 0, v_declName_579_);
lean_closure_set(v___f_584_, 1, v_toPure_583_);
v___x_585_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v_getEnv_582_, v___f_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f(lean_object* v_m_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_declName_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_isInductive_x3f___redArg(v_inst_587_, v_inst_588_, v_declName_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_592_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_593_ = lean_unsigned_to_nat(11u);
v___x_594_ = lean_unsigned_to_nat(115u);
v___x_595_ = ((lean_object*)(l_Lean_isDefn_x3f___redArg___lam__0___closed__0));
v___x_596_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_597_ = l_mkPanicMessageWithDecl(v___x_596_, v___x_595_, v___x_594_, v___x_593_, v___x_592_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg___lam__0(lean_object* v_toPure_598_, lean_object* v_constName_599_, lean_object* v___x_600_, lean_object* v_____do__lift_601_){
_start:
{
uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_605_ = 0;
v___x_606_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_601_, v_constName_599_, v___x_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_620_; 
v_val_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_620_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_620_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_620_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint8_t v_kind_611_; 
v_kind_611_ = lean_ctor_get_uint8(v_val_607_, sizeof(void*)*3);
if (v_kind_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_607_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v_val_613_; lean_object* v___x_615_; 
v_val_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_ref(v_val_613_);
lean_dec_ref_known(v___x_612_, 1);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_val_613_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_val_613_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_apply_2(v_toPure_598_, lean_box(0), v___x_615_);
return v___x_616_;
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref(v___x_612_);
lean_del_object(v___x_609_);
lean_dec(v_toPure_598_);
v___x_618_ = lean_obj_once(&l_Lean_isDefn_x3f___redArg___lam__0___closed__1, &l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1);
v___x_619_ = l_panic___redArg(v___x_600_, v___x_618_);
return v___x_619_;
}
}
else
{
lean_del_object(v___x_609_);
lean_dec(v_val_607_);
goto v___jp_602_;
}
}
}
else
{
lean_dec(v___x_606_);
goto v___jp_602_;
}
v___jp_602_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_apply_2(v_toPure_598_, lean_box(0), v___x_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg___lam__0___boxed(lean_object* v_toPure_621_, lean_object* v_constName_622_, lean_object* v___x_623_, lean_object* v_____do__lift_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_isDefn_x3f___redArg___lam__0(v_toPure_621_, v_constName_622_, v___x_623_, v_____do__lift_624_);
lean_dec(v___x_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg(lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_constName_628_){
_start:
{
lean_object* v_toApplicative_629_; lean_object* v_toBind_630_; lean_object* v_getEnv_631_; lean_object* v_toPure_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v_toApplicative_629_ = lean_ctor_get(v_inst_626_, 0);
v_toBind_630_ = lean_ctor_get(v_inst_626_, 1);
lean_inc(v_toBind_630_);
v_getEnv_631_ = lean_ctor_get(v_inst_627_, 0);
lean_inc(v_getEnv_631_);
lean_dec_ref(v_inst_627_);
v_toPure_632_ = lean_ctor_get(v_toApplicative_629_, 1);
lean_inc(v_toPure_632_);
v___x_633_ = lean_box(0);
v___x_634_ = l_instInhabitedOfMonad___redArg(v_inst_626_, v___x_633_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_isDefn_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_635_, 0, v_toPure_632_);
lean_closure_set(v___f_635_, 1, v_constName_628_);
lean_closure_set(v___f_635_, 2, v___x_634_);
v___x_636_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v_getEnv_631_, v___f_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f(lean_object* v_m_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_constName_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_isDefn_x3f___redArg(v_inst_638_, v_inst_639_, v_constName_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_643_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_644_ = lean_unsigned_to_nat(11u);
v___x_645_ = lean_unsigned_to_nat(122u);
v___x_646_ = ((lean_object*)(l_Lean_isCtor_x3f___redArg___lam__0___closed__0));
v___x_647_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_648_ = l_mkPanicMessageWithDecl(v___x_647_, v___x_646_, v___x_645_, v___x_644_, v___x_643_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0(lean_object* v_toPure_649_, lean_object* v_constName_650_, lean_object* v___x_651_, lean_object* v_____do__lift_652_){
_start:
{
uint8_t v___x_656_; lean_object* v___x_657_; 
v___x_656_ = 0;
v___x_657_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_652_, v_constName_650_, v___x_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_671_; 
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_671_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
uint8_t v_kind_662_; 
v_kind_662_ = lean_ctor_get_uint8(v_val_658_, sizeof(void*)*3);
if (v_kind_662_ == 6)
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_658_);
if (lean_obj_tag(v___x_663_) == 6)
{
lean_object* v_val_664_; lean_object* v___x_666_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc_ref(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_val_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_val_664_);
v___x_666_ = v_reuseFailAlloc_668_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; 
v___x_667_ = lean_apply_2(v_toPure_649_, lean_box(0), v___x_666_);
return v___x_667_;
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref(v___x_663_);
lean_del_object(v___x_660_);
lean_dec(v_toPure_649_);
v___x_669_ = lean_obj_once(&l_Lean_isCtor_x3f___redArg___lam__0___closed__1, &l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1);
v___x_670_ = l_panic___redArg(v___x_651_, v___x_669_);
return v___x_670_;
}
}
else
{
lean_del_object(v___x_660_);
lean_dec(v_val_658_);
goto v___jp_653_;
}
}
}
else
{
lean_dec(v___x_657_);
goto v___jp_653_;
}
v___jp_653_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(0);
v___x_655_ = lean_apply_2(v_toPure_649_, lean_box(0), v___x_654_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0___boxed(lean_object* v_toPure_672_, lean_object* v_constName_673_, lean_object* v___x_674_, lean_object* v_____do__lift_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_isCtor_x3f___redArg___lam__0(v_toPure_672_, v_constName_673_, v___x_674_, v_____do__lift_675_);
lean_dec(v___x_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg(lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_constName_679_){
_start:
{
lean_object* v_toApplicative_680_; lean_object* v_toBind_681_; lean_object* v_getEnv_682_; lean_object* v_toPure_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; 
v_toApplicative_680_ = lean_ctor_get(v_inst_677_, 0);
v_toBind_681_ = lean_ctor_get(v_inst_677_, 1);
lean_inc(v_toBind_681_);
v_getEnv_682_ = lean_ctor_get(v_inst_678_, 0);
lean_inc(v_getEnv_682_);
lean_dec_ref(v_inst_678_);
v_toPure_683_ = lean_ctor_get(v_toApplicative_680_, 1);
lean_inc(v_toPure_683_);
v___x_684_ = lean_box(0);
v___x_685_ = l_instInhabitedOfMonad___redArg(v_inst_677_, v___x_684_);
v___f_686_ = lean_alloc_closure((void*)(l_Lean_isCtor_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_686_, 0, v_toPure_683_);
lean_closure_set(v___f_686_, 1, v_constName_679_);
lean_closure_set(v___f_686_, 2, v___x_685_);
v___x_687_ = lean_apply_4(v_toBind_681_, lean_box(0), lean_box(0), v_getEnv_682_, v___f_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f(lean_object* v_m_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_constName_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_isCtor_x3f___redArg(v_inst_689_, v_inst_690_, v_constName_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_695_ = lean_unsigned_to_nat(11u);
v___x_696_ = lean_unsigned_to_nat(129u);
v___x_697_ = ((lean_object*)(l_Lean_isRec_x3f___redArg___lam__0___closed__0));
v___x_698_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0(lean_object* v_toPure_700_, lean_object* v_constName_701_, lean_object* v___x_702_, lean_object* v_____do__lift_703_){
_start:
{
uint8_t v___x_707_; lean_object* v___x_708_; 
v___x_707_ = 0;
v___x_708_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_703_, v_constName_701_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_722_; 
v_val_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_722_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_722_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_722_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v_kind_713_; 
v_kind_713_ = lean_ctor_get_uint8(v_val_709_, sizeof(void*)*3);
if (v_kind_713_ == 7)
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_709_);
if (lean_obj_tag(v___x_714_) == 7)
{
lean_object* v_val_715_; lean_object* v___x_717_; 
v_val_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc_ref(v_val_715_);
lean_dec_ref_known(v___x_714_, 1);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_val_715_);
v___x_717_ = v___x_711_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_val_715_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; 
v___x_718_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_717_);
return v___x_718_;
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec_ref(v___x_714_);
lean_del_object(v___x_711_);
lean_dec(v_toPure_700_);
v___x_720_ = lean_obj_once(&l_Lean_isRec_x3f___redArg___lam__0___closed__1, &l_Lean_isRec_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1);
v___x_721_ = l_panic___redArg(v___x_702_, v___x_720_);
return v___x_721_;
}
}
else
{
lean_del_object(v___x_711_);
lean_dec(v_val_709_);
goto v___jp_704_;
}
}
}
else
{
lean_dec(v___x_708_);
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_705_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0___boxed(lean_object* v_toPure_723_, lean_object* v_constName_724_, lean_object* v___x_725_, lean_object* v_____do__lift_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_isRec_x3f___redArg___lam__0(v_toPure_723_, v_constName_724_, v___x_725_, v_____do__lift_726_);
lean_dec(v___x_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg(lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_constName_730_){
_start:
{
lean_object* v_toApplicative_731_; lean_object* v_toBind_732_; lean_object* v_getEnv_733_; lean_object* v_toPure_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; 
v_toApplicative_731_ = lean_ctor_get(v_inst_728_, 0);
v_toBind_732_ = lean_ctor_get(v_inst_728_, 1);
lean_inc(v_toBind_732_);
v_getEnv_733_ = lean_ctor_get(v_inst_729_, 0);
lean_inc(v_getEnv_733_);
lean_dec_ref(v_inst_729_);
v_toPure_734_ = lean_ctor_get(v_toApplicative_731_, 1);
lean_inc(v_toPure_734_);
v___x_735_ = lean_box(0);
v___x_736_ = l_instInhabitedOfMonad___redArg(v_inst_728_, v___x_735_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_isRec_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_737_, 0, v_toPure_734_);
lean_closure_set(v___f_737_, 1, v_constName_730_);
lean_closure_set(v___f_737_, 2, v___x_736_);
v___x_738_ = lean_apply_4(v_toBind_732_, lean_box(0), lean_box(0), v_getEnv_733_, v___f_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f(lean_object* v_m_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_constName_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_isRec_x3f___redArg(v_inst_740_, v_inst_741_, v_constName_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0(lean_object* v_constName_745_, lean_object* v_toPure_746_, lean_object* v_info_747_){
_start:
{
lean_object* v_levelParams_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_levelParams_748_ = lean_ctor_get(v_info_747_, 1);
lean_inc(v_levelParams_748_);
lean_dec_ref(v_info_747_);
v___x_749_ = ((lean_object*)(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0));
v___x_750_ = lean_box(0);
v___x_751_ = l_List_mapTR_loop___redArg(v___x_749_, v_levelParams_748_, v___x_750_);
v___x_752_ = l_Lean_mkConst(v_constName_745_, v___x_751_);
v___x_753_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_constName_757_){
_start:
{
lean_object* v_toApplicative_758_; lean_object* v_toBind_759_; lean_object* v_toPure_760_; lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___x_763_; 
v_toApplicative_758_ = lean_ctor_get(v_inst_754_, 0);
v_toBind_759_ = lean_ctor_get(v_inst_754_, 1);
lean_inc(v_toBind_759_);
v_toPure_760_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_inc(v_toPure_760_);
lean_inc(v_constName_757_);
v___x_761_ = l_Lean_getConstVal___redArg(v_inst_754_, v_inst_755_, v_inst_756_, v_constName_757_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_mkConstWithLevelParams___redArg___lam__0), 3, 2);
lean_closure_set(v___f_762_, 0, v_constName_757_);
lean_closure_set(v___f_762_, 1, v_toPure_760_);
v___x_763_ = lean_apply_4(v_toBind_759_, lean_box(0), lean_box(0), v___x_761_, v___f_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object* v_m_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_constName_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_765_, v_inst_766_, v_inst_767_, v_constName_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg___lam__0(lean_object* v_constName_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_toPure_779_, lean_object* v_____do__lift_780_){
_start:
{
if (lean_obj_tag(v_____do__lift_780_) == 0)
{
lean_object* v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_toPure_779_);
v___x_781_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_782_ = 0;
v___x_783_ = l_Lean_MessageData_ofConstName(v_constName_776_, v___x_782_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_781_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__3, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_throwError___redArg(v_inst_777_, v_inst_778_, v___x_786_);
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_dec_ref(v_inst_778_);
lean_dec_ref(v_inst_777_);
lean_dec(v_constName_776_);
v_val_788_ = lean_ctor_get(v_____do__lift_780_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_____do__lift_780_, 1);
v___x_789_ = lean_apply_2(v_toPure_779_, lean_box(0), v_val_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_constName_793_){
_start:
{
lean_object* v_toApplicative_794_; lean_object* v_toBind_795_; lean_object* v_getEnv_796_; lean_object* v_toPure_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_toApplicative_794_ = lean_ctor_get(v_inst_790_, 0);
v_toBind_795_ = lean_ctor_get(v_inst_790_, 1);
lean_inc_n(v_toBind_795_, 2);
v_getEnv_796_ = lean_ctor_get(v_inst_791_, 0);
lean_inc(v_getEnv_796_);
lean_dec_ref(v_inst_791_);
v_toPure_797_ = lean_ctor_get(v_toApplicative_794_, 1);
lean_inc_n(v_toPure_797_, 2);
v___x_798_ = lean_box(0);
lean_inc_ref(v_inst_790_);
lean_inc(v_constName_793_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_getConstInfoDefn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_799_, 0, v_constName_793_);
lean_closure_set(v___f_799_, 1, v_inst_790_);
lean_closure_set(v___f_799_, 2, v_inst_792_);
lean_closure_set(v___f_799_, 3, v_toPure_797_);
v___x_800_ = l_instInhabitedOfMonad___redArg(v_inst_790_, v___x_798_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_isDefn_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_801_, 0, v_toPure_797_);
lean_closure_set(v___f_801_, 1, v_constName_793_);
lean_closure_set(v___f_801_, 2, v___x_800_);
v___x_802_ = lean_apply_4(v_toBind_795_, lean_box(0), lean_box(0), v_getEnv_796_, v___f_801_);
v___x_803_ = lean_apply_4(v_toBind_795_, lean_box(0), lean_box(0), v___x_802_, v___f_799_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object* v_m_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_constName_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_getConstInfoDefn___redArg(v_inst_805_, v_inst_806_, v_inst_807_, v_constName_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__0(lean_object* v_constName_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_toPure_816_, lean_object* v_____do__lift_817_){
_start:
{
if (lean_obj_tag(v_____do__lift_817_) == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_toPure_816_);
v___x_818_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_819_ = 0;
v___x_820_ = l_Lean_MessageData_ofConstName(v_constName_813_, v___x_819_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_818_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_getConstInfoInduct___redArg___lam__0___closed__1, &l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_throwError___redArg(v_inst_814_, v_inst_815_, v___x_823_);
return v___x_824_;
}
else
{
lean_object* v_val_825_; lean_object* v___x_826_; 
lean_dec_ref(v_inst_815_);
lean_dec_ref(v_inst_814_);
lean_dec(v_constName_813_);
v_val_825_ = lean_ctor_get(v_____do__lift_817_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v_____do__lift_817_, 1);
v___x_826_ = lean_apply_2(v_toPure_816_, lean_box(0), v_val_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__1(lean_object* v_constName_827_, lean_object* v_toPure_828_, lean_object* v_____do__lift_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = l_Lean_isInductiveCore_x3f(v_____do__lift_829_, v_constName_827_);
v___x_831_ = lean_apply_2(v_toPure_828_, lean_box(0), v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg(lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_constName_835_){
_start:
{
lean_object* v_toApplicative_836_; lean_object* v_toBind_837_; lean_object* v_getEnv_838_; lean_object* v_toPure_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_toApplicative_836_ = lean_ctor_get(v_inst_832_, 0);
v_toBind_837_ = lean_ctor_get(v_inst_832_, 1);
lean_inc_n(v_toBind_837_, 2);
v_getEnv_838_ = lean_ctor_get(v_inst_833_, 0);
lean_inc(v_getEnv_838_);
lean_dec_ref(v_inst_833_);
v_toPure_839_ = lean_ctor_get(v_toApplicative_836_, 1);
lean_inc_n(v_toPure_839_, 2);
lean_inc(v_constName_835_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_840_, 0, v_constName_835_);
lean_closure_set(v___f_840_, 1, v_inst_832_);
lean_closure_set(v___f_840_, 2, v_inst_834_);
lean_closure_set(v___f_840_, 3, v_toPure_839_);
v___f_841_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__1), 3, 2);
lean_closure_set(v___f_841_, 0, v_constName_835_);
lean_closure_set(v___f_841_, 1, v_toPure_839_);
v___x_842_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v_getEnv_838_, v___f_841_);
v___x_843_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v___x_842_, v___f_840_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object* v_m_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_constName_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_getConstInfoInduct___redArg(v_inst_845_, v_inst_846_, v_inst_847_, v_constName_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg___lam__0(lean_object* v_constName_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_toPure_856_, lean_object* v_____do__lift_857_){
_start:
{
if (lean_obj_tag(v_____do__lift_857_) == 0)
{
lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_toPure_856_);
v___x_858_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_859_ = 0;
v___x_860_ = l_Lean_MessageData_ofConstName(v_constName_853_, v___x_859_);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_858_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_obj_once(&l_Lean_getConstInfoCtor___redArg___lam__0___closed__1, &l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_throwError___redArg(v_inst_854_, v_inst_855_, v___x_863_);
return v___x_864_;
}
else
{
lean_object* v_val_865_; lean_object* v___x_866_; 
lean_dec_ref(v_inst_855_);
lean_dec_ref(v_inst_854_);
lean_dec(v_constName_853_);
v_val_865_ = lean_ctor_get(v_____do__lift_857_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_____do__lift_857_, 1);
v___x_866_ = lean_apply_2(v_toPure_856_, lean_box(0), v_val_865_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg(lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_constName_870_){
_start:
{
lean_object* v_toApplicative_871_; lean_object* v_toBind_872_; lean_object* v_getEnv_873_; lean_object* v_toPure_874_; lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_toApplicative_871_ = lean_ctor_get(v_inst_867_, 0);
v_toBind_872_ = lean_ctor_get(v_inst_867_, 1);
lean_inc_n(v_toBind_872_, 2);
v_getEnv_873_ = lean_ctor_get(v_inst_868_, 0);
lean_inc(v_getEnv_873_);
lean_dec_ref(v_inst_868_);
v_toPure_874_ = lean_ctor_get(v_toApplicative_871_, 1);
lean_inc_n(v_toPure_874_, 2);
v___x_875_ = lean_box(0);
lean_inc_ref(v_inst_867_);
lean_inc(v_constName_870_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_getConstInfoCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_876_, 0, v_constName_870_);
lean_closure_set(v___f_876_, 1, v_inst_867_);
lean_closure_set(v___f_876_, 2, v_inst_869_);
lean_closure_set(v___f_876_, 3, v_toPure_874_);
v___x_877_ = l_instInhabitedOfMonad___redArg(v_inst_867_, v___x_875_);
v___f_878_ = lean_alloc_closure((void*)(l_Lean_isCtor_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_878_, 0, v_toPure_874_);
lean_closure_set(v___f_878_, 1, v_constName_870_);
lean_closure_set(v___f_878_, 2, v___x_877_);
v___x_879_ = lean_apply_4(v_toBind_872_, lean_box(0), lean_box(0), v_getEnv_873_, v___f_878_);
v___x_880_ = lean_apply_4(v_toBind_872_, lean_box(0), lean_box(0), v___x_879_, v___f_876_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object* v_m_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_constName_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_getConstInfoCtor___redArg(v_inst_882_, v_inst_883_, v_inst_884_, v_constName_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_getConstInfoRec___redArg___lam__0___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg___lam__0(lean_object* v_constName_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_toPure_893_, lean_object* v_____do__lift_894_){
_start:
{
if (lean_obj_tag(v_____do__lift_894_) == 0)
{
lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_toPure_893_);
v___x_895_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_896_ = 0;
v___x_897_ = l_Lean_MessageData_ofConstName(v_constName_890_, v___x_896_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_895_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l_Lean_getConstInfoRec___redArg___lam__0___closed__1, &l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_throwError___redArg(v_inst_891_, v_inst_892_, v___x_900_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_903_; 
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_inst_891_);
lean_dec(v_constName_890_);
v_val_902_ = lean_ctor_get(v_____do__lift_894_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v_____do__lift_894_, 1);
v___x_903_ = lean_apply_2(v_toPure_893_, lean_box(0), v_val_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg(lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_constName_907_){
_start:
{
lean_object* v_toApplicative_908_; lean_object* v_toBind_909_; lean_object* v_getEnv_910_; lean_object* v_toPure_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_toApplicative_908_ = lean_ctor_get(v_inst_904_, 0);
v_toBind_909_ = lean_ctor_get(v_inst_904_, 1);
lean_inc_n(v_toBind_909_, 2);
v_getEnv_910_ = lean_ctor_get(v_inst_905_, 0);
lean_inc(v_getEnv_910_);
lean_dec_ref(v_inst_905_);
v_toPure_911_ = lean_ctor_get(v_toApplicative_908_, 1);
lean_inc_n(v_toPure_911_, 2);
v___x_912_ = lean_box(0);
lean_inc_ref(v_inst_904_);
lean_inc(v_constName_907_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_getConstInfoRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_913_, 0, v_constName_907_);
lean_closure_set(v___f_913_, 1, v_inst_904_);
lean_closure_set(v___f_913_, 2, v_inst_906_);
lean_closure_set(v___f_913_, 3, v_toPure_911_);
v___x_914_ = l_instInhabitedOfMonad___redArg(v_inst_904_, v___x_912_);
v___f_915_ = lean_alloc_closure((void*)(l_Lean_isRec_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_915_, 0, v_toPure_911_);
lean_closure_set(v___f_915_, 1, v_constName_907_);
lean_closure_set(v___f_915_, 2, v___x_914_);
v___x_916_ = lean_apply_4(v_toBind_909_, lean_box(0), lean_box(0), v_getEnv_910_, v___f_915_);
v___x_917_ = lean_apply_4(v_toBind_909_, lean_box(0), lean_box(0), v___x_916_, v___f_913_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object* v_m_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_constName_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_getConstInfoRec___redArg(v_inst_919_, v_inst_920_, v_inst_921_, v_constName_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__0(lean_object* v_k_924_, lean_object* v_val_925_, lean_object* v_us_926_, lean_object* v_failK_927_, lean_object* v_____do__lift_928_){
_start:
{
if (lean_obj_tag(v_____do__lift_928_) == 6)
{
lean_object* v_val_929_; lean_object* v___x_930_; 
lean_dec(v_failK_927_);
v_val_929_ = lean_ctor_get(v_____do__lift_928_, 0);
lean_inc_ref(v_val_929_);
lean_dec_ref_known(v_____do__lift_928_, 1);
v___x_930_ = lean_apply_3(v_k_924_, v_val_925_, v_us_926_, v_val_929_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v_____do__lift_928_);
lean_dec(v_us_926_);
lean_dec_ref(v_val_925_);
lean_dec(v_k_924_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_apply_1(v_failK_927_, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__1(lean_object* v_declName_933_, lean_object* v_failK_934_, lean_object* v_k_935_, lean_object* v_us_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_toBind_940_, lean_object* v_____do__lift_941_){
_start:
{
uint8_t v___x_945_; lean_object* v___x_946_; 
v___x_945_ = 0;
v___x_946_ = l_Lean_Environment_find_x3f(v_____do__lift_941_, v_declName_933_, v___x_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v_toBind_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec(v_us_936_);
lean_dec(v_k_935_);
v___x_947_ = lean_box(0);
v___x_948_ = lean_apply_1(v_failK_934_, v___x_947_);
return v___x_948_;
}
else
{
lean_object* v_val_949_; 
v_val_949_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_val_949_);
lean_dec_ref_known(v___x_946_, 1);
if (lean_obj_tag(v_val_949_) == 5)
{
lean_object* v_val_950_; lean_object* v_ctors_951_; 
v_val_950_ = lean_ctor_get(v_val_949_, 0);
lean_inc_ref(v_val_950_);
lean_dec_ref_known(v_val_949_, 1);
v_ctors_951_ = lean_ctor_get(v_val_950_, 4);
if (lean_obj_tag(v_ctors_951_) == 1)
{
lean_object* v_tail_952_; 
v_tail_952_ = lean_ctor_get(v_ctors_951_, 1);
if (lean_obj_tag(v_tail_952_) == 0)
{
lean_object* v_head_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_head_953_ = lean_ctor_get(v_ctors_951_, 0);
lean_inc(v_head_953_);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(v___f_954_, 0, v_k_935_);
lean_closure_set(v___f_954_, 1, v_val_950_);
lean_closure_set(v___f_954_, 2, v_us_936_);
lean_closure_set(v___f_954_, 3, v_failK_934_);
v___x_955_ = l_Lean_getConstInfo___redArg(v_inst_937_, v_inst_938_, v_inst_939_, v_head_953_);
v___x_956_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_955_, v___f_954_);
return v___x_956_;
}
else
{
lean_dec_ref(v_val_950_);
lean_dec(v_toBind_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec(v_us_936_);
lean_dec(v_k_935_);
goto v___jp_942_;
}
}
else
{
lean_dec_ref(v_val_950_);
lean_dec(v_toBind_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec(v_us_936_);
lean_dec(v_k_935_);
goto v___jp_942_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_val_949_);
lean_dec(v_toBind_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec(v_us_936_);
lean_dec(v_k_935_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_apply_1(v_failK_934_, v___x_957_);
return v___x_958_;
}
}
v___jp_942_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_box(0);
v___x_944_ = lean_apply_1(v_failK_934_, v___x_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg(lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_e_962_, lean_object* v_failK_963_, lean_object* v_k_964_){
_start:
{
if (lean_obj_tag(v_e_962_) == 4)
{
lean_object* v_toBind_965_; lean_object* v_declName_966_; lean_object* v_us_967_; lean_object* v_getEnv_968_; lean_object* v___f_969_; lean_object* v___x_970_; 
v_toBind_965_ = lean_ctor_get(v_inst_959_, 1);
lean_inc_n(v_toBind_965_, 2);
v_declName_966_ = lean_ctor_get(v_e_962_, 0);
lean_inc(v_declName_966_);
v_us_967_ = lean_ctor_get(v_e_962_, 1);
lean_inc(v_us_967_);
lean_dec_ref_known(v_e_962_, 2);
v_getEnv_968_ = lean_ctor_get(v_inst_960_, 0);
lean_inc(v_getEnv_968_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_969_, 0, v_declName_966_);
lean_closure_set(v___f_969_, 1, v_failK_963_);
lean_closure_set(v___f_969_, 2, v_k_964_);
lean_closure_set(v___f_969_, 3, v_us_967_);
lean_closure_set(v___f_969_, 4, v_inst_959_);
lean_closure_set(v___f_969_, 5, v_inst_960_);
lean_closure_set(v___f_969_, 6, v_inst_961_);
lean_closure_set(v___f_969_, 7, v_toBind_965_);
v___x_970_ = lean_apply_4(v_toBind_965_, lean_box(0), lean_box(0), v_getEnv_968_, v___f_969_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_k_964_);
lean_dec_ref(v_e_962_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
lean_dec_ref(v_inst_959_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_apply_1(v_failK_963_, v___x_971_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure(lean_object* v_m_973_, lean_object* v_00_u03b1_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_e_978_, lean_object* v_failK_979_, lean_object* v_k_980_){
_start:
{
if (lean_obj_tag(v_e_978_) == 4)
{
lean_object* v_toBind_981_; lean_object* v_declName_982_; lean_object* v_us_983_; lean_object* v_getEnv_984_; lean_object* v___f_985_; lean_object* v___x_986_; 
v_toBind_981_ = lean_ctor_get(v_inst_975_, 1);
lean_inc_n(v_toBind_981_, 2);
v_declName_982_ = lean_ctor_get(v_e_978_, 0);
lean_inc(v_declName_982_);
v_us_983_ = lean_ctor_get(v_e_978_, 1);
lean_inc(v_us_983_);
lean_dec_ref_known(v_e_978_, 2);
v_getEnv_984_ = lean_ctor_get(v_inst_976_, 0);
lean_inc(v_getEnv_984_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_985_, 0, v_declName_982_);
lean_closure_set(v___f_985_, 1, v_failK_979_);
lean_closure_set(v___f_985_, 2, v_k_980_);
lean_closure_set(v___f_985_, 3, v_us_983_);
lean_closure_set(v___f_985_, 4, v_inst_975_);
lean_closure_set(v___f_985_, 5, v_inst_976_);
lean_closure_set(v___f_985_, 6, v_inst_977_);
lean_closure_set(v___f_985_, 7, v_toBind_981_);
v___x_986_ = lean_apply_4(v_toBind_981_, lean_box(0), lean_box(0), v_getEnv_984_, v___f_985_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_k_980_);
lean_dec_ref(v_e_978_);
lean_dec_ref(v_inst_977_);
lean_dec_ref(v_inst_976_);
lean_dec_ref(v_inst_975_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_1(v_failK_979_, v___x_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg___lam__1(lean_object* v_declName_989_, lean_object* v_failK_990_, lean_object* v_k_991_, lean_object* v_us_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_toBind_996_, lean_object* v_____do__lift_997_){
_start:
{
uint8_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = 0;
v___x_1005_ = l_Lean_Environment_find_x3f(v_____do__lift_997_, v_declName_989_, v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec(v_us_992_);
lean_dec(v_k_991_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_apply_1(v_failK_990_, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; 
v_val_1008_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___x_1005_, 1);
if (lean_obj_tag(v_val_1008_) == 5)
{
lean_object* v_val_1009_; uint8_t v_isRec_1010_; 
v_val_1009_ = lean_ctor_get(v_val_1008_, 0);
lean_inc_ref(v_val_1009_);
lean_dec_ref_known(v_val_1008_, 1);
v_isRec_1010_ = lean_ctor_get_uint8(v_val_1009_, sizeof(void*)*6);
if (v_isRec_1010_ == 0)
{
lean_object* v_numIndices_1011_; lean_object* v_ctors_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; uint8_t v___x_1015_; 
v_numIndices_1011_ = lean_ctor_get(v_val_1009_, 2);
v_ctors_1012_ = lean_ctor_get(v_val_1009_, 4);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_nat_dec_eq(v_numIndices_1011_, v___x_1013_);
v___x_1015_ = lean_bool_not(v___x_1014_);
if (v___x_1015_ == 0)
{
if (lean_obj_tag(v_ctors_1012_) == 1)
{
lean_object* v_tail_1016_; 
v_tail_1016_ = lean_ctor_get(v_ctors_1012_, 1);
if (lean_obj_tag(v_tail_1016_) == 0)
{
lean_object* v_head_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_head_1017_ = lean_ctor_get(v_ctors_1012_, 0);
lean_inc(v_head_1017_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1018_, 0, v_k_991_);
lean_closure_set(v___f_1018_, 1, v_val_1009_);
lean_closure_set(v___f_1018_, 2, v_us_992_);
lean_closure_set(v___f_1018_, 3, v_failK_990_);
v___x_1019_ = l_Lean_getConstInfo___redArg(v_inst_993_, v_inst_994_, v_inst_995_, v_head_1017_);
v___x_1020_ = lean_apply_4(v_toBind_996_, lean_box(0), lean_box(0), v___x_1019_, v___f_1018_);
return v___x_1020_;
}
else
{
lean_dec_ref(v_val_1009_);
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec(v_us_992_);
lean_dec(v_k_991_);
goto v___jp_1001_;
}
}
else
{
lean_dec_ref(v_val_1009_);
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec(v_us_992_);
lean_dec(v_k_991_);
goto v___jp_1001_;
}
}
else
{
lean_dec_ref(v_val_1009_);
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec(v_us_992_);
lean_dec(v_k_991_);
goto v___jp_998_;
}
}
else
{
lean_dec_ref(v_val_1009_);
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec(v_us_992_);
lean_dec(v_k_991_);
goto v___jp_998_;
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_val_1008_);
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec(v_us_992_);
lean_dec(v_k_991_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_apply_1(v_failK_990_, v___x_1021_);
return v___x_1022_;
}
}
v___jp_998_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_box(0);
v___x_1000_ = lean_apply_1(v_failK_990_, v___x_999_);
return v___x_1000_;
}
v___jp_1001_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_apply_1(v_failK_990_, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg(lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_e_1026_, lean_object* v_failK_1027_, lean_object* v_k_1028_){
_start:
{
if (lean_obj_tag(v_e_1026_) == 4)
{
lean_object* v_toBind_1029_; lean_object* v_declName_1030_; lean_object* v_us_1031_; lean_object* v_getEnv_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
v_toBind_1029_ = lean_ctor_get(v_inst_1023_, 1);
lean_inc_n(v_toBind_1029_, 2);
v_declName_1030_ = lean_ctor_get(v_e_1026_, 0);
lean_inc(v_declName_1030_);
v_us_1031_ = lean_ctor_get(v_e_1026_, 1);
lean_inc(v_us_1031_);
lean_dec_ref_known(v_e_1026_, 2);
v_getEnv_1032_ = lean_ctor_get(v_inst_1024_, 0);
lean_inc(v_getEnv_1032_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_matchConstNonRecStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1033_, 0, v_declName_1030_);
lean_closure_set(v___f_1033_, 1, v_failK_1027_);
lean_closure_set(v___f_1033_, 2, v_k_1028_);
lean_closure_set(v___f_1033_, 3, v_us_1031_);
lean_closure_set(v___f_1033_, 4, v_inst_1023_);
lean_closure_set(v___f_1033_, 5, v_inst_1024_);
lean_closure_set(v___f_1033_, 6, v_inst_1025_);
lean_closure_set(v___f_1033_, 7, v_toBind_1029_);
v___x_1034_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v_getEnv_1032_, v___f_1033_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v_k_1028_);
lean_dec_ref(v_e_1026_);
lean_dec_ref(v_inst_1025_);
lean_dec_ref(v_inst_1024_);
lean_dec_ref(v_inst_1023_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_apply_1(v_failK_1027_, v___x_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure(lean_object* v_m_1037_, lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_e_1042_, lean_object* v_failK_1043_, lean_object* v_k_1044_){
_start:
{
if (lean_obj_tag(v_e_1042_) == 4)
{
lean_object* v_toBind_1045_; lean_object* v_declName_1046_; lean_object* v_us_1047_; lean_object* v_getEnv_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; 
v_toBind_1045_ = lean_ctor_get(v_inst_1039_, 1);
lean_inc_n(v_toBind_1045_, 2);
v_declName_1046_ = lean_ctor_get(v_e_1042_, 0);
lean_inc(v_declName_1046_);
v_us_1047_ = lean_ctor_get(v_e_1042_, 1);
lean_inc(v_us_1047_);
lean_dec_ref_known(v_e_1042_, 2);
v_getEnv_1048_ = lean_ctor_get(v_inst_1040_, 0);
lean_inc(v_getEnv_1048_);
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_matchConstNonRecStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1049_, 0, v_declName_1046_);
lean_closure_set(v___f_1049_, 1, v_failK_1043_);
lean_closure_set(v___f_1049_, 2, v_k_1044_);
lean_closure_set(v___f_1049_, 3, v_us_1047_);
lean_closure_set(v___f_1049_, 4, v_inst_1039_);
lean_closure_set(v___f_1049_, 5, v_inst_1040_);
lean_closure_set(v___f_1049_, 6, v_inst_1041_);
lean_closure_set(v___f_1049_, 7, v_toBind_1045_);
v___x_1050_ = lean_apply_4(v_toBind_1045_, lean_box(0), lean_box(0), v_getEnv_1048_, v___f_1049_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec(v_k_1044_);
lean_dec_ref(v_e_1042_);
lean_dec_ref(v_inst_1041_);
lean_dec_ref(v_inst_1040_);
lean_dec_ref(v_inst_1039_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_apply_1(v_failK_1043_, v___x_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasCompileError___boxed(lean_object* v_env_1055_, lean_object* v_constName_1056_){
_start:
{
uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = lean_has_compile_error(v_env_1055_, v_constName_1056_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0(lean_object* v_____do__lift_1059_, lean_object* v_constName_1060_, uint8_t v_checkMeta_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v___x_1064_, lean_object* v_____do__lift_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Lean_Environment_evalConst___redArg(v_____do__lift_1059_, v_____do__lift_1065_, v_constName_1060_, v_checkMeta_1061_);
v___x_1067_ = l_Lean_ofExcept___redArg(v_inst_1062_, v_inst_1063_, v___x_1064_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0___boxed(lean_object* v_____do__lift_1068_, lean_object* v_constName_1069_, lean_object* v_checkMeta_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v___x_1073_, lean_object* v_____do__lift_1074_){
_start:
{
uint8_t v_checkMeta_boxed_1075_; lean_object* v_res_1076_; 
v_checkMeta_boxed_1075_ = lean_unbox(v_checkMeta_1070_);
v_res_1076_ = l_Lean_evalConst___redArg___lam__0(v_____do__lift_1068_, v_constName_1069_, v_checkMeta_boxed_1075_, v_inst_1071_, v_inst_1072_, v___x_1073_, v_____do__lift_1074_);
lean_dec_ref(v_____do__lift_1074_);
lean_dec(v_constName_1069_);
lean_dec_ref(v_____do__lift_1068_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1(lean_object* v_constName_1077_, uint8_t v_checkMeta_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v___x_1081_, lean_object* v_toBind_1082_, lean_object* v_inst_1083_, lean_object* v_____do__lift_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(v_checkMeta_1078_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1086_, 0, v_____do__lift_1084_);
lean_closure_set(v___f_1086_, 1, v_constName_1077_);
lean_closure_set(v___f_1086_, 2, v___x_1085_);
lean_closure_set(v___f_1086_, 3, v_inst_1079_);
lean_closure_set(v___f_1086_, 4, v_inst_1080_);
lean_closure_set(v___f_1086_, 5, v___x_1081_);
v___x_1087_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v_inst_1083_, v___f_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1___boxed(lean_object* v_constName_1088_, lean_object* v_checkMeta_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v___x_1092_, lean_object* v_toBind_1093_, lean_object* v_inst_1094_, lean_object* v_____do__lift_1095_){
_start:
{
uint8_t v_checkMeta_boxed_1096_; lean_object* v_res_1097_; 
v_checkMeta_boxed_1096_ = lean_unbox(v_checkMeta_1089_);
v_res_1097_ = l_Lean_evalConst___redArg___lam__1(v_constName_1088_, v_checkMeta_boxed_1096_, v_inst_1090_, v_inst_1091_, v___x_1092_, v_toBind_1093_, v_inst_1094_, v_____do__lift_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__2(lean_object* v_toBind_1098_, lean_object* v_getEnv_1099_, lean_object* v___f_1100_, lean_object* v_____r_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v_getEnv_1099_, v___f_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__3(lean_object* v_constName_1103_, lean_object* v_toBind_1104_, lean_object* v_getEnv_1105_, lean_object* v___f_1106_, lean_object* v_inst_1107_, lean_object* v___f_1108_, lean_object* v_____do__lift_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_has_compile_error(v_____do__lift_1109_, v_constName_1103_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v___f_1108_);
lean_dec_ref(v_inst_1107_);
v___x_1111_ = lean_apply_4(v_toBind_1104_, lean_box(0), lean_box(0), v_getEnv_1105_, v___f_1106_);
return v___x_1111_;
}
else
{
lean_object* v_toMonadExceptOf_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v___f_1106_);
lean_dec(v_getEnv_1105_);
v_toMonadExceptOf_1112_ = lean_ctor_get(v_inst_1107_, 0);
lean_inc_ref(v_toMonadExceptOf_1112_);
lean_dec_ref(v_inst_1107_);
v___x_1113_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_1112_);
v___x_1114_ = l_Lean_Elab_throwAbortCommand___redArg(v___x_1113_);
v___x_1115_ = lean_apply_4(v_toBind_1104_, lean_box(0), lean_box(0), v___x_1114_, v___f_1108_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg(lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_constName_1121_, uint8_t v_checkMeta_1122_){
_start:
{
lean_object* v_toBind_1123_; lean_object* v_getEnv_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v_toBind_1123_ = lean_ctor_get(v_inst_1117_, 1);
lean_inc_n(v_toBind_1123_, 4);
v_getEnv_1124_ = lean_ctor_get(v_inst_1118_, 0);
lean_inc_n(v_getEnv_1124_, 3);
lean_dec_ref(v_inst_1118_);
v___x_1125_ = ((lean_object*)(l_Lean_evalConst___redArg___closed__0));
v___x_1126_ = lean_box(v_checkMeta_1122_);
lean_inc_ref(v_inst_1119_);
lean_inc(v_constName_1121_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1127_, 0, v_constName_1121_);
lean_closure_set(v___f_1127_, 1, v___x_1126_);
lean_closure_set(v___f_1127_, 2, v_inst_1117_);
lean_closure_set(v___f_1127_, 3, v_inst_1119_);
lean_closure_set(v___f_1127_, 4, v___x_1125_);
lean_closure_set(v___f_1127_, 5, v_toBind_1123_);
lean_closure_set(v___f_1127_, 6, v_inst_1120_);
lean_inc_ref(v___f_1127_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1128_, 0, v_toBind_1123_);
lean_closure_set(v___f_1128_, 1, v_getEnv_1124_);
lean_closure_set(v___f_1128_, 2, v___f_1127_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1129_, 0, v_constName_1121_);
lean_closure_set(v___f_1129_, 1, v_toBind_1123_);
lean_closure_set(v___f_1129_, 2, v_getEnv_1124_);
lean_closure_set(v___f_1129_, 3, v___f_1127_);
lean_closure_set(v___f_1129_, 4, v_inst_1119_);
lean_closure_set(v___f_1129_, 5, v___f_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v_getEnv_1124_, v___f_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___boxed(lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_constName_1135_, lean_object* v_checkMeta_1136_){
_start:
{
uint8_t v_checkMeta_boxed_1137_; lean_object* v_res_1138_; 
v_checkMeta_boxed_1137_ = lean_unbox(v_checkMeta_1136_);
v_res_1138_ = l_Lean_evalConst___redArg(v_inst_1131_, v_inst_1132_, v_inst_1133_, v_inst_1134_, v_constName_1135_, v_checkMeta_boxed_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_00_u03b1_1144_, lean_object* v_constName_1145_, uint8_t v_checkMeta_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_evalConst___redArg(v_inst_1140_, v_inst_1141_, v_inst_1142_, v_inst_1143_, v_constName_1145_, v_checkMeta_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___boxed(lean_object* v_m_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_00_u03b1_1153_, lean_object* v_constName_1154_, lean_object* v_checkMeta_1155_){
_start:
{
uint8_t v_checkMeta_boxed_1156_; lean_object* v_res_1157_; 
v_checkMeta_boxed_1156_ = lean_unbox(v_checkMeta_1155_);
v_res_1157_ = l_Lean_evalConst(v_m_1148_, v_inst_1149_, v_inst_1150_, v_inst_1151_, v_inst_1152_, v_00_u03b1_1153_, v_constName_1154_, v_checkMeta_boxed_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0(lean_object* v_____do__lift_1158_, lean_object* v_typeName_1159_, lean_object* v_constName_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v___x_1163_, lean_object* v_____do__lift_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_1158_, v_____do__lift_1164_, v_typeName_1159_, v_constName_1160_);
v___x_1166_ = l_Lean_ofExcept___redArg(v_inst_1161_, v_inst_1162_, v___x_1163_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0___boxed(lean_object* v_____do__lift_1167_, lean_object* v_typeName_1168_, lean_object* v_constName_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v___x_1172_, lean_object* v_____do__lift_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_evalConstCheck___redArg___lam__0(v_____do__lift_1167_, v_typeName_1168_, v_constName_1169_, v_inst_1170_, v_inst_1171_, v___x_1172_, v_____do__lift_1173_);
lean_dec_ref(v_____do__lift_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__1(lean_object* v_typeName_1175_, lean_object* v_constName_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v___x_1179_, lean_object* v_toBind_1180_, lean_object* v_inst_1181_, lean_object* v_____do__lift_1182_){
_start:
{
lean_object* v___f_1183_; lean_object* v___x_1184_; 
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1183_, 0, v_____do__lift_1182_);
lean_closure_set(v___f_1183_, 1, v_typeName_1175_);
lean_closure_set(v___f_1183_, 2, v_constName_1176_);
lean_closure_set(v___f_1183_, 3, v_inst_1177_);
lean_closure_set(v___f_1183_, 4, v_inst_1178_);
lean_closure_set(v___f_1183_, 5, v___x_1179_);
v___x_1184_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v_inst_1181_, v___f_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_typeName_1189_, lean_object* v_constName_1190_){
_start:
{
lean_object* v_toBind_1191_; lean_object* v_getEnv_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; 
v_toBind_1191_ = lean_ctor_get(v_inst_1185_, 1);
lean_inc_n(v_toBind_1191_, 4);
v_getEnv_1192_ = lean_ctor_get(v_inst_1186_, 0);
lean_inc_n(v_getEnv_1192_, 3);
lean_dec_ref(v_inst_1186_);
v___x_1193_ = ((lean_object*)(l_Lean_evalConst___redArg___closed__0));
lean_inc_ref(v_inst_1187_);
lean_inc(v_constName_1190_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1194_, 0, v_typeName_1189_);
lean_closure_set(v___f_1194_, 1, v_constName_1190_);
lean_closure_set(v___f_1194_, 2, v_inst_1185_);
lean_closure_set(v___f_1194_, 3, v_inst_1187_);
lean_closure_set(v___f_1194_, 4, v___x_1193_);
lean_closure_set(v___f_1194_, 5, v_toBind_1191_);
lean_closure_set(v___f_1194_, 6, v_inst_1188_);
lean_inc_ref(v___f_1194_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1195_, 0, v_toBind_1191_);
lean_closure_set(v___f_1195_, 1, v_getEnv_1192_);
lean_closure_set(v___f_1195_, 2, v___f_1194_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1196_, 0, v_constName_1190_);
lean_closure_set(v___f_1196_, 1, v_toBind_1191_);
lean_closure_set(v___f_1196_, 2, v_getEnv_1192_);
lean_closure_set(v___f_1196_, 3, v___f_1194_);
lean_closure_set(v___f_1196_, 4, v_inst_1187_);
lean_closure_set(v___f_1196_, 5, v___f_1195_);
v___x_1197_ = lean_apply_4(v_toBind_1191_, lean_box(0), lean_box(0), v_getEnv_1192_, v___f_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object* v_m_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_typeName_1204_, lean_object* v_constName_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_evalConstCheck___redArg(v_inst_1199_, v_inst_1200_, v_inst_1201_, v_inst_1202_, v_typeName_1204_, v_constName_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0(lean_object* v___x_1207_, lean_object* v_val_1208_, lean_object* v_toPure_1209_, lean_object* v_____do__lift_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = l_Lean_Environment_allImportedModuleNames(v_____do__lift_1210_);
v___x_1212_ = lean_array_get(v___x_1207_, v___x_1211_, v_val_1208_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = lean_apply_2(v_toPure_1209_, lean_box(0), v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(lean_object* v___x_1215_, lean_object* v_val_1216_, lean_object* v_toPure_1217_, lean_object* v_____do__lift_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_findModuleOf_x3f___redArg___lam__0(v___x_1215_, v_val_1216_, v_toPure_1217_, v_____do__lift_1218_);
lean_dec_ref(v_____do__lift_1218_);
lean_dec(v_val_1216_);
lean_dec(v___x_1215_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1(lean_object* v_declName_1220_, lean_object* v_toPure_1221_, lean_object* v___x_1222_, lean_object* v_toBind_1223_, lean_object* v_getEnv_1224_, lean_object* v_____do__lift_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1225_, v_declName_1220_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_getEnv_1224_);
lean_dec(v_toBind_1223_);
lean_dec(v___x_1222_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_apply_2(v_toPure_1221_, lean_box(0), v___x_1227_);
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; 
v_val_1229_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1226_, 1);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1230_, 0, v___x_1222_);
lean_closure_set(v___f_1230_, 1, v_val_1229_);
lean_closure_set(v___f_1230_, 2, v_toPure_1221_);
v___x_1231_ = lean_apply_4(v_toBind_1223_, lean_box(0), lean_box(0), v_getEnv_1224_, v___f_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(lean_object* v_declName_1232_, lean_object* v_toPure_1233_, lean_object* v___x_1234_, lean_object* v_toBind_1235_, lean_object* v_getEnv_1236_, lean_object* v_____do__lift_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_findModuleOf_x3f___redArg___lam__1(v_declName_1232_, v_toPure_1233_, v___x_1234_, v_toBind_1235_, v_getEnv_1236_, v_____do__lift_1237_);
lean_dec_ref(v_____do__lift_1237_);
lean_dec(v_declName_1232_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__2(lean_object* v_inst_1239_, lean_object* v_declName_1240_, lean_object* v_toPure_1241_, lean_object* v___x_1242_, lean_object* v_toBind_1243_, lean_object* v_____r_1244_){
_start:
{
lean_object* v_getEnv_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v_getEnv_1245_ = lean_ctor_get(v_inst_1239_, 0);
lean_inc_n(v_getEnv_1245_, 2);
lean_dec_ref(v_inst_1239_);
lean_inc(v_toBind_1243_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1246_, 0, v_declName_1240_);
lean_closure_set(v___f_1246_, 1, v_toPure_1241_);
lean_closure_set(v___f_1246_, 2, v___x_1242_);
lean_closure_set(v___f_1246_, 3, v_toBind_1243_);
lean_closure_set(v___f_1246_, 4, v_getEnv_1245_);
v___x_1247_ = lean_apply_4(v_toBind_1243_, lean_box(0), lean_box(0), v_getEnv_1245_, v___f_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg(lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_declName_1251_){
_start:
{
lean_object* v_toApplicative_1252_; lean_object* v_toFunctor_1253_; lean_object* v_toBind_1254_; lean_object* v_toPure_1255_; lean_object* v_mapConst_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_toApplicative_1252_ = lean_ctor_get(v_inst_1248_, 0);
v_toFunctor_1253_ = lean_ctor_get(v_toApplicative_1252_, 0);
v_toBind_1254_ = lean_ctor_get(v_inst_1248_, 1);
lean_inc_n(v_toBind_1254_, 2);
v_toPure_1255_ = lean_ctor_get(v_toApplicative_1252_, 1);
v_mapConst_1256_ = lean_ctor_get(v_toFunctor_1253_, 1);
lean_inc(v_mapConst_1256_);
v___x_1257_ = lean_box(0);
lean_inc(v_toPure_1255_);
lean_inc(v_declName_1251_);
lean_inc_ref(v_inst_1249_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1258_, 0, v_inst_1249_);
lean_closure_set(v___f_1258_, 1, v_declName_1251_);
lean_closure_set(v___f_1258_, 2, v_toPure_1255_);
lean_closure_set(v___f_1258_, 3, v___x_1257_);
lean_closure_set(v___f_1258_, 4, v_toBind_1254_);
v___x_1259_ = l_Lean_getConstInfo___redArg(v_inst_1248_, v_inst_1249_, v_inst_1250_, v_declName_1251_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_apply_4(v_mapConst_1256_, lean_box(0), lean_box(0), v___x_1260_, v___x_1259_);
v___x_1262_ = lean_apply_4(v_toBind_1254_, lean_box(0), lean_box(0), v___x_1261_, v___f_1258_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object* v_m_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_declName_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_findModuleOf_x3f___redArg(v_inst_1264_, v_inst_1265_, v_inst_1266_, v_declName_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object* v_toPure_1269_, lean_object* v_____x_1270_){
_start:
{
if (lean_obj_tag(v_____x_1270_) == 6)
{
lean_object* v_val_1271_; lean_object* v_numFields_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_val_1271_ = lean_ctor_get(v_____x_1270_, 0);
v_numFields_1272_ = lean_ctor_get(v_val_1271_, 4);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_nat_dec_eq(v_numFields_1272_, v___x_1273_);
v___x_1275_ = lean_box(v___x_1274_);
v___x_1276_ = lean_apply_2(v_toPure_1269_, lean_box(0), v___x_1275_);
return v___x_1276_;
}
else
{
uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = 0;
v___x_1278_ = lean_box(v___x_1277_);
v___x_1279_ = lean_apply_2(v_toPure_1269_, lean_box(0), v___x_1278_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object* v_toPure_1280_, lean_object* v_____x_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_isEnumType___redArg___lam__0(v_toPure_1280_, v_____x_1281_);
lean_dec_ref(v_____x_1281_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_toBind_1286_, lean_object* v___f_1287_, lean_object* v_ctorName_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = l_Lean_getConstInfo___redArg(v_inst_1283_, v_inst_1284_, v_inst_1285_, v_ctorName_1288_);
v___x_1290_ = lean_apply_4(v_toBind_1286_, lean_box(0), lean_box(0), v___x_1289_, v___f_1287_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object* v_toPure_1291_, lean_object* v_inst_1292_, lean_object* v___f_1293_, lean_object* v_____do__lift_1294_){
_start:
{
if (lean_obj_tag(v_____do__lift_1294_) == 5)
{
lean_object* v_val_1295_; lean_object* v_toConstantVal_1296_; lean_object* v_numParams_1297_; lean_object* v_numIndices_1298_; lean_object* v_ctors_1299_; uint8_t v_isRec_1300_; uint8_t v_isUnsafe_1301_; uint8_t v___y_1303_; lean_object* v_type_1324_; uint8_t v___x_1325_; uint8_t v___x_1326_; 
v_val_1295_ = lean_ctor_get(v_____do__lift_1294_, 0);
lean_inc_ref(v_val_1295_);
lean_dec_ref_known(v_____do__lift_1294_, 1);
v_toConstantVal_1296_ = lean_ctor_get(v_val_1295_, 0);
v_numParams_1297_ = lean_ctor_get(v_val_1295_, 1);
lean_inc(v_numParams_1297_);
v_numIndices_1298_ = lean_ctor_get(v_val_1295_, 2);
lean_inc(v_numIndices_1298_);
v_ctors_1299_ = lean_ctor_get(v_val_1295_, 4);
lean_inc(v_ctors_1299_);
v_isRec_1300_ = lean_ctor_get_uint8(v_val_1295_, sizeof(void*)*6);
v_isUnsafe_1301_ = lean_ctor_get_uint8(v_val_1295_, sizeof(void*)*6 + 1);
v_type_1324_ = lean_ctor_get(v_toConstantVal_1296_, 2);
v___x_1325_ = l_Lean_Expr_isProp(v_type_1324_);
v___x_1326_ = lean_bool_not(v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_val_1295_);
v___y_1303_ = v___x_1326_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1327_ = l_Lean_InductiveVal_numTypeFormers(v_val_1295_);
lean_dec_ref(v_val_1295_);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_dec_eq(v___x_1327_, v___x_1328_);
lean_dec(v___x_1327_);
v___y_1303_ = v___x_1329_;
goto v___jp_1302_;
}
v___jp_1302_:
{
if (v___y_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v_ctors_1299_);
lean_dec(v_numIndices_1298_);
lean_dec(v_numParams_1297_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1304_ = lean_box(v___y_1303_);
v___x_1305_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1304_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_nat_dec_eq(v_numIndices_1298_, v___x_1306_);
lean_dec(v_numIndices_1298_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v_ctors_1299_);
lean_dec(v_numParams_1297_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1308_ = lean_box(v___x_1307_);
v___x_1309_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1308_);
return v___x_1309_;
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_eq(v_numParams_1297_, v___x_1306_);
lean_dec(v_numParams_1297_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec(v_ctors_1299_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1311_ = lean_box(v___x_1310_);
v___x_1312_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1311_);
return v___x_1312_;
}
else
{
uint8_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = l_List_isEmpty___redArg(v_ctors_1299_);
v___x_1314_ = lean_bool_not(v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_ctors_1299_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1315_ = lean_box(v___x_1314_);
v___x_1316_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1315_);
return v___x_1316_;
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_bool_not(v_isRec_1300_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_ctors_1299_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1318_ = lean_box(v___x_1317_);
v___x_1319_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1318_);
return v___x_1319_;
}
else
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_bool_not(v_isUnsafe_1301_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_ctors_1299_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1321_ = lean_box(v___x_1320_);
v___x_1322_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1321_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_toPure_1291_);
v___x_1323_ = l_List_allM___redArg(v_inst_1292_, v___f_1293_, v_ctors_1299_);
return v___x_1323_;
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
uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_____do__lift_1294_);
lean_dec(v___f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1330_ = 0;
v___x_1331_ = lean_box(v___x_1330_);
v___x_1332_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1331_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_declName_1336_){
_start:
{
lean_object* v_toApplicative_1337_; lean_object* v_toBind_1338_; lean_object* v_toPure_1339_; lean_object* v___x_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; 
v_toApplicative_1337_ = lean_ctor_get(v_inst_1333_, 0);
v_toBind_1338_ = lean_ctor_get(v_inst_1333_, 1);
lean_inc_n(v_toBind_1338_, 2);
v_toPure_1339_ = lean_ctor_get(v_toApplicative_1337_, 1);
lean_inc_n(v_toPure_1339_, 2);
lean_inc_ref(v_inst_1335_);
lean_inc_ref(v_inst_1334_);
lean_inc_ref_n(v_inst_1333_, 2);
v___x_1340_ = l_Lean_getConstInfo___redArg(v_inst_1333_, v_inst_1334_, v_inst_1335_, v_declName_1336_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1341_, 0, v_toPure_1339_);
v___f_1342_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1342_, 0, v_inst_1333_);
lean_closure_set(v___f_1342_, 1, v_inst_1334_);
lean_closure_set(v___f_1342_, 2, v_inst_1335_);
lean_closure_set(v___f_1342_, 3, v_toBind_1338_);
lean_closure_set(v___f_1342_, 4, v___f_1341_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1343_, 0, v_toPure_1339_);
lean_closure_set(v___f_1343_, 1, v_inst_1333_);
lean_closure_set(v___f_1343_, 2, v___f_1342_);
v___x_1344_ = lean_apply_4(v_toBind_1338_, lean_box(0), lean_box(0), v___x_1340_, v___f_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object* v_m_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_declName_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_isEnumType___redArg(v_inst_1346_, v_inst_1347_, v_inst_1348_, v_declName_1349_);
return v___x_1350_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
lean_object* runtime_initialize_Lean_AuxRecursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Old(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Old(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_MonadEnv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* initialize_Lean_Log(uint8_t builtin);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Old(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_MonadEnv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Old(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_MonadEnv(builtin);
}
#ifdef __cplusplus
}
#endif
