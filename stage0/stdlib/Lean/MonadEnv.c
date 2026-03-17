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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_allM___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_isCtor_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_isCtor_x3f___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isCtor_x3f___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isRec_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_isRec_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_isRec_x3f___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_isRec_x3f___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isRec_x3f___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_toBind_51_);
lean_dec_ref(v_inst_45_);
v_getEnv_52_ = lean_ctor_get(v_inst_47_, 0);
lean_inc(v_getEnv_52_);
v_toFunctor_53_ = lean_ctor_get(v_toApplicative_50_, 0);
lean_inc_ref(v_toFunctor_53_);
lean_dec_ref(v_toApplicative_50_);
v___f_54_ = ((lean_object*)(l_Lean_withEnv___redArg___closed__0));
v___f_55_ = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_55_, 0, v_x_49_);
lean_inc(v_toBind_51_);
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
lean_dec_ref(v___x_69_);
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
lean_dec_ref(v___x_100_);
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
lean_inc(v_toBind_200_);
lean_dec_ref(v_inst_195_);
v_getEnv_201_ = lean_ctor_get(v_inst_196_, 0);
lean_inc(v_getEnv_201_);
v_toFunctor_202_ = lean_ctor_get(v_toApplicative_199_, 0);
lean_inc_ref(v_toFunctor_202_);
v_toPure_203_ = lean_ctor_get(v_toApplicative_199_, 1);
lean_inc(v_toPure_203_);
lean_dec_ref(v_toApplicative_199_);
v___f_204_ = ((lean_object*)(l_Lean_withoutModifyingEnv_x27___redArg___closed__0));
lean_inc(v_getEnv_201_);
lean_inc(v_toBind_200_);
lean_inc(v_toPure_203_);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_205_, 0, v_toPure_203_);
lean_closure_set(v___f_205_, 1, v_toBind_200_);
lean_closure_set(v___f_205_, 2, v_getEnv_201_);
v___f_206_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_206_, 0, v_toPure_203_);
lean_inc(v_toBind_200_);
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
lean_inc(v_toBind_216_);
lean_dec_ref(v_inst_210_);
v_getEnv_217_ = lean_ctor_get(v_inst_211_, 0);
lean_inc(v_getEnv_217_);
v_toFunctor_218_ = lean_ctor_get(v_toApplicative_215_, 0);
lean_inc_ref(v_toFunctor_218_);
v_toPure_219_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_219_);
lean_dec_ref(v_toApplicative_215_);
v___f_220_ = ((lean_object*)(l_Lean_withoutModifyingEnv_x27___redArg___closed__0));
lean_inc(v_getEnv_217_);
lean_inc(v_toBind_216_);
lean_inc(v_toPure_219_);
v___f_221_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_221_, 0, v_toPure_219_);
lean_closure_set(v___f_221_, 1, v_toBind_216_);
lean_closure_set(v___f_221_, 2, v_getEnv_217_);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_222_, 0, v_toPure_219_);
lean_inc(v_toBind_216_);
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
lean_dec_ref(v___x_231_);
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
lean_dec_ref(v_e_238_);
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
lean_dec_ref(v_e_253_);
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
lean_dec_ref(v___x_270_);
if (lean_obj_tag(v_val_273_) == 5)
{
lean_object* v_val_274_; lean_object* v___x_275_; 
lean_dec(v_failK_265_);
v_val_274_ = lean_ctor_get(v_val_273_, 0);
lean_inc_ref(v_val_274_);
lean_dec_ref(v_val_273_);
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
lean_dec_ref(v_e_280_);
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
lean_dec_ref(v_e_295_);
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
lean_dec_ref(v___x_312_);
if (lean_obj_tag(v_val_315_) == 6)
{
lean_object* v_val_316_; lean_object* v___x_317_; 
lean_dec(v_failK_307_);
v_val_316_ = lean_ctor_get(v_val_315_, 0);
lean_inc_ref(v_val_316_);
lean_dec_ref(v_val_315_);
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
lean_dec_ref(v_e_322_);
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
lean_dec_ref(v_e_337_);
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
lean_dec_ref(v___x_354_);
if (lean_obj_tag(v_val_357_) == 7)
{
lean_object* v_val_358_; lean_object* v___x_359_; 
lean_dec(v_failK_349_);
v_val_358_ = lean_ctor_get(v_val_357_, 0);
lean_inc_ref(v_val_358_);
lean_dec_ref(v_val_357_);
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
lean_dec_ref(v_e_364_);
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
lean_dec_ref(v_e_379_);
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
lean_dec_ref(v___x_440_);
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
lean_dec_ref(v___x_467_);
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
lean_dec_ref(v___x_494_);
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
v___x_543_ = lean_panic_fn(v___x_542_, v_msg_541_);
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
lean_dec_ref(v___x_562_);
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
lean_dec(v___x_600_);
v_val_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_ref(v_val_613_);
lean_dec_ref(v___x_612_);
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
lean_dec(v___x_600_);
goto v___jp_602_;
}
}
}
else
{
lean_dec(v___x_606_);
lean_dec(v___x_600_);
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
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_constName_623_){
_start:
{
lean_object* v_toApplicative_624_; lean_object* v_toBind_625_; lean_object* v_getEnv_626_; lean_object* v_toPure_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
v_toApplicative_624_ = lean_ctor_get(v_inst_621_, 0);
v_toBind_625_ = lean_ctor_get(v_inst_621_, 1);
lean_inc(v_toBind_625_);
v_getEnv_626_ = lean_ctor_get(v_inst_622_, 0);
lean_inc(v_getEnv_626_);
lean_dec_ref(v_inst_622_);
v_toPure_627_ = lean_ctor_get(v_toApplicative_624_, 1);
lean_inc(v_toPure_627_);
v___x_628_ = lean_box(0);
v___x_629_ = l_instInhabitedOfMonad___redArg(v_inst_621_, v___x_628_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_isDefn_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_630_, 0, v_toPure_627_);
lean_closure_set(v___f_630_, 1, v_constName_623_);
lean_closure_set(v___f_630_, 2, v___x_629_);
v___x_631_ = lean_apply_4(v_toBind_625_, lean_box(0), lean_box(0), v_getEnv_626_, v___f_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f(lean_object* v_m_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_constName_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_isDefn_x3f___redArg(v_inst_633_, v_inst_634_, v_constName_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_639_ = lean_unsigned_to_nat(11u);
v___x_640_ = lean_unsigned_to_nat(122u);
v___x_641_ = ((lean_object*)(l_Lean_isCtor_x3f___redArg___lam__0___closed__0));
v___x_642_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_643_ = l_mkPanicMessageWithDecl(v___x_642_, v___x_641_, v___x_640_, v___x_639_, v___x_638_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0(lean_object* v_toPure_644_, lean_object* v_constName_645_, lean_object* v___x_646_, lean_object* v_____do__lift_647_){
_start:
{
uint8_t v___x_651_; lean_object* v___x_652_; 
v___x_651_ = 0;
v___x_652_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_647_, v_constName_645_, v___x_651_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_666_; 
v_val_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_666_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_666_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_666_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
uint8_t v_kind_657_; 
v_kind_657_ = lean_ctor_get_uint8(v_val_653_, sizeof(void*)*3);
if (v_kind_657_ == 6)
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_653_);
if (lean_obj_tag(v___x_658_) == 6)
{
lean_object* v_val_659_; lean_object* v___x_661_; 
lean_dec(v___x_646_);
v_val_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_val_659_);
lean_dec_ref(v___x_658_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_val_659_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_val_659_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = lean_apply_2(v_toPure_644_, lean_box(0), v___x_661_);
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v___x_658_);
lean_del_object(v___x_655_);
lean_dec(v_toPure_644_);
v___x_664_ = lean_obj_once(&l_Lean_isCtor_x3f___redArg___lam__0___closed__1, &l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1);
v___x_665_ = l_panic___redArg(v___x_646_, v___x_664_);
return v___x_665_;
}
}
else
{
lean_del_object(v___x_655_);
lean_dec(v_val_653_);
lean_dec(v___x_646_);
goto v___jp_648_;
}
}
}
else
{
lean_dec(v___x_652_);
lean_dec(v___x_646_);
goto v___jp_648_;
}
v___jp_648_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = lean_apply_2(v_toPure_644_, lean_box(0), v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_constName_669_){
_start:
{
lean_object* v_toApplicative_670_; lean_object* v_toBind_671_; lean_object* v_getEnv_672_; lean_object* v_toPure_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___f_676_; lean_object* v___x_677_; 
v_toApplicative_670_ = lean_ctor_get(v_inst_667_, 0);
v_toBind_671_ = lean_ctor_get(v_inst_667_, 1);
lean_inc(v_toBind_671_);
v_getEnv_672_ = lean_ctor_get(v_inst_668_, 0);
lean_inc(v_getEnv_672_);
lean_dec_ref(v_inst_668_);
v_toPure_673_ = lean_ctor_get(v_toApplicative_670_, 1);
lean_inc(v_toPure_673_);
v___x_674_ = lean_box(0);
v___x_675_ = l_instInhabitedOfMonad___redArg(v_inst_667_, v___x_674_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_isCtor_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_676_, 0, v_toPure_673_);
lean_closure_set(v___f_676_, 1, v_constName_669_);
lean_closure_set(v___f_676_, 2, v___x_675_);
v___x_677_ = lean_apply_4(v_toBind_671_, lean_box(0), lean_box(0), v_getEnv_672_, v___f_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f(lean_object* v_m_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_constName_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_isCtor_x3f___redArg(v_inst_679_, v_inst_680_, v_constName_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_684_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_685_ = lean_unsigned_to_nat(11u);
v___x_686_ = lean_unsigned_to_nat(129u);
v___x_687_ = ((lean_object*)(l_Lean_isRec_x3f___redArg___lam__0___closed__0));
v___x_688_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_689_ = l_mkPanicMessageWithDecl(v___x_688_, v___x_687_, v___x_686_, v___x_685_, v___x_684_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0(lean_object* v_toPure_690_, lean_object* v_constName_691_, lean_object* v___x_692_, lean_object* v_____do__lift_693_){
_start:
{
uint8_t v___x_697_; lean_object* v___x_698_; 
v___x_697_ = 0;
v___x_698_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_693_, v_constName_691_, v___x_697_);
if (lean_obj_tag(v___x_698_) == 1)
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_712_; 
v_val_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_712_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_712_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_712_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
uint8_t v_kind_703_; 
v_kind_703_ = lean_ctor_get_uint8(v_val_699_, sizeof(void*)*3);
if (v_kind_703_ == 7)
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_699_);
if (lean_obj_tag(v___x_704_) == 7)
{
lean_object* v_val_705_; lean_object* v___x_707_; 
lean_dec(v___x_692_);
v_val_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_val_705_);
lean_dec_ref(v___x_704_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_val_705_);
v___x_707_ = v___x_701_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_val_705_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_apply_2(v_toPure_690_, lean_box(0), v___x_707_);
return v___x_708_;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref(v___x_704_);
lean_del_object(v___x_701_);
lean_dec(v_toPure_690_);
v___x_710_ = lean_obj_once(&l_Lean_isRec_x3f___redArg___lam__0___closed__1, &l_Lean_isRec_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1);
v___x_711_ = l_panic___redArg(v___x_692_, v___x_710_);
return v___x_711_;
}
}
else
{
lean_del_object(v___x_701_);
lean_dec(v_val_699_);
lean_dec(v___x_692_);
goto v___jp_694_;
}
}
}
else
{
lean_dec(v___x_698_);
lean_dec(v___x_692_);
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = lean_apply_2(v_toPure_690_, lean_box(0), v___x_695_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg(lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_constName_715_){
_start:
{
lean_object* v_toApplicative_716_; lean_object* v_toBind_717_; lean_object* v_getEnv_718_; lean_object* v_toPure_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___x_723_; 
v_toApplicative_716_ = lean_ctor_get(v_inst_713_, 0);
v_toBind_717_ = lean_ctor_get(v_inst_713_, 1);
lean_inc(v_toBind_717_);
v_getEnv_718_ = lean_ctor_get(v_inst_714_, 0);
lean_inc(v_getEnv_718_);
lean_dec_ref(v_inst_714_);
v_toPure_719_ = lean_ctor_get(v_toApplicative_716_, 1);
lean_inc(v_toPure_719_);
v___x_720_ = lean_box(0);
v___x_721_ = l_instInhabitedOfMonad___redArg(v_inst_713_, v___x_720_);
v___f_722_ = lean_alloc_closure((void*)(l_Lean_isRec_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_722_, 0, v_toPure_719_);
lean_closure_set(v___f_722_, 1, v_constName_715_);
lean_closure_set(v___f_722_, 2, v___x_721_);
v___x_723_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v_getEnv_718_, v___f_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f(lean_object* v_m_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_constName_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_isRec_x3f___redArg(v_inst_725_, v_inst_726_, v_constName_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0(lean_object* v_constName_730_, lean_object* v_toPure_731_, lean_object* v_info_732_){
_start:
{
lean_object* v_levelParams_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_levelParams_733_ = lean_ctor_get(v_info_732_, 1);
lean_inc(v_levelParams_733_);
lean_dec_ref(v_info_732_);
v___x_734_ = ((lean_object*)(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0));
v___x_735_ = lean_box(0);
v___x_736_ = l_List_mapTR_loop___redArg(v___x_734_, v_levelParams_733_, v___x_735_);
v___x_737_ = l_Lean_mkConst(v_constName_730_, v___x_736_);
v___x_738_ = lean_apply_2(v_toPure_731_, lean_box(0), v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_constName_742_){
_start:
{
lean_object* v_toApplicative_743_; lean_object* v_toBind_744_; lean_object* v_toPure_745_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v_toApplicative_743_ = lean_ctor_get(v_inst_739_, 0);
v_toBind_744_ = lean_ctor_get(v_inst_739_, 1);
lean_inc(v_toBind_744_);
v_toPure_745_ = lean_ctor_get(v_toApplicative_743_, 1);
lean_inc(v_toPure_745_);
lean_inc(v_constName_742_);
v___x_746_ = l_Lean_getConstVal___redArg(v_inst_739_, v_inst_740_, v_inst_741_, v_constName_742_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_mkConstWithLevelParams___redArg___lam__0), 3, 2);
lean_closure_set(v___f_747_, 0, v_constName_742_);
lean_closure_set(v___f_747_, 1, v_toPure_745_);
v___x_748_ = lean_apply_4(v_toBind_744_, lean_box(0), lean_box(0), v___x_746_, v___f_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object* v_m_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_constName_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_750_, v_inst_751_, v_inst_752_, v_constName_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg___lam__0(lean_object* v_constName_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_toPure_764_, lean_object* v_____do__lift_765_){
_start:
{
if (lean_obj_tag(v_____do__lift_765_) == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v_toPure_764_);
v___x_766_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_767_ = 0;
v___x_768_ = l_Lean_MessageData_ofConstName(v_constName_761_, v___x_767_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_766_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__3, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_throwError___redArg(v_inst_762_, v_inst_763_, v___x_771_);
return v___x_772_;
}
else
{
lean_object* v_val_773_; lean_object* v___x_774_; 
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
lean_dec(v_constName_761_);
v_val_773_ = lean_ctor_get(v_____do__lift_765_, 0);
lean_inc(v_val_773_);
lean_dec_ref(v_____do__lift_765_);
v___x_774_ = lean_apply_2(v_toPure_764_, lean_box(0), v_val_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg(lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_constName_778_){
_start:
{
lean_object* v_toApplicative_779_; lean_object* v_toBind_780_; lean_object* v_getEnv_781_; lean_object* v_toPure_782_; lean_object* v___x_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_toApplicative_779_ = lean_ctor_get(v_inst_775_, 0);
v_toBind_780_ = lean_ctor_get(v_inst_775_, 1);
lean_inc(v_toBind_780_);
v_getEnv_781_ = lean_ctor_get(v_inst_776_, 0);
lean_inc(v_getEnv_781_);
lean_dec_ref(v_inst_776_);
v_toPure_782_ = lean_ctor_get(v_toApplicative_779_, 1);
lean_inc(v_toPure_782_);
v___x_783_ = lean_box(0);
lean_inc(v_toPure_782_);
lean_inc_ref(v_inst_775_);
lean_inc(v_constName_778_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_getConstInfoDefn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_784_, 0, v_constName_778_);
lean_closure_set(v___f_784_, 1, v_inst_775_);
lean_closure_set(v___f_784_, 2, v_inst_777_);
lean_closure_set(v___f_784_, 3, v_toPure_782_);
v___x_785_ = l_instInhabitedOfMonad___redArg(v_inst_775_, v___x_783_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_isDefn_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_786_, 0, v_toPure_782_);
lean_closure_set(v___f_786_, 1, v_constName_778_);
lean_closure_set(v___f_786_, 2, v___x_785_);
lean_inc(v_toBind_780_);
v___x_787_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v_getEnv_781_, v___f_786_);
v___x_788_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v___x_787_, v___f_784_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object* v_m_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_constName_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_getConstInfoDefn___redArg(v_inst_790_, v_inst_791_, v_inst_792_, v_constName_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__0(lean_object* v_constName_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_toPure_801_, lean_object* v_____do__lift_802_){
_start:
{
if (lean_obj_tag(v_____do__lift_802_) == 0)
{
lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_toPure_801_);
v___x_803_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_804_ = 0;
v___x_805_ = l_Lean_MessageData_ofConstName(v_constName_798_, v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_obj_once(&l_Lean_getConstInfoInduct___redArg___lam__0___closed__1, &l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwError___redArg(v_inst_799_, v_inst_800_, v___x_808_);
return v___x_809_;
}
else
{
lean_object* v_val_810_; lean_object* v___x_811_; 
lean_dec_ref(v_inst_800_);
lean_dec_ref(v_inst_799_);
lean_dec(v_constName_798_);
v_val_810_ = lean_ctor_get(v_____do__lift_802_, 0);
lean_inc(v_val_810_);
lean_dec_ref(v_____do__lift_802_);
v___x_811_ = lean_apply_2(v_toPure_801_, lean_box(0), v_val_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__1(lean_object* v_constName_812_, lean_object* v_toPure_813_, lean_object* v_____do__lift_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = l_Lean_isInductiveCore_x3f(v_____do__lift_814_, v_constName_812_);
v___x_816_ = lean_apply_2(v_toPure_813_, lean_box(0), v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_constName_820_){
_start:
{
lean_object* v_toApplicative_821_; lean_object* v_toBind_822_; lean_object* v_getEnv_823_; lean_object* v_toPure_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_toApplicative_821_ = lean_ctor_get(v_inst_817_, 0);
v_toBind_822_ = lean_ctor_get(v_inst_817_, 1);
lean_inc(v_toBind_822_);
v_getEnv_823_ = lean_ctor_get(v_inst_818_, 0);
lean_inc(v_getEnv_823_);
lean_dec_ref(v_inst_818_);
v_toPure_824_ = lean_ctor_get(v_toApplicative_821_, 1);
lean_inc(v_toPure_824_);
lean_inc(v_toPure_824_);
lean_inc(v_constName_820_);
v___f_825_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_825_, 0, v_constName_820_);
lean_closure_set(v___f_825_, 1, v_inst_817_);
lean_closure_set(v___f_825_, 2, v_inst_819_);
lean_closure_set(v___f_825_, 3, v_toPure_824_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__1), 3, 2);
lean_closure_set(v___f_826_, 0, v_constName_820_);
lean_closure_set(v___f_826_, 1, v_toPure_824_);
lean_inc(v_toBind_822_);
v___x_827_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v_getEnv_823_, v___f_826_);
v___x_828_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v___x_827_, v___f_825_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object* v_m_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_constName_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_getConstInfoInduct___redArg(v_inst_830_, v_inst_831_, v_inst_832_, v_constName_833_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg___lam__0(lean_object* v_constName_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_toPure_841_, lean_object* v_____do__lift_842_){
_start:
{
if (lean_obj_tag(v_____do__lift_842_) == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v_toPure_841_);
v___x_843_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_844_ = 0;
v___x_845_ = l_Lean_MessageData_ofConstName(v_constName_838_, v___x_844_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_843_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_obj_once(&l_Lean_getConstInfoCtor___redArg___lam__0___closed__1, &l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_throwError___redArg(v_inst_839_, v_inst_840_, v___x_848_);
return v___x_849_;
}
else
{
lean_object* v_val_850_; lean_object* v___x_851_; 
lean_dec_ref(v_inst_840_);
lean_dec_ref(v_inst_839_);
lean_dec(v_constName_838_);
v_val_850_ = lean_ctor_get(v_____do__lift_842_, 0);
lean_inc(v_val_850_);
lean_dec_ref(v_____do__lift_842_);
v___x_851_ = lean_apply_2(v_toPure_841_, lean_box(0), v_val_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg(lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_constName_855_){
_start:
{
lean_object* v_toApplicative_856_; lean_object* v_toBind_857_; lean_object* v_getEnv_858_; lean_object* v_toPure_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_toApplicative_856_ = lean_ctor_get(v_inst_852_, 0);
v_toBind_857_ = lean_ctor_get(v_inst_852_, 1);
lean_inc(v_toBind_857_);
v_getEnv_858_ = lean_ctor_get(v_inst_853_, 0);
lean_inc(v_getEnv_858_);
lean_dec_ref(v_inst_853_);
v_toPure_859_ = lean_ctor_get(v_toApplicative_856_, 1);
lean_inc(v_toPure_859_);
v___x_860_ = lean_box(0);
lean_inc(v_toPure_859_);
lean_inc_ref(v_inst_852_);
lean_inc(v_constName_855_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_getConstInfoCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_861_, 0, v_constName_855_);
lean_closure_set(v___f_861_, 1, v_inst_852_);
lean_closure_set(v___f_861_, 2, v_inst_854_);
lean_closure_set(v___f_861_, 3, v_toPure_859_);
v___x_862_ = l_instInhabitedOfMonad___redArg(v_inst_852_, v___x_860_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_isCtor_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_863_, 0, v_toPure_859_);
lean_closure_set(v___f_863_, 1, v_constName_855_);
lean_closure_set(v___f_863_, 2, v___x_862_);
lean_inc(v_toBind_857_);
v___x_864_ = lean_apply_4(v_toBind_857_, lean_box(0), lean_box(0), v_getEnv_858_, v___f_863_);
v___x_865_ = lean_apply_4(v_toBind_857_, lean_box(0), lean_box(0), v___x_864_, v___f_861_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object* v_m_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_constName_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_getConstInfoCtor___redArg(v_inst_867_, v_inst_868_, v_inst_869_, v_constName_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_getConstInfoRec___redArg___lam__0___closed__0));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg___lam__0(lean_object* v_constName_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_toPure_878_, lean_object* v_____do__lift_879_){
_start:
{
if (lean_obj_tag(v_____do__lift_879_) == 0)
{
lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v_toPure_878_);
v___x_880_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_881_ = 0;
v___x_882_ = l_Lean_MessageData_ofConstName(v_constName_875_, v___x_881_);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_880_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_obj_once(&l_Lean_getConstInfoRec___redArg___lam__0___closed__1, &l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_throwError___redArg(v_inst_876_, v_inst_877_, v___x_885_);
return v___x_886_;
}
else
{
lean_object* v_val_887_; lean_object* v___x_888_; 
lean_dec_ref(v_inst_877_);
lean_dec_ref(v_inst_876_);
lean_dec(v_constName_875_);
v_val_887_ = lean_ctor_get(v_____do__lift_879_, 0);
lean_inc(v_val_887_);
lean_dec_ref(v_____do__lift_879_);
v___x_888_ = lean_apply_2(v_toPure_878_, lean_box(0), v_val_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg(lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_constName_892_){
_start:
{
lean_object* v_toApplicative_893_; lean_object* v_toBind_894_; lean_object* v_getEnv_895_; lean_object* v_toPure_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toApplicative_893_ = lean_ctor_get(v_inst_889_, 0);
v_toBind_894_ = lean_ctor_get(v_inst_889_, 1);
lean_inc(v_toBind_894_);
v_getEnv_895_ = lean_ctor_get(v_inst_890_, 0);
lean_inc(v_getEnv_895_);
lean_dec_ref(v_inst_890_);
v_toPure_896_ = lean_ctor_get(v_toApplicative_893_, 1);
lean_inc(v_toPure_896_);
v___x_897_ = lean_box(0);
lean_inc(v_toPure_896_);
lean_inc_ref(v_inst_889_);
lean_inc(v_constName_892_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_getConstInfoRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_898_, 0, v_constName_892_);
lean_closure_set(v___f_898_, 1, v_inst_889_);
lean_closure_set(v___f_898_, 2, v_inst_891_);
lean_closure_set(v___f_898_, 3, v_toPure_896_);
v___x_899_ = l_instInhabitedOfMonad___redArg(v_inst_889_, v___x_897_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_isRec_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_900_, 0, v_toPure_896_);
lean_closure_set(v___f_900_, 1, v_constName_892_);
lean_closure_set(v___f_900_, 2, v___x_899_);
lean_inc(v_toBind_894_);
v___x_901_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v_getEnv_895_, v___f_900_);
v___x_902_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v___x_901_, v___f_898_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object* v_m_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_constName_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_getConstInfoRec___redArg(v_inst_904_, v_inst_905_, v_inst_906_, v_constName_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__0(lean_object* v_k_909_, lean_object* v_val_910_, lean_object* v_us_911_, lean_object* v_failK_912_, lean_object* v_____do__lift_913_){
_start:
{
if (lean_obj_tag(v_____do__lift_913_) == 6)
{
lean_object* v_val_914_; lean_object* v___x_915_; 
lean_dec(v_failK_912_);
v_val_914_ = lean_ctor_get(v_____do__lift_913_, 0);
lean_inc_ref(v_val_914_);
lean_dec_ref(v_____do__lift_913_);
v___x_915_ = lean_apply_3(v_k_909_, v_val_910_, v_us_911_, v_val_914_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_____do__lift_913_);
lean_dec(v_us_911_);
lean_dec_ref(v_val_910_);
lean_dec(v_k_909_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_apply_1(v_failK_912_, v___x_916_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__1(lean_object* v_declName_918_, lean_object* v_failK_919_, lean_object* v_k_920_, lean_object* v_us_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_toBind_925_, lean_object* v_____do__lift_926_){
_start:
{
uint8_t v___x_930_; lean_object* v___x_931_; 
v___x_930_ = 0;
v___x_931_ = l_Lean_Environment_find_x3f(v_____do__lift_926_, v_declName_918_, v___x_930_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_toBind_925_);
lean_dec_ref(v_inst_924_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_dec(v_us_921_);
lean_dec(v_k_920_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_apply_1(v_failK_919_, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v_val_934_; 
v_val_934_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_val_934_);
lean_dec_ref(v___x_931_);
if (lean_obj_tag(v_val_934_) == 5)
{
lean_object* v_val_935_; lean_object* v_ctors_936_; 
v_val_935_ = lean_ctor_get(v_val_934_, 0);
lean_inc_ref(v_val_935_);
lean_dec_ref(v_val_934_);
v_ctors_936_ = lean_ctor_get(v_val_935_, 4);
if (lean_obj_tag(v_ctors_936_) == 1)
{
lean_object* v_tail_937_; 
v_tail_937_ = lean_ctor_get(v_ctors_936_, 1);
if (lean_obj_tag(v_tail_937_) == 0)
{
lean_object* v_head_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_head_938_ = lean_ctor_get(v_ctors_936_, 0);
lean_inc(v_head_938_);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(v___f_939_, 0, v_k_920_);
lean_closure_set(v___f_939_, 1, v_val_935_);
lean_closure_set(v___f_939_, 2, v_us_921_);
lean_closure_set(v___f_939_, 3, v_failK_919_);
v___x_940_ = l_Lean_getConstInfo___redArg(v_inst_922_, v_inst_923_, v_inst_924_, v_head_938_);
v___x_941_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_940_, v___f_939_);
return v___x_941_;
}
else
{
lean_dec_ref(v_val_935_);
lean_dec(v_toBind_925_);
lean_dec_ref(v_inst_924_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_dec(v_us_921_);
lean_dec(v_k_920_);
goto v___jp_927_;
}
}
else
{
lean_dec_ref(v_val_935_);
lean_dec(v_toBind_925_);
lean_dec_ref(v_inst_924_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_dec(v_us_921_);
lean_dec(v_k_920_);
goto v___jp_927_;
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_val_934_);
lean_dec(v_toBind_925_);
lean_dec_ref(v_inst_924_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_dec(v_us_921_);
lean_dec(v_k_920_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_1(v_failK_919_, v___x_942_);
return v___x_943_;
}
}
v___jp_927_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_box(0);
v___x_929_ = lean_apply_1(v_failK_919_, v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg(lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_e_947_, lean_object* v_failK_948_, lean_object* v_k_949_){
_start:
{
if (lean_obj_tag(v_e_947_) == 4)
{
lean_object* v_toBind_950_; lean_object* v_declName_951_; lean_object* v_us_952_; lean_object* v_getEnv_953_; lean_object* v___f_954_; lean_object* v___x_955_; 
v_toBind_950_ = lean_ctor_get(v_inst_944_, 1);
lean_inc(v_toBind_950_);
v_declName_951_ = lean_ctor_get(v_e_947_, 0);
lean_inc(v_declName_951_);
v_us_952_ = lean_ctor_get(v_e_947_, 1);
lean_inc(v_us_952_);
lean_dec_ref(v_e_947_);
v_getEnv_953_ = lean_ctor_get(v_inst_945_, 0);
lean_inc(v_getEnv_953_);
lean_inc(v_toBind_950_);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_954_, 0, v_declName_951_);
lean_closure_set(v___f_954_, 1, v_failK_948_);
lean_closure_set(v___f_954_, 2, v_k_949_);
lean_closure_set(v___f_954_, 3, v_us_952_);
lean_closure_set(v___f_954_, 4, v_inst_944_);
lean_closure_set(v___f_954_, 5, v_inst_945_);
lean_closure_set(v___f_954_, 6, v_inst_946_);
lean_closure_set(v___f_954_, 7, v_toBind_950_);
v___x_955_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v_getEnv_953_, v___f_954_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_k_949_);
lean_dec_ref(v_e_947_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_apply_1(v_failK_948_, v___x_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure(lean_object* v_m_958_, lean_object* v_00_u03b1_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_e_963_, lean_object* v_failK_964_, lean_object* v_k_965_){
_start:
{
if (lean_obj_tag(v_e_963_) == 4)
{
lean_object* v_toBind_966_; lean_object* v_declName_967_; lean_object* v_us_968_; lean_object* v_getEnv_969_; lean_object* v___f_970_; lean_object* v___x_971_; 
v_toBind_966_ = lean_ctor_get(v_inst_960_, 1);
lean_inc(v_toBind_966_);
v_declName_967_ = lean_ctor_get(v_e_963_, 0);
lean_inc(v_declName_967_);
v_us_968_ = lean_ctor_get(v_e_963_, 1);
lean_inc(v_us_968_);
lean_dec_ref(v_e_963_);
v_getEnv_969_ = lean_ctor_get(v_inst_961_, 0);
lean_inc(v_getEnv_969_);
lean_inc(v_toBind_966_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_970_, 0, v_declName_967_);
lean_closure_set(v___f_970_, 1, v_failK_964_);
lean_closure_set(v___f_970_, 2, v_k_965_);
lean_closure_set(v___f_970_, 3, v_us_968_);
lean_closure_set(v___f_970_, 4, v_inst_960_);
lean_closure_set(v___f_970_, 5, v_inst_961_);
lean_closure_set(v___f_970_, 6, v_inst_962_);
lean_closure_set(v___f_970_, 7, v_toBind_966_);
v___x_971_ = lean_apply_4(v_toBind_966_, lean_box(0), lean_box(0), v_getEnv_969_, v___f_970_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_k_965_);
lean_dec_ref(v_e_963_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_apply_1(v_failK_964_, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg___lam__1(lean_object* v_declName_974_, lean_object* v_failK_975_, lean_object* v_k_976_, lean_object* v_us_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_toBind_981_, lean_object* v_____do__lift_982_){
_start:
{
uint8_t v___x_989_; lean_object* v___x_990_; 
v___x_989_ = 0;
v___x_990_ = l_Lean_Environment_find_x3f(v_____do__lift_982_, v_declName_974_, v___x_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec(v_toBind_981_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_us_977_);
lean_dec(v_k_976_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_apply_1(v_failK_975_, v___x_991_);
return v___x_992_;
}
else
{
lean_object* v_val_993_; 
v_val_993_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_993_);
lean_dec_ref(v___x_990_);
if (lean_obj_tag(v_val_993_) == 5)
{
lean_object* v_val_994_; uint8_t v_isRec_995_; 
v_val_994_ = lean_ctor_get(v_val_993_, 0);
lean_inc_ref(v_val_994_);
lean_dec_ref(v_val_993_);
v_isRec_995_ = lean_ctor_get_uint8(v_val_994_, sizeof(void*)*6);
if (v_isRec_995_ == 0)
{
lean_object* v_numIndices_996_; lean_object* v_ctors_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_numIndices_996_ = lean_ctor_get(v_val_994_, 2);
v_ctors_997_ = lean_ctor_get(v_val_994_, 4);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_nat_dec_eq(v_numIndices_996_, v___x_998_);
if (v___x_999_ == 0)
{
lean_dec_ref(v_val_994_);
lean_dec(v_toBind_981_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_us_977_);
lean_dec(v_k_976_);
goto v___jp_983_;
}
else
{
if (lean_obj_tag(v_ctors_997_) == 1)
{
lean_object* v_tail_1000_; 
v_tail_1000_ = lean_ctor_get(v_ctors_997_, 1);
if (lean_obj_tag(v_tail_1000_) == 0)
{
lean_object* v_head_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_head_1001_ = lean_ctor_get(v_ctors_997_, 0);
lean_inc(v_head_1001_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1002_, 0, v_k_976_);
lean_closure_set(v___f_1002_, 1, v_val_994_);
lean_closure_set(v___f_1002_, 2, v_us_977_);
lean_closure_set(v___f_1002_, 3, v_failK_975_);
v___x_1003_ = l_Lean_getConstInfo___redArg(v_inst_978_, v_inst_979_, v_inst_980_, v_head_1001_);
v___x_1004_ = lean_apply_4(v_toBind_981_, lean_box(0), lean_box(0), v___x_1003_, v___f_1002_);
return v___x_1004_;
}
else
{
lean_dec_ref(v_val_994_);
lean_dec(v_toBind_981_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_us_977_);
lean_dec(v_k_976_);
goto v___jp_986_;
}
}
else
{
lean_dec_ref(v_val_994_);
lean_dec(v_toBind_981_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_us_977_);
lean_dec(v_k_976_);
goto v___jp_986_;
}
}
}
else
{
lean_dec_ref(v_val_994_);
lean_dec(v_toBind_981_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_us_977_);
lean_dec(v_k_976_);
goto v___jp_983_;
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec(v_val_993_);
lean_dec(v_toBind_981_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_us_977_);
lean_dec(v_k_976_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_apply_1(v_failK_975_, v___x_1005_);
return v___x_1006_;
}
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_box(0);
v___x_985_ = lean_apply_1(v_failK_975_, v___x_984_);
return v___x_985_;
}
v___jp_986_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_1(v_failK_975_, v___x_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg(lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_e_1010_, lean_object* v_failK_1011_, lean_object* v_k_1012_){
_start:
{
if (lean_obj_tag(v_e_1010_) == 4)
{
lean_object* v_toBind_1013_; lean_object* v_declName_1014_; lean_object* v_us_1015_; lean_object* v_getEnv_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v_toBind_1013_ = lean_ctor_get(v_inst_1007_, 1);
lean_inc(v_toBind_1013_);
v_declName_1014_ = lean_ctor_get(v_e_1010_, 0);
lean_inc(v_declName_1014_);
v_us_1015_ = lean_ctor_get(v_e_1010_, 1);
lean_inc(v_us_1015_);
lean_dec_ref(v_e_1010_);
v_getEnv_1016_ = lean_ctor_get(v_inst_1008_, 0);
lean_inc(v_getEnv_1016_);
lean_inc(v_toBind_1013_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_matchConstNonRecStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1017_, 0, v_declName_1014_);
lean_closure_set(v___f_1017_, 1, v_failK_1011_);
lean_closure_set(v___f_1017_, 2, v_k_1012_);
lean_closure_set(v___f_1017_, 3, v_us_1015_);
lean_closure_set(v___f_1017_, 4, v_inst_1007_);
lean_closure_set(v___f_1017_, 5, v_inst_1008_);
lean_closure_set(v___f_1017_, 6, v_inst_1009_);
lean_closure_set(v___f_1017_, 7, v_toBind_1013_);
v___x_1018_ = lean_apply_4(v_toBind_1013_, lean_box(0), lean_box(0), v_getEnv_1016_, v___f_1017_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_k_1012_);
lean_dec_ref(v_e_1010_);
lean_dec_ref(v_inst_1009_);
lean_dec_ref(v_inst_1008_);
lean_dec_ref(v_inst_1007_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_apply_1(v_failK_1011_, v___x_1019_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure(lean_object* v_m_1021_, lean_object* v_00_u03b1_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_e_1026_, lean_object* v_failK_1027_, lean_object* v_k_1028_){
_start:
{
if (lean_obj_tag(v_e_1026_) == 4)
{
lean_object* v_toBind_1029_; lean_object* v_declName_1030_; lean_object* v_us_1031_; lean_object* v_getEnv_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
v_toBind_1029_ = lean_ctor_get(v_inst_1023_, 1);
lean_inc(v_toBind_1029_);
v_declName_1030_ = lean_ctor_get(v_e_1026_, 0);
lean_inc(v_declName_1030_);
v_us_1031_ = lean_ctor_get(v_e_1026_, 1);
lean_inc(v_us_1031_);
lean_dec_ref(v_e_1026_);
v_getEnv_1032_ = lean_ctor_get(v_inst_1024_, 0);
lean_inc(v_getEnv_1032_);
lean_inc(v_toBind_1029_);
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
LEAN_EXPORT lean_object* l_Lean_hasCompileError___boxed(lean_object* v_env_1039_, lean_object* v_constName_1040_){
_start:
{
uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_res_1041_ = lean_has_compile_error(v_env_1039_, v_constName_1040_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0(lean_object* v_____do__lift_1043_, lean_object* v_constName_1044_, uint8_t v_checkMeta_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v___x_1048_, lean_object* v_____do__lift_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = l_Lean_Environment_evalConst___redArg(v_____do__lift_1043_, v_____do__lift_1049_, v_constName_1044_, v_checkMeta_1045_);
v___x_1051_ = l_Lean_ofExcept___redArg(v_inst_1046_, v_inst_1047_, v___x_1048_, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0___boxed(lean_object* v_____do__lift_1052_, lean_object* v_constName_1053_, lean_object* v_checkMeta_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v___x_1057_, lean_object* v_____do__lift_1058_){
_start:
{
uint8_t v_checkMeta_boxed_1059_; lean_object* v_res_1060_; 
v_checkMeta_boxed_1059_ = lean_unbox(v_checkMeta_1054_);
v_res_1060_ = l_Lean_evalConst___redArg___lam__0(v_____do__lift_1052_, v_constName_1053_, v_checkMeta_boxed_1059_, v_inst_1055_, v_inst_1056_, v___x_1057_, v_____do__lift_1058_);
lean_dec_ref(v_____do__lift_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1(lean_object* v_constName_1061_, uint8_t v_checkMeta_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v___x_1065_, lean_object* v_toBind_1066_, lean_object* v_inst_1067_, lean_object* v_____do__lift_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_box(v_checkMeta_1062_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1070_, 0, v_____do__lift_1068_);
lean_closure_set(v___f_1070_, 1, v_constName_1061_);
lean_closure_set(v___f_1070_, 2, v___x_1069_);
lean_closure_set(v___f_1070_, 3, v_inst_1063_);
lean_closure_set(v___f_1070_, 4, v_inst_1064_);
lean_closure_set(v___f_1070_, 5, v___x_1065_);
v___x_1071_ = lean_apply_4(v_toBind_1066_, lean_box(0), lean_box(0), v_inst_1067_, v___f_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1___boxed(lean_object* v_constName_1072_, lean_object* v_checkMeta_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v___x_1076_, lean_object* v_toBind_1077_, lean_object* v_inst_1078_, lean_object* v_____do__lift_1079_){
_start:
{
uint8_t v_checkMeta_boxed_1080_; lean_object* v_res_1081_; 
v_checkMeta_boxed_1080_ = lean_unbox(v_checkMeta_1073_);
v_res_1081_ = l_Lean_evalConst___redArg___lam__1(v_constName_1072_, v_checkMeta_boxed_1080_, v_inst_1074_, v_inst_1075_, v___x_1076_, v_toBind_1077_, v_inst_1078_, v_____do__lift_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__2(lean_object* v_toBind_1082_, lean_object* v_getEnv_1083_, lean_object* v___f_1084_, lean_object* v_____r_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v_getEnv_1083_, v___f_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__3(lean_object* v_constName_1087_, lean_object* v_toBind_1088_, lean_object* v_getEnv_1089_, lean_object* v___f_1090_, lean_object* v_inst_1091_, lean_object* v___f_1092_, lean_object* v_____do__lift_1093_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_has_compile_error(v_____do__lift_1093_, v_constName_1087_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v___f_1092_);
lean_dec_ref(v_inst_1091_);
v___x_1095_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v_getEnv_1089_, v___f_1090_);
return v___x_1095_;
}
else
{
lean_object* v_toMonadExceptOf_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v___f_1090_);
lean_dec(v_getEnv_1089_);
v_toMonadExceptOf_1096_ = lean_ctor_get(v_inst_1091_, 0);
lean_inc_ref(v_toMonadExceptOf_1096_);
lean_dec_ref(v_inst_1091_);
v___x_1097_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_1096_);
v___x_1098_ = l_Lean_Elab_throwAbortCommand___redArg(v___x_1097_);
v___x_1099_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1098_, v___f_1092_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg(lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_constName_1105_, uint8_t v_checkMeta_1106_){
_start:
{
lean_object* v_toBind_1107_; lean_object* v_getEnv_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; 
v_toBind_1107_ = lean_ctor_get(v_inst_1101_, 1);
lean_inc(v_toBind_1107_);
v_getEnv_1108_ = lean_ctor_get(v_inst_1102_, 0);
lean_inc(v_getEnv_1108_);
lean_dec_ref(v_inst_1102_);
v___x_1109_ = ((lean_object*)(l_Lean_evalConst___redArg___closed__0));
v___x_1110_ = lean_box(v_checkMeta_1106_);
lean_inc(v_toBind_1107_);
lean_inc_ref(v_inst_1103_);
lean_inc(v_constName_1105_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1111_, 0, v_constName_1105_);
lean_closure_set(v___f_1111_, 1, v___x_1110_);
lean_closure_set(v___f_1111_, 2, v_inst_1101_);
lean_closure_set(v___f_1111_, 3, v_inst_1103_);
lean_closure_set(v___f_1111_, 4, v___x_1109_);
lean_closure_set(v___f_1111_, 5, v_toBind_1107_);
lean_closure_set(v___f_1111_, 6, v_inst_1104_);
lean_inc_ref(v___f_1111_);
lean_inc(v_getEnv_1108_);
lean_inc(v_toBind_1107_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1112_, 0, v_toBind_1107_);
lean_closure_set(v___f_1112_, 1, v_getEnv_1108_);
lean_closure_set(v___f_1112_, 2, v___f_1111_);
lean_inc(v_getEnv_1108_);
lean_inc(v_toBind_1107_);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1113_, 0, v_constName_1105_);
lean_closure_set(v___f_1113_, 1, v_toBind_1107_);
lean_closure_set(v___f_1113_, 2, v_getEnv_1108_);
lean_closure_set(v___f_1113_, 3, v___f_1111_);
lean_closure_set(v___f_1113_, 4, v_inst_1103_);
lean_closure_set(v___f_1113_, 5, v___f_1112_);
v___x_1114_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v_getEnv_1108_, v___f_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___boxed(lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_constName_1119_, lean_object* v_checkMeta_1120_){
_start:
{
uint8_t v_checkMeta_boxed_1121_; lean_object* v_res_1122_; 
v_checkMeta_boxed_1121_ = lean_unbox(v_checkMeta_1120_);
v_res_1122_ = l_Lean_evalConst___redArg(v_inst_1115_, v_inst_1116_, v_inst_1117_, v_inst_1118_, v_constName_1119_, v_checkMeta_boxed_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object* v_m_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_00_u03b1_1128_, lean_object* v_constName_1129_, uint8_t v_checkMeta_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_evalConst___redArg(v_inst_1124_, v_inst_1125_, v_inst_1126_, v_inst_1127_, v_constName_1129_, v_checkMeta_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___boxed(lean_object* v_m_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_00_u03b1_1137_, lean_object* v_constName_1138_, lean_object* v_checkMeta_1139_){
_start:
{
uint8_t v_checkMeta_boxed_1140_; lean_object* v_res_1141_; 
v_checkMeta_boxed_1140_ = lean_unbox(v_checkMeta_1139_);
v_res_1141_ = l_Lean_evalConst(v_m_1132_, v_inst_1133_, v_inst_1134_, v_inst_1135_, v_inst_1136_, v_00_u03b1_1137_, v_constName_1138_, v_checkMeta_boxed_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0(lean_object* v_____do__lift_1142_, lean_object* v_typeName_1143_, lean_object* v_constName_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v___x_1147_, lean_object* v_____do__lift_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_1142_, v_____do__lift_1148_, v_typeName_1143_, v_constName_1144_);
v___x_1150_ = l_Lean_ofExcept___redArg(v_inst_1145_, v_inst_1146_, v___x_1147_, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0___boxed(lean_object* v_____do__lift_1151_, lean_object* v_typeName_1152_, lean_object* v_constName_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v___x_1156_, lean_object* v_____do__lift_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_evalConstCheck___redArg___lam__0(v_____do__lift_1151_, v_typeName_1152_, v_constName_1153_, v_inst_1154_, v_inst_1155_, v___x_1156_, v_____do__lift_1157_);
lean_dec_ref(v_____do__lift_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__1(lean_object* v_typeName_1159_, lean_object* v_constName_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v___x_1163_, lean_object* v_toBind_1164_, lean_object* v_inst_1165_, lean_object* v_____do__lift_1166_){
_start:
{
lean_object* v___f_1167_; lean_object* v___x_1168_; 
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1167_, 0, v_____do__lift_1166_);
lean_closure_set(v___f_1167_, 1, v_typeName_1159_);
lean_closure_set(v___f_1167_, 2, v_constName_1160_);
lean_closure_set(v___f_1167_, 3, v_inst_1161_);
lean_closure_set(v___f_1167_, 4, v_inst_1162_);
lean_closure_set(v___f_1167_, 5, v___x_1163_);
v___x_1168_ = lean_apply_4(v_toBind_1164_, lean_box(0), lean_box(0), v_inst_1165_, v___f_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_typeName_1173_, lean_object* v_constName_1174_){
_start:
{
lean_object* v_toBind_1175_; lean_object* v_getEnv_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; 
v_toBind_1175_ = lean_ctor_get(v_inst_1169_, 1);
lean_inc(v_toBind_1175_);
v_getEnv_1176_ = lean_ctor_get(v_inst_1170_, 0);
lean_inc(v_getEnv_1176_);
lean_dec_ref(v_inst_1170_);
v___x_1177_ = ((lean_object*)(l_Lean_evalConst___redArg___closed__0));
lean_inc(v_toBind_1175_);
lean_inc_ref(v_inst_1171_);
lean_inc(v_constName_1174_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1178_, 0, v_typeName_1173_);
lean_closure_set(v___f_1178_, 1, v_constName_1174_);
lean_closure_set(v___f_1178_, 2, v_inst_1169_);
lean_closure_set(v___f_1178_, 3, v_inst_1171_);
lean_closure_set(v___f_1178_, 4, v___x_1177_);
lean_closure_set(v___f_1178_, 5, v_toBind_1175_);
lean_closure_set(v___f_1178_, 6, v_inst_1172_);
lean_inc_ref(v___f_1178_);
lean_inc(v_getEnv_1176_);
lean_inc(v_toBind_1175_);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1179_, 0, v_toBind_1175_);
lean_closure_set(v___f_1179_, 1, v_getEnv_1176_);
lean_closure_set(v___f_1179_, 2, v___f_1178_);
lean_inc(v_getEnv_1176_);
lean_inc(v_toBind_1175_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1180_, 0, v_constName_1174_);
lean_closure_set(v___f_1180_, 1, v_toBind_1175_);
lean_closure_set(v___f_1180_, 2, v_getEnv_1176_);
lean_closure_set(v___f_1180_, 3, v___f_1178_);
lean_closure_set(v___f_1180_, 4, v_inst_1171_);
lean_closure_set(v___f_1180_, 5, v___f_1179_);
v___x_1181_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v_getEnv_1176_, v___f_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object* v_m_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_00_u03b1_1187_, lean_object* v_typeName_1188_, lean_object* v_constName_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_evalConstCheck___redArg(v_inst_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_, v_typeName_1188_, v_constName_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0(lean_object* v___x_1191_, lean_object* v_val_1192_, lean_object* v_toPure_1193_, lean_object* v_____do__lift_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = l_Lean_Environment_allImportedModuleNames(v_____do__lift_1194_);
v___x_1196_ = lean_array_get(v___x_1191_, v___x_1195_, v_val_1192_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
v___x_1198_ = lean_apply_2(v_toPure_1193_, lean_box(0), v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(lean_object* v___x_1199_, lean_object* v_val_1200_, lean_object* v_toPure_1201_, lean_object* v_____do__lift_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_findModuleOf_x3f___redArg___lam__0(v___x_1199_, v_val_1200_, v_toPure_1201_, v_____do__lift_1202_);
lean_dec_ref(v_____do__lift_1202_);
lean_dec(v_val_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1(lean_object* v_declName_1204_, lean_object* v_toPure_1205_, lean_object* v___x_1206_, lean_object* v_toBind_1207_, lean_object* v_getEnv_1208_, lean_object* v_____do__lift_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1209_, v_declName_1204_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec(v_getEnv_1208_);
lean_dec(v_toBind_1207_);
lean_dec(v___x_1206_);
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_apply_2(v_toPure_1205_, lean_box(0), v___x_1211_);
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; 
v_val_1213_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1210_);
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1214_, 0, v___x_1206_);
lean_closure_set(v___f_1214_, 1, v_val_1213_);
lean_closure_set(v___f_1214_, 2, v_toPure_1205_);
v___x_1215_ = lean_apply_4(v_toBind_1207_, lean_box(0), lean_box(0), v_getEnv_1208_, v___f_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(lean_object* v_declName_1216_, lean_object* v_toPure_1217_, lean_object* v___x_1218_, lean_object* v_toBind_1219_, lean_object* v_getEnv_1220_, lean_object* v_____do__lift_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_findModuleOf_x3f___redArg___lam__1(v_declName_1216_, v_toPure_1217_, v___x_1218_, v_toBind_1219_, v_getEnv_1220_, v_____do__lift_1221_);
lean_dec_ref(v_____do__lift_1221_);
lean_dec(v_declName_1216_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__2(lean_object* v_inst_1223_, lean_object* v_declName_1224_, lean_object* v_toPure_1225_, lean_object* v___x_1226_, lean_object* v_toBind_1227_, lean_object* v_____r_1228_){
_start:
{
lean_object* v_getEnv_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; 
v_getEnv_1229_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc(v_getEnv_1229_);
lean_dec_ref(v_inst_1223_);
lean_inc(v_getEnv_1229_);
lean_inc(v_toBind_1227_);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1230_, 0, v_declName_1224_);
lean_closure_set(v___f_1230_, 1, v_toPure_1225_);
lean_closure_set(v___f_1230_, 2, v___x_1226_);
lean_closure_set(v___f_1230_, 3, v_toBind_1227_);
lean_closure_set(v___f_1230_, 4, v_getEnv_1229_);
v___x_1231_ = lean_apply_4(v_toBind_1227_, lean_box(0), lean_box(0), v_getEnv_1229_, v___f_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg(lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_declName_1235_){
_start:
{
lean_object* v_toApplicative_1236_; lean_object* v_toFunctor_1237_; lean_object* v_toBind_1238_; lean_object* v_toPure_1239_; lean_object* v_mapConst_1240_; lean_object* v___x_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_toApplicative_1236_ = lean_ctor_get(v_inst_1232_, 0);
v_toFunctor_1237_ = lean_ctor_get(v_toApplicative_1236_, 0);
v_toBind_1238_ = lean_ctor_get(v_inst_1232_, 1);
lean_inc(v_toBind_1238_);
v_toPure_1239_ = lean_ctor_get(v_toApplicative_1236_, 1);
v_mapConst_1240_ = lean_ctor_get(v_toFunctor_1237_, 1);
lean_inc(v_mapConst_1240_);
v___x_1241_ = lean_box(0);
lean_inc(v_toBind_1238_);
lean_inc(v_toPure_1239_);
lean_inc(v_declName_1235_);
lean_inc_ref(v_inst_1233_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1242_, 0, v_inst_1233_);
lean_closure_set(v___f_1242_, 1, v_declName_1235_);
lean_closure_set(v___f_1242_, 2, v_toPure_1239_);
lean_closure_set(v___f_1242_, 3, v___x_1241_);
lean_closure_set(v___f_1242_, 4, v_toBind_1238_);
v___x_1243_ = l_Lean_getConstInfo___redArg(v_inst_1232_, v_inst_1233_, v_inst_1234_, v_declName_1235_);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_apply_4(v_mapConst_1240_, lean_box(0), lean_box(0), v___x_1244_, v___x_1243_);
v___x_1246_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1245_, v___f_1242_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object* v_m_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_declName_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_findModuleOf_x3f___redArg(v_inst_1248_, v_inst_1249_, v_inst_1250_, v_declName_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object* v___x_1253_, lean_object* v_toPure_1254_, uint8_t v_isUnsafe_1255_, lean_object* v_____x_1256_){
_start:
{
if (lean_obj_tag(v_____x_1256_) == 6)
{
lean_object* v_val_1257_; lean_object* v_numFields_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_val_1257_ = lean_ctor_get(v_____x_1256_, 0);
v_numFields_1258_ = lean_ctor_get(v_val_1257_, 4);
v___x_1259_ = lean_nat_dec_eq(v_numFields_1258_, v___x_1253_);
v___x_1260_ = lean_box(v___x_1259_);
v___x_1261_ = lean_apply_2(v_toPure_1254_, lean_box(0), v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_box(v_isUnsafe_1255_);
v___x_1263_ = lean_apply_2(v_toPure_1254_, lean_box(0), v___x_1262_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object* v___x_1264_, lean_object* v_toPure_1265_, lean_object* v_isUnsafe_1266_, lean_object* v_____x_1267_){
_start:
{
uint8_t v_isUnsafe_boxed_1268_; lean_object* v_res_1269_; 
v_isUnsafe_boxed_1268_ = lean_unbox(v_isUnsafe_1266_);
v_res_1269_ = l_Lean_isEnumType___redArg___lam__0(v___x_1264_, v_toPure_1265_, v_isUnsafe_boxed_1268_, v_____x_1267_);
lean_dec_ref(v_____x_1267_);
lean_dec(v___x_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_toBind_1273_, lean_object* v___f_1274_, lean_object* v_ctorName_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_Lean_getConstInfo___redArg(v_inst_1270_, v_inst_1271_, v_inst_1272_, v_ctorName_1275_);
v___x_1277_ = lean_apply_4(v_toBind_1273_, lean_box(0), lean_box(0), v___x_1276_, v___f_1274_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object* v_toPure_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_toBind_1282_, lean_object* v_____do__lift_1283_){
_start:
{
if (lean_obj_tag(v_____do__lift_1283_) == 5)
{
lean_object* v_val_1284_; lean_object* v_toConstantVal_1285_; lean_object* v_numParams_1286_; lean_object* v_numIndices_1287_; lean_object* v_ctors_1288_; uint8_t v_isRec_1289_; uint8_t v_isUnsafe_1290_; lean_object* v_type_1291_; uint8_t v___x_1292_; 
v_val_1284_ = lean_ctor_get(v_____do__lift_1283_, 0);
lean_inc_ref(v_val_1284_);
lean_dec_ref(v_____do__lift_1283_);
v_toConstantVal_1285_ = lean_ctor_get(v_val_1284_, 0);
v_numParams_1286_ = lean_ctor_get(v_val_1284_, 1);
lean_inc(v_numParams_1286_);
v_numIndices_1287_ = lean_ctor_get(v_val_1284_, 2);
lean_inc(v_numIndices_1287_);
v_ctors_1288_ = lean_ctor_get(v_val_1284_, 4);
lean_inc(v_ctors_1288_);
v_isRec_1289_ = lean_ctor_get_uint8(v_val_1284_, sizeof(void*)*6);
v_isUnsafe_1290_ = lean_ctor_get_uint8(v_val_1284_, sizeof(void*)*6 + 1);
v_type_1291_ = lean_ctor_get(v_toConstantVal_1285_, 2);
v___x_1292_ = l_Lean_Expr_isProp(v_type_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1293_ = l_Lean_InductiveVal_numTypeFormers(v_val_1284_);
lean_dec_ref(v_val_1284_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_dec_eq(v___x_1293_, v___x_1294_);
lean_dec(v___x_1293_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v_ctors_1288_);
lean_dec(v_numIndices_1287_);
lean_dec(v_numParams_1286_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1296_ = lean_box(v___x_1295_);
v___x_1297_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1296_);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_eq(v_numIndices_1287_, v___x_1298_);
lean_dec(v_numIndices_1287_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v_ctors_1288_);
lean_dec(v_numParams_1286_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1300_ = lean_box(v___x_1299_);
v___x_1301_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1300_);
return v___x_1301_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_eq(v_numParams_1286_, v___x_1298_);
lean_dec(v_numParams_1286_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_ctors_1288_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1303_ = lean_box(v___x_1302_);
v___x_1304_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1303_);
return v___x_1304_;
}
else
{
uint8_t v___x_1305_; 
v___x_1305_ = l_List_isEmpty___redArg(v_ctors_1288_);
if (v___x_1305_ == 0)
{
if (v_isRec_1289_ == 0)
{
if (v_isUnsafe_1290_ == 0)
{
lean_object* v___x_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_box(v_isUnsafe_1290_);
v___f_1307_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1307_, 0, v___x_1298_);
lean_closure_set(v___f_1307_, 1, v_toPure_1278_);
lean_closure_set(v___f_1307_, 2, v___x_1306_);
lean_inc_ref(v_inst_1279_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1308_, 0, v_inst_1279_);
lean_closure_set(v___f_1308_, 1, v_inst_1280_);
lean_closure_set(v___f_1308_, 2, v_inst_1281_);
lean_closure_set(v___f_1308_, 3, v_toBind_1282_);
lean_closure_set(v___f_1308_, 4, v___f_1307_);
v___x_1309_ = l_List_allM___redArg(v_inst_1279_, v___f_1308_, v_ctors_1288_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_ctors_1288_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1310_ = lean_box(v_isRec_1289_);
v___x_1311_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1310_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec(v_ctors_1288_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1312_ = lean_box(v___x_1305_);
v___x_1313_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1312_);
return v___x_1313_;
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_ctors_1288_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1314_ = lean_box(v___x_1292_);
v___x_1315_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1314_);
return v___x_1315_;
}
}
}
}
}
else
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec(v_ctors_1288_);
lean_dec(v_numIndices_1287_);
lean_dec(v_numParams_1286_);
lean_dec_ref(v_val_1284_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1316_ = 0;
v___x_1317_ = lean_box(v___x_1316_);
v___x_1318_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1317_);
return v___x_1318_;
}
}
else
{
uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_____do__lift_1283_);
lean_dec(v_toBind_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1319_ = 0;
v___x_1320_ = lean_box(v___x_1319_);
v___x_1321_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1320_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg(lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_declName_1325_){
_start:
{
lean_object* v_toApplicative_1326_; lean_object* v_toBind_1327_; lean_object* v_toPure_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; 
v_toApplicative_1326_ = lean_ctor_get(v_inst_1322_, 0);
v_toBind_1327_ = lean_ctor_get(v_inst_1322_, 1);
lean_inc(v_toBind_1327_);
v_toPure_1328_ = lean_ctor_get(v_toApplicative_1326_, 1);
lean_inc(v_toPure_1328_);
lean_inc_ref(v_inst_1324_);
lean_inc_ref(v_inst_1323_);
lean_inc_ref(v_inst_1322_);
v___x_1329_ = l_Lean_getConstInfo___redArg(v_inst_1322_, v_inst_1323_, v_inst_1324_, v_declName_1325_);
lean_inc(v_toBind_1327_);
v___f_1330_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1330_, 0, v_toPure_1328_);
lean_closure_set(v___f_1330_, 1, v_inst_1322_);
lean_closure_set(v___f_1330_, 2, v_inst_1323_);
lean_closure_set(v___f_1330_, 3, v_inst_1324_);
lean_closure_set(v___f_1330_, 4, v_toBind_1327_);
v___x_1331_ = lean_apply_4(v_toBind_1327_, lean_box(0), lean_box(0), v___x_1329_, v___f_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object* v_m_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_declName_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_isEnumType___redArg(v_inst_1333_, v_inst_1334_, v_inst_1335_, v_declName_1336_);
return v___x_1337_;
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
