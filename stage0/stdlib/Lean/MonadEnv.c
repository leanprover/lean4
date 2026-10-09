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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_allM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkRecName(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_isInductiveCore(lean_object* v_env_66_, lean_object* v_declName_67_){
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
LEAN_EXPORT void l_Lean_isInductiveCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_66_ = stack[0].m_obj;
lean_object* v_declName_67_ = stack[1].m_obj;
uint8_t v_res_73_;
v_res_73_ = l_Lean_isInductiveCore(v_env_66_, v_declName_67_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_isInductiveCore___boxed(lean_object* v_env_74_, lean_object* v_declName_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lean_isInductiveCore(v_env_74_, v_declName_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg___lam__0(lean_object* v_declName_78_, lean_object* v_toPure_79_, lean_object* v_____do__lift_80_){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = l_Lean_isInductiveCore(v_____do__lift_80_, v_declName_78_);
v___x_82_ = lean_box(v___x_81_);
v___x_83_ = lean_apply_2(v_toPure_79_, lean_box(0), v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg(lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_declName_86_){
_start:
{
lean_object* v_toApplicative_87_; lean_object* v_toBind_88_; lean_object* v_getEnv_89_; lean_object* v_toPure_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v_toApplicative_87_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_ref(v_toApplicative_87_);
v_toBind_88_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_toBind_88_);
lean_dec_ref(v_inst_84_);
v_getEnv_89_ = lean_ctor_get(v_inst_85_, 0);
lean_inc(v_getEnv_89_);
lean_dec_ref(v_inst_85_);
v_toPure_90_ = lean_ctor_get(v_toApplicative_87_, 1);
lean_inc(v_toPure_90_);
lean_dec_ref(v_toApplicative_87_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_isInductive___redArg___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v_declName_86_);
lean_closure_set(v___f_91_, 1, v_toPure_90_);
v___x_92_ = lean_apply_4(v_toBind_88_, lean_box(0), lean_box(0), v_getEnv_89_, v___f_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object* v_m_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_declName_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_isInductive___redArg(v_inst_94_, v_inst_95_, v_declName_96_);
return v___x_97_;
}
}
uint8_t l_Lean_isRecCore(lean_object* v_env_98_, lean_object* v_declName_99_){
_start:
{
uint8_t v___x_100_; lean_object* v___x_101_; 
v___x_100_ = 0;
v___x_101_ = l_Lean_Environment_findAsync_x3f(v_env_98_, v_declName_99_, v___x_100_);
if (lean_obj_tag(v___x_101_) == 1)
{
lean_object* v_val_102_; uint8_t v_kind_103_; 
v_val_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v___x_101_, 1);
v_kind_103_ = lean_ctor_get_uint8(v_val_102_, sizeof(void*)*3);
lean_dec(v_val_102_);
if (v_kind_103_ == 7)
{
uint8_t v___x_104_; 
v___x_104_ = 1;
return v___x_104_;
}
else
{
return v___x_100_;
}
}
else
{
lean_dec(v___x_101_);
return v___x_100_;
}
}
}
LEAN_EXPORT void l_Lean_isRecCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_98_ = stack[0].m_obj;
lean_object* v_declName_99_ = stack[1].m_obj;
uint8_t v_res_105_;
v_res_105_ = l_Lean_isRecCore(v_env_98_, v_declName_99_);
stack->m_num = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object* v_env_106_, lean_object* v_declName_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Lean_isRecCore(v_env_106_, v_declName_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___redArg___lam__0(lean_object* v_declName_110_, lean_object* v_toPure_111_, lean_object* v_____do__lift_112_){
_start:
{
uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = l_Lean_isRecCore(v_____do__lift_112_, v_declName_110_);
v___x_114_ = lean_box(v___x_113_);
v___x_115_ = lean_apply_2(v_toPure_111_, lean_box(0), v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___redArg(lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_declName_118_){
_start:
{
lean_object* v_toApplicative_119_; lean_object* v_toBind_120_; lean_object* v_getEnv_121_; lean_object* v_toPure_122_; lean_object* v___f_123_; lean_object* v___x_124_; 
v_toApplicative_119_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_ref(v_toApplicative_119_);
v_toBind_120_ = lean_ctor_get(v_inst_116_, 1);
lean_inc(v_toBind_120_);
lean_dec_ref(v_inst_116_);
v_getEnv_121_ = lean_ctor_get(v_inst_117_, 0);
lean_inc(v_getEnv_121_);
lean_dec_ref(v_inst_117_);
v_toPure_122_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc(v_toPure_122_);
lean_dec_ref(v_toApplicative_119_);
v___f_123_ = lean_alloc_closure((void*)(l_Lean_isRec___redArg___lam__0), 3, 2);
lean_closure_set(v___f_123_, 0, v_declName_118_);
lean_closure_set(v___f_123_, 1, v_toPure_122_);
v___x_124_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v_getEnv_121_, v___f_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_declName_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_isRec___redArg(v_inst_126_, v_inst_127_, v_declName_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg___lam__0(lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_x_133_, lean_object* v_____do__lift_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = l_Lean_Environment_unlockAsync(v_____do__lift_134_);
v___x_136_ = l_Lean_withEnv___redArg(v_inst_130_, v_inst_131_, v_inst_132_, v___x_135_, v_x_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_toBind_141_; lean_object* v_getEnv_142_; lean_object* v___f_143_; lean_object* v___x_144_; 
v_toBind_141_ = lean_ctor_get(v_inst_137_, 1);
lean_inc(v_toBind_141_);
v_getEnv_142_ = lean_ctor_get(v_inst_138_, 0);
lean_inc(v_getEnv_142_);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___redArg___lam__0), 5, 4);
lean_closure_set(v___f_143_, 0, v_inst_137_);
lean_closure_set(v___f_143_, 1, v_inst_139_);
lean_closure_set(v___f_143_, 2, v_inst_138_);
lean_closure_set(v___f_143_, 3, v_x_140_);
v___x_144_ = lean_apply_4(v_toBind_141_, lean_box(0), lean_box(0), v_getEnv_142_, v___f_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object* v_m_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_00_u03b1_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_toBind_151_; lean_object* v_getEnv_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v_toBind_151_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_toBind_151_);
v_getEnv_152_ = lean_ctor_get(v_inst_147_, 0);
lean_inc(v_getEnv_152_);
v___f_153_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___redArg___lam__0), 5, 4);
lean_closure_set(v___f_153_, 0, v_inst_146_);
lean_closure_set(v___f_153_, 1, v_inst_148_);
lean_closure_set(v___f_153_, 2, v_inst_147_);
lean_closure_set(v___f_153_, 3, v_x_150_);
v___x_154_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v_getEnv_152_, v___f_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0(lean_object* v_x_155_){
_start:
{
lean_object* v_fst_156_; 
v_fst_156_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_fst_156_);
return v_fst_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(lean_object* v_x_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__0(v_x_157_);
lean_dec_ref(v_x_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__1(lean_object* v_a_159_, lean_object* v_toPure_160_, lean_object* v_____do__lift_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v_a_159_);
lean_ctor_set(v___x_162_, 1, v_____do__lift_161_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___x_164_ = lean_apply_2(v_toPure_160_, lean_box(0), v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__2(lean_object* v_toPure_165_, lean_object* v_toBind_166_, lean_object* v_getEnv_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; 
v___f_169_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_169_, 0, v_a_168_);
lean_closure_set(v___f_169_, 1, v_toPure_165_);
v___x_170_ = lean_apply_4(v_toBind_166_, lean_box(0), lean_box(0), v_getEnv_167_, v___f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__3(lean_object* v_toPure_171_, lean_object* v_e_172_){
_start:
{
lean_object* v_a_173_; lean_object* v___x_174_; 
v_a_173_ = lean_ctor_get(v_e_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref(v_e_172_);
v___x_174_ = lean_apply_2(v_toPure_171_, lean_box(0), v_a_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4(lean_object* v___x_175_, lean_object* v_x_176_){
_start:
{
lean_inc(v___x_175_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(lean_object* v___x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_withoutModifyingEnv_x27___redArg___lam__4(v___x_177_, v_x_178_);
lean_dec(v_x_178_);
lean_dec(v___x_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__5(lean_object* v_toFunctor_180_, lean_object* v_toBind_181_, lean_object* v_x_182_, lean_object* v___f_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v___f_186_, lean_object* v___f_187_, lean_object* v_env_188_){
_start:
{
lean_object* v_map_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v_y_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_map_189_ = lean_ctor_get(v_toFunctor_180_, 0);
lean_inc(v_map_189_);
lean_dec_ref(v_toFunctor_180_);
lean_inc(v_toBind_181_);
v___x_190_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v_x_182_, v___f_183_);
v___x_191_ = l_Lean_setEnv___redArg(v_inst_184_, v_env_188_);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_192_, 0, v___x_191_);
v_y_193_ = lean_apply_4(v_inst_185_, lean_box(0), lean_box(0), v___x_190_, v___f_192_);
v___x_194_ = lean_apply_4(v_map_189_, lean_box(0), lean_box(0), v___f_186_, v_y_193_);
v___x_195_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v___x_194_, v___f_187_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_toApplicative_201_; lean_object* v_toBind_202_; lean_object* v_getEnv_203_; lean_object* v_toFunctor_204_; lean_object* v_toPure_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___f_209_; lean_object* v___x_210_; 
v_toApplicative_201_ = lean_ctor_get(v_inst_197_, 0);
lean_inc_ref(v_toApplicative_201_);
v_toBind_202_ = lean_ctor_get(v_inst_197_, 1);
lean_inc_n(v_toBind_202_, 3);
lean_dec_ref(v_inst_197_);
v_getEnv_203_ = lean_ctor_get(v_inst_198_, 0);
lean_inc_n(v_getEnv_203_, 2);
v_toFunctor_204_ = lean_ctor_get(v_toApplicative_201_, 0);
lean_inc_ref(v_toFunctor_204_);
v_toPure_205_ = lean_ctor_get(v_toApplicative_201_, 1);
lean_inc_n(v_toPure_205_, 2);
lean_dec_ref(v_toApplicative_201_);
v___f_206_ = ((lean_object*)(l_Lean_withoutModifyingEnv_x27___redArg___closed__0));
v___f_207_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_207_, 0, v_toPure_205_);
lean_closure_set(v___f_207_, 1, v_toBind_202_);
lean_closure_set(v___f_207_, 2, v_getEnv_203_);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_208_, 0, v_toPure_205_);
v___f_209_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_209_, 0, v_toFunctor_204_);
lean_closure_set(v___f_209_, 1, v_toBind_202_);
lean_closure_set(v___f_209_, 2, v_x_200_);
lean_closure_set(v___f_209_, 3, v___f_207_);
lean_closure_set(v___f_209_, 4, v_inst_198_);
lean_closure_set(v___f_209_, 5, v_inst_199_);
lean_closure_set(v___f_209_, 6, v___f_206_);
lean_closure_set(v___f_209_, 7, v___f_208_);
v___x_210_ = lean_apply_4(v_toBind_202_, lean_box(0), lean_box(0), v_getEnv_203_, v___f_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object* v_m_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_00_u03b1_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_toApplicative_217_; lean_object* v_toBind_218_; lean_object* v_getEnv_219_; lean_object* v_toFunctor_220_; lean_object* v_toPure_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; 
v_toApplicative_217_ = lean_ctor_get(v_inst_212_, 0);
lean_inc_ref(v_toApplicative_217_);
v_toBind_218_ = lean_ctor_get(v_inst_212_, 1);
lean_inc_n(v_toBind_218_, 3);
lean_dec_ref(v_inst_212_);
v_getEnv_219_ = lean_ctor_get(v_inst_213_, 0);
lean_inc_n(v_getEnv_219_, 2);
v_toFunctor_220_ = lean_ctor_get(v_toApplicative_217_, 0);
lean_inc_ref(v_toFunctor_220_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_217_, 1);
lean_inc_n(v_toPure_221_, 2);
lean_dec_ref(v_toApplicative_217_);
v___f_222_ = ((lean_object*)(l_Lean_withoutModifyingEnv_x27___redArg___closed__0));
v___f_223_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_223_, 0, v_toPure_221_);
lean_closure_set(v___f_223_, 1, v_toBind_218_);
lean_closure_set(v___f_223_, 2, v_getEnv_219_);
v___f_224_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_224_, 0, v_toPure_221_);
v___f_225_ = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_225_, 0, v_toFunctor_220_);
lean_closure_set(v___f_225_, 1, v_toBind_218_);
lean_closure_set(v___f_225_, 2, v_x_216_);
lean_closure_set(v___f_225_, 3, v___f_223_);
lean_closure_set(v___f_225_, 4, v_inst_213_);
lean_closure_set(v___f_225_, 5, v_inst_214_);
lean_closure_set(v___f_225_, 6, v___f_222_);
lean_closure_set(v___f_225_, 7, v___f_224_);
v___x_226_ = lean_apply_4(v_toBind_218_, lean_box(0), lean_box(0), v_getEnv_219_, v___f_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg___lam__0(lean_object* v_declName_227_, lean_object* v_failK_228_, lean_object* v_k_229_, lean_object* v_us_230_, lean_object* v_____do__lift_231_){
_start:
{
uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_232_ = 0;
v___x_233_ = l_Lean_Environment_find_x3f(v_____do__lift_231_, v_declName_227_, v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_us_230_);
lean_dec(v_k_229_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_1(v_failK_228_, v___x_234_);
return v___x_235_;
}
else
{
lean_object* v_val_236_; lean_object* v___x_237_; 
lean_dec(v_failK_228_);
v_val_236_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_233_, 1);
v___x_237_ = lean_apply_2(v_k_229_, v_val_236_, v_us_230_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg(lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_e_240_, lean_object* v_failK_241_, lean_object* v_k_242_){
_start:
{
if (lean_obj_tag(v_e_240_) == 4)
{
lean_object* v_toBind_243_; lean_object* v_declName_244_; lean_object* v_us_245_; lean_object* v_getEnv_246_; lean_object* v___f_247_; lean_object* v___x_248_; 
v_toBind_243_ = lean_ctor_get(v_inst_238_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_238_);
v_declName_244_ = lean_ctor_get(v_e_240_, 0);
lean_inc(v_declName_244_);
v_us_245_ = lean_ctor_get(v_e_240_, 1);
lean_inc(v_us_245_);
lean_dec_ref_known(v_e_240_, 2);
v_getEnv_246_ = lean_ctor_get(v_inst_239_, 0);
lean_inc(v_getEnv_246_);
lean_dec_ref(v_inst_239_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_matchConst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_247_, 0, v_declName_244_);
lean_closure_set(v___f_247_, 1, v_failK_241_);
lean_closure_set(v___f_247_, 2, v_k_242_);
lean_closure_set(v___f_247_, 3, v_us_245_);
v___x_248_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v_getEnv_246_, v___f_247_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_k_242_);
lean_dec_ref(v_e_240_);
lean_dec_ref(v_inst_239_);
lean_dec_ref(v_inst_238_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_apply_1(v_failK_241_, v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object* v_m_251_, lean_object* v_00_u03b1_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_e_255_, lean_object* v_failK_256_, lean_object* v_k_257_){
_start:
{
if (lean_obj_tag(v_e_255_) == 4)
{
lean_object* v_toBind_258_; lean_object* v_declName_259_; lean_object* v_us_260_; lean_object* v_getEnv_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v_toBind_258_ = lean_ctor_get(v_inst_253_, 1);
lean_inc(v_toBind_258_);
lean_dec_ref(v_inst_253_);
v_declName_259_ = lean_ctor_get(v_e_255_, 0);
lean_inc(v_declName_259_);
v_us_260_ = lean_ctor_get(v_e_255_, 1);
lean_inc(v_us_260_);
lean_dec_ref_known(v_e_255_, 2);
v_getEnv_261_ = lean_ctor_get(v_inst_254_, 0);
lean_inc(v_getEnv_261_);
lean_dec_ref(v_inst_254_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_matchConst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_262_, 0, v_declName_259_);
lean_closure_set(v___f_262_, 1, v_failK_256_);
lean_closure_set(v___f_262_, 2, v_k_257_);
lean_closure_set(v___f_262_, 3, v_us_260_);
v___x_263_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v_getEnv_261_, v___f_262_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_k_257_);
lean_dec_ref(v_e_255_);
lean_dec_ref(v_inst_254_);
lean_dec_ref(v_inst_253_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v_failK_256_, v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg___lam__0(lean_object* v_declName_266_, lean_object* v_failK_267_, lean_object* v_k_268_, lean_object* v_us_269_, lean_object* v_____do__lift_270_){
_start:
{
uint8_t v___x_271_; lean_object* v___x_272_; 
v___x_271_ = 0;
v___x_272_ = l_Lean_Environment_find_x3f(v_____do__lift_270_, v_declName_266_, v___x_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_us_269_);
lean_dec(v_k_268_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_apply_1(v_failK_267_, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v_val_275_; 
v_val_275_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v___x_272_, 1);
if (lean_obj_tag(v_val_275_) == 5)
{
lean_object* v_val_276_; lean_object* v___x_277_; 
lean_dec(v_failK_267_);
v_val_276_ = lean_ctor_get(v_val_275_, 0);
lean_inc_ref(v_val_276_);
lean_dec_ref_known(v_val_275_, 1);
v___x_277_ = lean_apply_2(v_k_268_, v_val_276_, v_us_269_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_val_275_);
lean_dec(v_us_269_);
lean_dec(v_k_268_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_apply_1(v_failK_267_, v___x_278_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg(lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_e_282_, lean_object* v_failK_283_, lean_object* v_k_284_){
_start:
{
if (lean_obj_tag(v_e_282_) == 4)
{
lean_object* v_toBind_285_; lean_object* v_declName_286_; lean_object* v_us_287_; lean_object* v_getEnv_288_; lean_object* v___f_289_; lean_object* v___x_290_; 
v_toBind_285_ = lean_ctor_get(v_inst_280_, 1);
lean_inc(v_toBind_285_);
lean_dec_ref(v_inst_280_);
v_declName_286_ = lean_ctor_get(v_e_282_, 0);
lean_inc(v_declName_286_);
v_us_287_ = lean_ctor_get(v_e_282_, 1);
lean_inc(v_us_287_);
lean_dec_ref_known(v_e_282_, 2);
v_getEnv_288_ = lean_ctor_get(v_inst_281_, 0);
lean_inc(v_getEnv_288_);
lean_dec_ref(v_inst_281_);
v___f_289_ = lean_alloc_closure((void*)(l_Lean_matchConstInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_289_, 0, v_declName_286_);
lean_closure_set(v___f_289_, 1, v_failK_283_);
lean_closure_set(v___f_289_, 2, v_k_284_);
lean_closure_set(v___f_289_, 3, v_us_287_);
v___x_290_ = lean_apply_4(v_toBind_285_, lean_box(0), lean_box(0), v_getEnv_288_, v___f_289_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_k_284_);
lean_dec_ref(v_e_282_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_apply_1(v_failK_283_, v___x_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object* v_m_293_, lean_object* v_00_u03b1_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_e_297_, lean_object* v_failK_298_, lean_object* v_k_299_){
_start:
{
if (lean_obj_tag(v_e_297_) == 4)
{
lean_object* v_toBind_300_; lean_object* v_declName_301_; lean_object* v_us_302_; lean_object* v_getEnv_303_; lean_object* v___f_304_; lean_object* v___x_305_; 
v_toBind_300_ = lean_ctor_get(v_inst_295_, 1);
lean_inc(v_toBind_300_);
lean_dec_ref(v_inst_295_);
v_declName_301_ = lean_ctor_get(v_e_297_, 0);
lean_inc(v_declName_301_);
v_us_302_ = lean_ctor_get(v_e_297_, 1);
lean_inc(v_us_302_);
lean_dec_ref_known(v_e_297_, 2);
v_getEnv_303_ = lean_ctor_get(v_inst_296_, 0);
lean_inc(v_getEnv_303_);
lean_dec_ref(v_inst_296_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_matchConstInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_304_, 0, v_declName_301_);
lean_closure_set(v___f_304_, 1, v_failK_298_);
lean_closure_set(v___f_304_, 2, v_k_299_);
lean_closure_set(v___f_304_, 3, v_us_302_);
v___x_305_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v_getEnv_303_, v___f_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_k_299_);
lean_dec_ref(v_e_297_);
lean_dec_ref(v_inst_296_);
lean_dec_ref(v_inst_295_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_apply_1(v_failK_298_, v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg___lam__0(lean_object* v_declName_308_, lean_object* v_failK_309_, lean_object* v_k_310_, lean_object* v_us_311_, lean_object* v_____do__lift_312_){
_start:
{
uint8_t v___x_313_; lean_object* v___x_314_; 
v___x_313_ = 0;
v___x_314_ = l_Lean_Environment_find_x3f(v_____do__lift_312_, v_declName_308_, v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_us_311_);
lean_dec(v_k_310_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_1(v_failK_309_, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v_val_317_; 
v_val_317_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v___x_314_, 1);
if (lean_obj_tag(v_val_317_) == 6)
{
lean_object* v_val_318_; lean_object* v___x_319_; 
lean_dec(v_failK_309_);
v_val_318_ = lean_ctor_get(v_val_317_, 0);
lean_inc_ref(v_val_318_);
lean_dec_ref_known(v_val_317_, 1);
v___x_319_ = lean_apply_2(v_k_310_, v_val_318_, v_us_311_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v_val_317_);
lean_dec(v_us_311_);
lean_dec(v_k_310_);
v___x_320_ = lean_box(0);
v___x_321_ = lean_apply_1(v_failK_309_, v___x_320_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg(lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_e_324_, lean_object* v_failK_325_, lean_object* v_k_326_){
_start:
{
if (lean_obj_tag(v_e_324_) == 4)
{
lean_object* v_toBind_327_; lean_object* v_declName_328_; lean_object* v_us_329_; lean_object* v_getEnv_330_; lean_object* v___f_331_; lean_object* v___x_332_; 
v_toBind_327_ = lean_ctor_get(v_inst_322_, 1);
lean_inc(v_toBind_327_);
lean_dec_ref(v_inst_322_);
v_declName_328_ = lean_ctor_get(v_e_324_, 0);
lean_inc(v_declName_328_);
v_us_329_ = lean_ctor_get(v_e_324_, 1);
lean_inc(v_us_329_);
lean_dec_ref_known(v_e_324_, 2);
v_getEnv_330_ = lean_ctor_get(v_inst_323_, 0);
lean_inc(v_getEnv_330_);
lean_dec_ref(v_inst_323_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_matchConstCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_331_, 0, v_declName_328_);
lean_closure_set(v___f_331_, 1, v_failK_325_);
lean_closure_set(v___f_331_, 2, v_k_326_);
lean_closure_set(v___f_331_, 3, v_us_329_);
v___x_332_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v_getEnv_330_, v___f_331_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_k_326_);
lean_dec_ref(v_e_324_);
lean_dec_ref(v_inst_323_);
lean_dec_ref(v_inst_322_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_1(v_failK_325_, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object* v_m_335_, lean_object* v_00_u03b1_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_e_339_, lean_object* v_failK_340_, lean_object* v_k_341_){
_start:
{
if (lean_obj_tag(v_e_339_) == 4)
{
lean_object* v_toBind_342_; lean_object* v_declName_343_; lean_object* v_us_344_; lean_object* v_getEnv_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_toBind_342_ = lean_ctor_get(v_inst_337_, 1);
lean_inc(v_toBind_342_);
lean_dec_ref(v_inst_337_);
v_declName_343_ = lean_ctor_get(v_e_339_, 0);
lean_inc(v_declName_343_);
v_us_344_ = lean_ctor_get(v_e_339_, 1);
lean_inc(v_us_344_);
lean_dec_ref_known(v_e_339_, 2);
v_getEnv_345_ = lean_ctor_get(v_inst_338_, 0);
lean_inc(v_getEnv_345_);
lean_dec_ref(v_inst_338_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_matchConstCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_346_, 0, v_declName_343_);
lean_closure_set(v___f_346_, 1, v_failK_340_);
lean_closure_set(v___f_346_, 2, v_k_341_);
lean_closure_set(v___f_346_, 3, v_us_344_);
v___x_347_ = lean_apply_4(v_toBind_342_, lean_box(0), lean_box(0), v_getEnv_345_, v___f_346_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_k_341_);
lean_dec_ref(v_e_339_);
lean_dec_ref(v_inst_338_);
lean_dec_ref(v_inst_337_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_apply_1(v_failK_340_, v___x_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg___lam__0(lean_object* v_declName_350_, lean_object* v_failK_351_, lean_object* v_k_352_, lean_object* v_us_353_, lean_object* v_____do__lift_354_){
_start:
{
uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_355_ = 0;
v___x_356_ = l_Lean_Environment_find_x3f(v_____do__lift_354_, v_declName_350_, v___x_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_us_353_);
lean_dec(v_k_352_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_apply_1(v_failK_351_, v___x_357_);
return v___x_358_;
}
else
{
lean_object* v_val_359_; 
v_val_359_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v___x_356_, 1);
if (lean_obj_tag(v_val_359_) == 7)
{
lean_object* v_val_360_; lean_object* v___x_361_; 
lean_dec(v_failK_351_);
v_val_360_ = lean_ctor_get(v_val_359_, 0);
lean_inc_ref(v_val_360_);
lean_dec_ref_known(v_val_359_, 1);
v___x_361_ = lean_apply_2(v_k_352_, v_val_360_, v_us_353_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v_val_359_);
lean_dec(v_us_353_);
lean_dec(v_k_352_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_apply_1(v_failK_351_, v___x_362_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_e_366_, lean_object* v_failK_367_, lean_object* v_k_368_){
_start:
{
if (lean_obj_tag(v_e_366_) == 4)
{
lean_object* v_toBind_369_; lean_object* v_declName_370_; lean_object* v_us_371_; lean_object* v_getEnv_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v_toBind_369_ = lean_ctor_get(v_inst_364_, 1);
lean_inc(v_toBind_369_);
lean_dec_ref(v_inst_364_);
v_declName_370_ = lean_ctor_get(v_e_366_, 0);
lean_inc(v_declName_370_);
v_us_371_ = lean_ctor_get(v_e_366_, 1);
lean_inc(v_us_371_);
lean_dec_ref_known(v_e_366_, 2);
v_getEnv_372_ = lean_ctor_get(v_inst_365_, 0);
lean_inc(v_getEnv_372_);
lean_dec_ref(v_inst_365_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_matchConstRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_373_, 0, v_declName_370_);
lean_closure_set(v___f_373_, 1, v_failK_367_);
lean_closure_set(v___f_373_, 2, v_k_368_);
lean_closure_set(v___f_373_, 3, v_us_371_);
v___x_374_ = lean_apply_4(v_toBind_369_, lean_box(0), lean_box(0), v_getEnv_372_, v___f_373_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_k_368_);
lean_dec_ref(v_e_366_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_364_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_apply_1(v_failK_367_, v___x_375_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object* v_m_377_, lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_e_381_, lean_object* v_failK_382_, lean_object* v_k_383_){
_start:
{
if (lean_obj_tag(v_e_381_) == 4)
{
lean_object* v_toBind_384_; lean_object* v_declName_385_; lean_object* v_us_386_; lean_object* v_getEnv_387_; lean_object* v___f_388_; lean_object* v___x_389_; 
v_toBind_384_ = lean_ctor_get(v_inst_379_, 1);
lean_inc(v_toBind_384_);
lean_dec_ref(v_inst_379_);
v_declName_385_ = lean_ctor_get(v_e_381_, 0);
lean_inc(v_declName_385_);
v_us_386_ = lean_ctor_get(v_e_381_, 1);
lean_inc(v_us_386_);
lean_dec_ref_known(v_e_381_, 2);
v_getEnv_387_ = lean_ctor_get(v_inst_380_, 0);
lean_inc(v_getEnv_387_);
lean_dec_ref(v_inst_380_);
v___f_388_ = lean_alloc_closure((void*)(l_Lean_matchConstRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_388_, 0, v_declName_385_);
lean_closure_set(v___f_388_, 1, v_failK_382_);
lean_closure_set(v___f_388_, 2, v_k_383_);
lean_closure_set(v___f_388_, 3, v_us_386_);
v___x_389_ = lean_apply_4(v_toBind_384_, lean_box(0), lean_box(0), v_getEnv_387_, v___f_388_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_k_383_);
lean_dec_ref(v_e_381_);
lean_dec_ref(v_inst_380_);
lean_dec_ref(v_inst_379_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_apply_1(v_failK_382_, v___x_390_);
return v___x_391_;
}
}
}
lean_object* l_Lean_hasConst___redArg___lam__0(lean_object* v_constName_392_, uint8_t v_skipRealize_393_, lean_object* v_toPure_394_, lean_object* v_____do__lift_395_){
_start:
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = l_Lean_Environment_contains(v_____do__lift_395_, v_constName_392_, v_skipRealize_393_);
v___x_397_ = lean_box(v___x_396_);
v___x_398_ = lean_apply_2(v_toPure_394_, lean_box(0), v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT void l_Lean_hasConst___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_392_ = stack[0].m_obj;
uint8_t v_skipRealize_393_ = stack[1].m_num;
lean_object* v_toPure_394_ = stack[2].m_obj;
lean_object* v_____do__lift_395_ = stack[3].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_hasConst___redArg___lam__0(v_constName_392_, v_skipRealize_393_, v_toPure_394_, v_____do__lift_395_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0___boxed(lean_object* v_constName_400_, lean_object* v_skipRealize_401_, lean_object* v_toPure_402_, lean_object* v_____do__lift_403_){
_start:
{
uint8_t v_skipRealize_boxed_404_; lean_object* v_res_405_; 
v_skipRealize_boxed_404_ = lean_unbox(v_skipRealize_401_);
v_res_405_ = l_Lean_hasConst___redArg___lam__0(v_constName_400_, v_skipRealize_boxed_404_, v_toPure_402_, v_____do__lift_403_);
return v_res_405_;
}
}
lean_object* l_Lean_hasConst___redArg(lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_constName_408_, uint8_t v_skipRealize_409_){
_start:
{
lean_object* v_toApplicative_410_; lean_object* v_toBind_411_; lean_object* v_getEnv_412_; lean_object* v_toPure_413_; lean_object* v___x_414_; lean_object* v___f_415_; lean_object* v___x_416_; 
v_toApplicative_410_ = lean_ctor_get(v_inst_406_, 0);
lean_inc_ref(v_toApplicative_410_);
v_toBind_411_ = lean_ctor_get(v_inst_406_, 1);
lean_inc(v_toBind_411_);
lean_dec_ref(v_inst_406_);
v_getEnv_412_ = lean_ctor_get(v_inst_407_, 0);
lean_inc(v_getEnv_412_);
lean_dec_ref(v_inst_407_);
v_toPure_413_ = lean_ctor_get(v_toApplicative_410_, 1);
lean_inc(v_toPure_413_);
lean_dec_ref(v_toApplicative_410_);
v___x_414_ = lean_box(v_skipRealize_409_);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_hasConst___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_415_, 0, v_constName_408_);
lean_closure_set(v___f_415_, 1, v___x_414_);
lean_closure_set(v___f_415_, 2, v_toPure_413_);
v___x_416_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v_getEnv_412_, v___f_415_);
return v___x_416_;
}
}
LEAN_EXPORT void l_Lean_hasConst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_406_ = stack[0].m_obj;
lean_object* v_inst_407_ = stack[1].m_obj;
lean_object* v_constName_408_ = stack[2].m_obj;
uint8_t v_skipRealize_409_ = stack[3].m_num;
lean_object* v_res_417_;
v_res_417_ = l_Lean_hasConst___redArg(v_inst_406_, v_inst_407_, v_constName_408_, v_skipRealize_409_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___boxed(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_constName_420_, lean_object* v_skipRealize_421_){
_start:
{
uint8_t v_skipRealize_boxed_422_; lean_object* v_res_423_; 
v_skipRealize_boxed_422_ = lean_unbox(v_skipRealize_421_);
v_res_423_ = l_Lean_hasConst___redArg(v_inst_418_, v_inst_419_, v_constName_420_, v_skipRealize_boxed_422_);
return v_res_423_;
}
}
lean_object* l_Lean_hasConst(lean_object* v_m_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_constName_427_, uint8_t v_skipRealize_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_hasConst___redArg(v_inst_425_, v_inst_426_, v_constName_427_, v_skipRealize_428_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_hasConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_425_ = stack[1].m_obj;
lean_object* v_inst_426_ = stack[2].m_obj;
lean_object* v_constName_427_ = stack[3].m_obj;
uint8_t v_skipRealize_428_ = stack[4].m_num;
lean_object* v_res_430_;
v_res_430_ = l_Lean_hasConst(lean_box(0), v_inst_425_, v_inst_426_, v_constName_427_, v_skipRealize_428_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___boxed(lean_object* v_m_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_constName_434_, lean_object* v_skipRealize_435_){
_start:
{
uint8_t v_skipRealize_boxed_436_; lean_object* v_res_437_; 
v_skipRealize_boxed_436_ = lean_unbox(v_skipRealize_435_);
v_res_437_ = l_Lean_hasConst(v_m_431_, v_inst_432_, v_inst_433_, v_constName_434_, v_skipRealize_boxed_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg___lam__0(lean_object* v_constName_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_toPure_442_, lean_object* v_____do__lift_443_){
_start:
{
uint8_t v___x_444_; lean_object* v___x_445_; 
v___x_444_ = 0;
lean_inc(v_constName_438_);
v___x_445_ = l_Lean_Environment_find_x3f(v_____do__lift_443_, v_constName_438_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec(v_toPure_442_);
v___x_446_ = l_Lean_throwUnknownConstant___redArg(v_inst_439_, v_inst_440_, v_inst_441_, v_constName_438_);
return v___x_446_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_448_; 
lean_dec_ref(v_inst_441_);
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
lean_dec(v_constName_438_);
v_val_447_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v___x_445_, 1);
v___x_448_ = lean_apply_2(v_toPure_442_, lean_box(0), v_val_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg(lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_constName_452_){
_start:
{
lean_object* v_toApplicative_453_; lean_object* v_toBind_454_; lean_object* v_getEnv_455_; lean_object* v_toPure_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_toApplicative_453_ = lean_ctor_get(v_inst_449_, 0);
v_toBind_454_ = lean_ctor_get(v_inst_449_, 1);
lean_inc(v_toBind_454_);
v_getEnv_455_ = lean_ctor_get(v_inst_450_, 0);
lean_inc(v_getEnv_455_);
v_toPure_456_ = lean_ctor_get(v_toApplicative_453_, 1);
lean_inc(v_toPure_456_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_getConstInfo___redArg___lam__0), 6, 5);
lean_closure_set(v___f_457_, 0, v_constName_452_);
lean_closure_set(v___f_457_, 1, v_inst_449_);
lean_closure_set(v___f_457_, 2, v_inst_450_);
lean_closure_set(v___f_457_, 3, v_inst_451_);
lean_closure_set(v___f_457_, 4, v_toPure_456_);
v___x_458_ = lean_apply_4(v_toBind_454_, lean_box(0), lean_box(0), v_getEnv_455_, v___f_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object* v_m_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_constName_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_getConstInfo___redArg(v_inst_460_, v_inst_461_, v_inst_462_, v_constName_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg___lam__0(lean_object* v_constName_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_toPure_469_, lean_object* v_____do__lift_470_){
_start:
{
uint8_t v___x_471_; lean_object* v___x_472_; 
v___x_471_ = 0;
lean_inc(v_constName_465_);
v___x_472_ = l_Lean_Environment_findConstVal_x3f(v_____do__lift_470_, v_constName_465_, v___x_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; 
lean_dec(v_toPure_469_);
v___x_473_ = l_Lean_throwUnknownConstant___redArg(v_inst_466_, v_inst_467_, v_inst_468_, v_constName_465_);
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; 
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_inst_467_);
lean_dec_ref(v_inst_466_);
lean_dec(v_constName_465_);
v_val_474_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_472_, 1);
v___x_475_ = lean_apply_2(v_toPure_469_, lean_box(0), v_val_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg(lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_constName_479_){
_start:
{
lean_object* v_toApplicative_480_; lean_object* v_toBind_481_; lean_object* v_getEnv_482_; lean_object* v_toPure_483_; lean_object* v___f_484_; lean_object* v___x_485_; 
v_toApplicative_480_ = lean_ctor_get(v_inst_476_, 0);
v_toBind_481_ = lean_ctor_get(v_inst_476_, 1);
lean_inc(v_toBind_481_);
v_getEnv_482_ = lean_ctor_get(v_inst_477_, 0);
lean_inc(v_getEnv_482_);
v_toPure_483_ = lean_ctor_get(v_toApplicative_480_, 1);
lean_inc(v_toPure_483_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_getConstVal___redArg___lam__0), 6, 5);
lean_closure_set(v___f_484_, 0, v_constName_479_);
lean_closure_set(v___f_484_, 1, v_inst_476_);
lean_closure_set(v___f_484_, 2, v_inst_477_);
lean_closure_set(v___f_484_, 3, v_inst_478_);
lean_closure_set(v___f_484_, 4, v_toPure_483_);
v___x_485_ = lean_apply_4(v_toBind_481_, lean_box(0), lean_box(0), v_getEnv_482_, v___f_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal(lean_object* v_m_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_constName_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_getConstVal___redArg(v_inst_487_, v_inst_488_, v_inst_489_, v_constName_490_);
return v___x_491_;
}
}
lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0(lean_object* v_constName_492_, uint8_t v_skipRealize_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_toPure_497_, lean_object* v_____do__lift_498_){
_start:
{
lean_object* v___x_499_; 
lean_inc(v_constName_492_);
v___x_499_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_498_, v_constName_492_, v_skipRealize_493_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; 
lean_dec(v_toPure_497_);
v___x_500_ = l_Lean_throwUnknownConstant___redArg(v_inst_494_, v_inst_495_, v_inst_496_, v_constName_492_);
return v___x_500_;
}
else
{
lean_object* v_val_501_; lean_object* v___x_502_; 
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_inst_495_);
lean_dec_ref(v_inst_494_);
lean_dec(v_constName_492_);
v_val_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_501_);
lean_dec_ref_known(v___x_499_, 1);
v___x_502_ = lean_apply_2(v_toPure_497_, lean_box(0), v_val_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT void l_Lean_getAsyncConstInfo___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_492_ = stack[0].m_obj;
uint8_t v_skipRealize_493_ = stack[1].m_num;
lean_object* v_inst_494_ = stack[2].m_obj;
lean_object* v_inst_495_ = stack[3].m_obj;
lean_object* v_inst_496_ = stack[4].m_obj;
lean_object* v_toPure_497_ = stack[5].m_obj;
lean_object* v_____do__lift_498_ = stack[6].m_obj;
lean_object* v_res_503_;
v_res_503_ = l_Lean_getAsyncConstInfo___redArg___lam__0(v_constName_492_, v_skipRealize_493_, v_inst_494_, v_inst_495_, v_inst_496_, v_toPure_497_, v_____do__lift_498_);
stack->m_obj
 = v_res_503_;
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(lean_object* v_constName_504_, lean_object* v_skipRealize_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_toPure_509_, lean_object* v_____do__lift_510_){
_start:
{
uint8_t v_skipRealize_boxed_511_; lean_object* v_res_512_; 
v_skipRealize_boxed_511_ = lean_unbox(v_skipRealize_505_);
v_res_512_ = l_Lean_getAsyncConstInfo___redArg___lam__0(v_constName_504_, v_skipRealize_boxed_511_, v_inst_506_, v_inst_507_, v_inst_508_, v_toPure_509_, v_____do__lift_510_);
return v_res_512_;
}
}
lean_object* l_Lean_getAsyncConstInfo___redArg(lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_constName_516_, uint8_t v_skipRealize_517_){
_start:
{
lean_object* v_toApplicative_518_; lean_object* v_toBind_519_; lean_object* v_getEnv_520_; lean_object* v_toPure_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___x_524_; 
v_toApplicative_518_ = lean_ctor_get(v_inst_513_, 0);
v_toBind_519_ = lean_ctor_get(v_inst_513_, 1);
lean_inc(v_toBind_519_);
v_getEnv_520_ = lean_ctor_get(v_inst_514_, 0);
lean_inc(v_getEnv_520_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_518_, 1);
lean_inc(v_toPure_521_);
v___x_522_ = lean_box(v_skipRealize_517_);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_getAsyncConstInfo___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_523_, 0, v_constName_516_);
lean_closure_set(v___f_523_, 1, v___x_522_);
lean_closure_set(v___f_523_, 2, v_inst_513_);
lean_closure_set(v___f_523_, 3, v_inst_514_);
lean_closure_set(v___f_523_, 4, v_inst_515_);
lean_closure_set(v___f_523_, 5, v_toPure_521_);
v___x_524_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v_getEnv_520_, v___f_523_);
return v___x_524_;
}
}
LEAN_EXPORT void l_Lean_getAsyncConstInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_513_ = stack[0].m_obj;
lean_object* v_inst_514_ = stack[1].m_obj;
lean_object* v_inst_515_ = stack[2].m_obj;
lean_object* v_constName_516_ = stack[3].m_obj;
uint8_t v_skipRealize_517_ = stack[4].m_num;
lean_object* v_res_525_;
v_res_525_ = l_Lean_getAsyncConstInfo___redArg(v_inst_513_, v_inst_514_, v_inst_515_, v_constName_516_, v_skipRealize_517_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___boxed(lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_constName_529_, lean_object* v_skipRealize_530_){
_start:
{
uint8_t v_skipRealize_boxed_531_; lean_object* v_res_532_; 
v_skipRealize_boxed_531_ = lean_unbox(v_skipRealize_530_);
v_res_532_ = l_Lean_getAsyncConstInfo___redArg(v_inst_526_, v_inst_527_, v_inst_528_, v_constName_529_, v_skipRealize_boxed_531_);
return v_res_532_;
}
}
lean_object* l_Lean_getAsyncConstInfo(lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_constName_537_, uint8_t v_skipRealize_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_getAsyncConstInfo___redArg(v_inst_534_, v_inst_535_, v_inst_536_, v_constName_537_, v_skipRealize_538_);
return v___x_539_;
}
}
LEAN_EXPORT void l_Lean_getAsyncConstInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_534_ = stack[1].m_obj;
lean_object* v_inst_535_ = stack[2].m_obj;
lean_object* v_inst_536_ = stack[3].m_obj;
lean_object* v_constName_537_ = stack[4].m_obj;
uint8_t v_skipRealize_538_ = stack[5].m_num;
lean_object* v_res_540_;
v_res_540_ = l_Lean_getAsyncConstInfo(lean_box(0), v_inst_534_, v_inst_535_, v_inst_536_, v_constName_537_, v_skipRealize_538_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___boxed(lean_object* v_m_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_constName_545_, lean_object* v_skipRealize_546_){
_start:
{
uint8_t v_skipRealize_boxed_547_; lean_object* v_res_548_; 
v_skipRealize_boxed_547_ = lean_unbox(v_skipRealize_546_);
v_res_548_ = l_Lean_getAsyncConstInfo(v_m_541_, v_inst_542_, v_inst_543_, v_inst_544_, v_constName_545_, v_skipRealize_boxed_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isInductiveCore_x3f_spec__0(lean_object* v_msg_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(0);
v___x_551_ = lean_panic_fn_borrowed(v___x_550_, v_msg_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_isInductiveCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_556_ = lean_unsigned_to_nat(11u);
v___x_557_ = lean_unsigned_to_nat(105u);
v___x_558_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__1));
v___x_559_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_560_ = l_mkPanicMessageWithDecl(v___x_559_, v___x_558_, v___x_557_, v___x_556_, v___x_555_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductiveCore_x3f(lean_object* v_env_561_, lean_object* v_declName_562_){
_start:
{
uint8_t v___x_563_; lean_object* v___x_564_; 
v___x_563_ = 0;
v___x_564_ = l_Lean_Environment_findAsync_x3f(v_env_561_, v_declName_562_, v___x_563_);
if (lean_obj_tag(v___x_564_) == 1)
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_578_; 
v_val_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_578_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_578_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_578_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint8_t v_kind_569_; 
v_kind_569_ = lean_ctor_get_uint8(v_val_565_, sizeof(void*)*3);
if (v_kind_569_ == 5)
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_565_);
if (lean_obj_tag(v___x_570_) == 5)
{
lean_object* v_val_571_; lean_object* v___x_573_; 
v_val_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_val_571_);
lean_dec_ref_known(v___x_570_, 1);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_val_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_val_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v___x_570_);
lean_del_object(v___x_567_);
v___x_575_ = lean_obj_once(&l_Lean_isInductiveCore_x3f___closed__3, &l_Lean_isInductiveCore_x3f___closed__3_once, _init_l_Lean_isInductiveCore_x3f___closed__3);
v___x_576_ = l_panic___at___00Lean_isInductiveCore_x3f_spec__0(v___x_575_);
return v___x_576_;
}
}
else
{
lean_object* v___x_577_; 
lean_del_object(v___x_567_);
lean_dec(v_val_565_);
v___x_577_ = lean_box(0);
return v___x_577_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v___x_564_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg___lam__0(lean_object* v_declName_580_, lean_object* v_toPure_581_, lean_object* v_____do__lift_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = l_Lean_isInductiveCore_x3f(v_____do__lift_582_, v_declName_580_);
v___x_584_ = lean_apply_2(v_toPure_581_, lean_box(0), v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg(lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_declName_587_){
_start:
{
lean_object* v_toApplicative_588_; lean_object* v_toBind_589_; lean_object* v_getEnv_590_; lean_object* v_toPure_591_; lean_object* v___f_592_; lean_object* v___x_593_; 
v_toApplicative_588_ = lean_ctor_get(v_inst_585_, 0);
lean_inc_ref(v_toApplicative_588_);
v_toBind_589_ = lean_ctor_get(v_inst_585_, 1);
lean_inc(v_toBind_589_);
lean_dec_ref(v_inst_585_);
v_getEnv_590_ = lean_ctor_get(v_inst_586_, 0);
lean_inc(v_getEnv_590_);
lean_dec_ref(v_inst_586_);
v_toPure_591_ = lean_ctor_get(v_toApplicative_588_, 1);
lean_inc(v_toPure_591_);
lean_dec_ref(v_toApplicative_588_);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_isInductive_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_592_, 0, v_declName_587_);
lean_closure_set(v___f_592_, 1, v_toPure_591_);
v___x_593_ = lean_apply_4(v_toBind_589_, lean_box(0), lean_box(0), v_getEnv_590_, v___f_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f(lean_object* v_m_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_declName_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_isInductive_x3f___redArg(v_inst_595_, v_inst_596_, v_declName_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_600_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_601_ = lean_unsigned_to_nat(11u);
v___x_602_ = lean_unsigned_to_nat(115u);
v___x_603_ = ((lean_object*)(l_Lean_isDefn_x3f___redArg___lam__0___closed__0));
v___x_604_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_605_ = l_mkPanicMessageWithDecl(v___x_604_, v___x_603_, v___x_602_, v___x_601_, v___x_600_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg___lam__0(lean_object* v_toPure_606_, lean_object* v_constName_607_, lean_object* v___x_608_, lean_object* v_____do__lift_609_){
_start:
{
uint8_t v___x_613_; lean_object* v___x_614_; 
v___x_613_ = 0;
v___x_614_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_609_, v_constName_607_, v___x_613_);
if (lean_obj_tag(v___x_614_) == 1)
{
lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_628_; 
v_val_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_628_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_628_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_628_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v_kind_619_; 
v_kind_619_ = lean_ctor_get_uint8(v_val_615_, sizeof(void*)*3);
if (v_kind_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_615_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_val_621_; lean_object* v___x_623_; 
v_val_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_val_621_);
lean_dec_ref_known(v___x_620_, 1);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_val_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_val_621_);
v___x_623_ = v_reuseFailAlloc_625_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_apply_2(v_toPure_606_, lean_box(0), v___x_623_);
return v___x_624_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v___x_620_);
lean_del_object(v___x_617_);
lean_dec(v_toPure_606_);
v___x_626_ = lean_obj_once(&l_Lean_isDefn_x3f___redArg___lam__0___closed__1, &l_Lean_isDefn_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isDefn_x3f___redArg___lam__0___closed__1);
v___x_627_ = l_panic___redArg(v___x_608_, v___x_626_);
return v___x_627_;
}
}
else
{
lean_del_object(v___x_617_);
lean_dec(v_val_615_);
goto v___jp_610_;
}
}
}
else
{
lean_dec(v___x_614_);
goto v___jp_610_;
}
v___jp_610_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(0);
v___x_612_ = lean_apply_2(v_toPure_606_, lean_box(0), v___x_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg___lam__0___boxed(lean_object* v_toPure_629_, lean_object* v_constName_630_, lean_object* v___x_631_, lean_object* v_____do__lift_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_isDefn_x3f___redArg___lam__0(v_toPure_629_, v_constName_630_, v___x_631_, v_____do__lift_632_);
lean_dec(v___x_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___redArg(lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_constName_636_){
_start:
{
lean_object* v_toApplicative_637_; lean_object* v_toBind_638_; lean_object* v_getEnv_639_; lean_object* v_toPure_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___f_643_; lean_object* v___x_644_; 
v_toApplicative_637_ = lean_ctor_get(v_inst_634_, 0);
v_toBind_638_ = lean_ctor_get(v_inst_634_, 1);
lean_inc(v_toBind_638_);
v_getEnv_639_ = lean_ctor_get(v_inst_635_, 0);
lean_inc(v_getEnv_639_);
lean_dec_ref(v_inst_635_);
v_toPure_640_ = lean_ctor_get(v_toApplicative_637_, 1);
lean_inc(v_toPure_640_);
v___x_641_ = lean_box(0);
v___x_642_ = l_instInhabitedOfMonad___redArg(v_inst_634_, v___x_641_);
v___f_643_ = lean_alloc_closure((void*)(l_Lean_isDefn_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_643_, 0, v_toPure_640_);
lean_closure_set(v___f_643_, 1, v_constName_636_);
lean_closure_set(v___f_643_, 2, v___x_642_);
v___x_644_ = lean_apply_4(v_toBind_638_, lean_box(0), lean_box(0), v_getEnv_639_, v___f_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f(lean_object* v_m_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_constName_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_isDefn_x3f___redArg(v_inst_646_, v_inst_647_, v_constName_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_652_ = lean_unsigned_to_nat(11u);
v___x_653_ = lean_unsigned_to_nat(122u);
v___x_654_ = ((lean_object*)(l_Lean_isCtor_x3f___redArg___lam__0___closed__0));
v___x_655_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_656_ = l_mkPanicMessageWithDecl(v___x_655_, v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0(lean_object* v_toPure_657_, lean_object* v_constName_658_, lean_object* v___x_659_, lean_object* v_____do__lift_660_){
_start:
{
uint8_t v___x_664_; lean_object* v___x_665_; 
v___x_664_ = 0;
v___x_665_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_660_, v_constName_658_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_679_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_679_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_679_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_val_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_679_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
uint8_t v_kind_670_; 
v_kind_670_ = lean_ctor_get_uint8(v_val_666_, sizeof(void*)*3);
if (v_kind_670_ == 6)
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_666_);
if (lean_obj_tag(v___x_671_) == 6)
{
lean_object* v_val_672_; lean_object* v___x_674_; 
v_val_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_val_672_);
lean_dec_ref_known(v___x_671_, 1);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_val_672_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_val_672_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_apply_2(v_toPure_657_, lean_box(0), v___x_674_);
return v___x_675_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec_ref(v___x_671_);
lean_del_object(v___x_668_);
lean_dec(v_toPure_657_);
v___x_677_ = lean_obj_once(&l_Lean_isCtor_x3f___redArg___lam__0___closed__1, &l_Lean_isCtor_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isCtor_x3f___redArg___lam__0___closed__1);
v___x_678_ = l_panic___redArg(v___x_659_, v___x_677_);
return v___x_678_;
}
}
else
{
lean_del_object(v___x_668_);
lean_dec(v_val_666_);
goto v___jp_661_;
}
}
}
else
{
lean_dec(v___x_665_);
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_box(0);
v___x_663_ = lean_apply_2(v_toPure_657_, lean_box(0), v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg___lam__0___boxed(lean_object* v_toPure_680_, lean_object* v_constName_681_, lean_object* v___x_682_, lean_object* v_____do__lift_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_isCtor_x3f___redArg___lam__0(v_toPure_680_, v_constName_681_, v___x_682_, v_____do__lift_683_);
lean_dec(v___x_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___redArg(lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_constName_687_){
_start:
{
lean_object* v_toApplicative_688_; lean_object* v_toBind_689_; lean_object* v_getEnv_690_; lean_object* v_toPure_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; 
v_toApplicative_688_ = lean_ctor_get(v_inst_685_, 0);
v_toBind_689_ = lean_ctor_get(v_inst_685_, 1);
lean_inc(v_toBind_689_);
v_getEnv_690_ = lean_ctor_get(v_inst_686_, 0);
lean_inc(v_getEnv_690_);
lean_dec_ref(v_inst_686_);
v_toPure_691_ = lean_ctor_get(v_toApplicative_688_, 1);
lean_inc(v_toPure_691_);
v___x_692_ = lean_box(0);
v___x_693_ = l_instInhabitedOfMonad___redArg(v_inst_685_, v___x_692_);
v___f_694_ = lean_alloc_closure((void*)(l_Lean_isCtor_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_694_, 0, v_toPure_691_);
lean_closure_set(v___f_694_, 1, v_constName_687_);
lean_closure_set(v___f_694_, 2, v___x_693_);
v___x_695_ = lean_apply_4(v_toBind_689_, lean_box(0), lean_box(0), v_getEnv_690_, v___f_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f(lean_object* v_m_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_constName_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_isCtor_x3f___redArg(v_inst_697_, v_inst_698_, v_constName_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_702_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__2));
v___x_703_ = lean_unsigned_to_nat(11u);
v___x_704_ = lean_unsigned_to_nat(129u);
v___x_705_ = ((lean_object*)(l_Lean_isRec_x3f___redArg___lam__0___closed__0));
v___x_706_ = ((lean_object*)(l_Lean_isInductiveCore_x3f___closed__0));
v___x_707_ = l_mkPanicMessageWithDecl(v___x_706_, v___x_705_, v___x_704_, v___x_703_, v___x_702_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0(lean_object* v_toPure_708_, lean_object* v_constName_709_, lean_object* v___x_710_, lean_object* v_____do__lift_711_){
_start:
{
uint8_t v___x_715_; lean_object* v___x_716_; 
v___x_715_ = 0;
v___x_716_ = l_Lean_Environment_findAsync_x3f(v_____do__lift_711_, v_constName_709_, v___x_715_);
if (lean_obj_tag(v___x_716_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_730_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_730_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_val_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
uint8_t v_kind_721_; 
v_kind_721_ = lean_ctor_get_uint8(v_val_717_, sizeof(void*)*3);
if (v_kind_721_ == 7)
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_717_);
if (lean_obj_tag(v___x_722_) == 7)
{
lean_object* v_val_723_; lean_object* v___x_725_; 
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_val_723_);
lean_dec_ref_known(v___x_722_, 1);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_val_723_);
v___x_725_ = v___x_719_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_val_723_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_apply_2(v_toPure_708_, lean_box(0), v___x_725_);
return v___x_726_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v___x_722_);
lean_del_object(v___x_719_);
lean_dec(v_toPure_708_);
v___x_728_ = lean_obj_once(&l_Lean_isRec_x3f___redArg___lam__0___closed__1, &l_Lean_isRec_x3f___redArg___lam__0___closed__1_once, _init_l_Lean_isRec_x3f___redArg___lam__0___closed__1);
v___x_729_ = l_panic___redArg(v___x_710_, v___x_728_);
return v___x_729_;
}
}
else
{
lean_del_object(v___x_719_);
lean_dec(v_val_717_);
goto v___jp_712_;
}
}
}
else
{
lean_dec(v___x_716_);
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_apply_2(v_toPure_708_, lean_box(0), v___x_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg___lam__0___boxed(lean_object* v_toPure_731_, lean_object* v_constName_732_, lean_object* v___x_733_, lean_object* v_____do__lift_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_isRec_x3f___redArg___lam__0(v_toPure_731_, v_constName_732_, v___x_733_, v_____do__lift_734_);
lean_dec(v___x_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f___redArg(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_constName_738_){
_start:
{
lean_object* v_toApplicative_739_; lean_object* v_toBind_740_; lean_object* v_getEnv_741_; lean_object* v_toPure_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; 
v_toApplicative_739_ = lean_ctor_get(v_inst_736_, 0);
v_toBind_740_ = lean_ctor_get(v_inst_736_, 1);
lean_inc(v_toBind_740_);
v_getEnv_741_ = lean_ctor_get(v_inst_737_, 0);
lean_inc(v_getEnv_741_);
lean_dec_ref(v_inst_737_);
v_toPure_742_ = lean_ctor_get(v_toApplicative_739_, 1);
lean_inc(v_toPure_742_);
v___x_743_ = lean_box(0);
v___x_744_ = l_instInhabitedOfMonad___redArg(v_inst_736_, v___x_743_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_isRec_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_745_, 0, v_toPure_742_);
lean_closure_set(v___f_745_, 1, v_constName_738_);
lean_closure_set(v___f_745_, 2, v___x_744_);
v___x_746_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v_getEnv_741_, v___f_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec_x3f(lean_object* v_m_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_constName_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_isRec_x3f___redArg(v_inst_748_, v_inst_749_, v_constName_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0(lean_object* v_constName_753_, lean_object* v_toPure_754_, lean_object* v_info_755_){
_start:
{
lean_object* v_levelParams_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_levelParams_756_ = lean_ctor_get(v_info_755_, 1);
lean_inc(v_levelParams_756_);
lean_dec_ref(v_info_755_);
v___x_757_ = ((lean_object*)(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0));
v___x_758_ = lean_box(0);
v___x_759_ = l_List_mapTR_loop___redArg(v___x_757_, v_levelParams_756_, v___x_758_);
v___x_760_ = l_Lean_mkConst(v_constName_753_, v___x_759_);
v___x_761_ = lean_apply_2(v_toPure_754_, lean_box(0), v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_constName_765_){
_start:
{
lean_object* v_toApplicative_766_; lean_object* v_toBind_767_; lean_object* v_toPure_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; 
v_toApplicative_766_ = lean_ctor_get(v_inst_762_, 0);
v_toBind_767_ = lean_ctor_get(v_inst_762_, 1);
lean_inc(v_toBind_767_);
v_toPure_768_ = lean_ctor_get(v_toApplicative_766_, 1);
lean_inc(v_toPure_768_);
lean_inc(v_constName_765_);
v___x_769_ = l_Lean_getConstVal___redArg(v_inst_762_, v_inst_763_, v_inst_764_, v_constName_765_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_mkConstWithLevelParams___redArg___lam__0), 3, 2);
lean_closure_set(v___f_770_, 0, v_constName_765_);
lean_closure_set(v___f_770_, 1, v_toPure_768_);
v___x_771_ = lean_apply_4(v_toBind_767_, lean_box(0), lean_box(0), v___x_769_, v___f_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object* v_m_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_constName_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_773_, v_inst_774_, v_inst_775_, v_constName_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg___lam__0(lean_object* v_constName_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_toPure_787_, lean_object* v_____do__lift_788_){
_start:
{
if (lean_obj_tag(v_____do__lift_788_) == 0)
{
lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_toPure_787_);
v___x_789_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_790_ = 0;
v___x_791_ = l_Lean_MessageData_ofConstName(v_constName_784_, v___x_790_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_789_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__3, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__3_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_throwError___redArg(v_inst_785_, v_inst_786_, v___x_794_);
return v___x_795_;
}
else
{
lean_object* v_val_796_; lean_object* v___x_797_; 
lean_dec_ref(v_inst_786_);
lean_dec_ref(v_inst_785_);
lean_dec(v_constName_784_);
v_val_796_ = lean_ctor_get(v_____do__lift_788_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v_____do__lift_788_, 1);
v___x_797_ = lean_apply_2(v_toPure_787_, lean_box(0), v_val_796_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_constName_801_){
_start:
{
lean_object* v_toApplicative_802_; lean_object* v_toBind_803_; lean_object* v_getEnv_804_; lean_object* v_toPure_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_toApplicative_802_ = lean_ctor_get(v_inst_798_, 0);
v_toBind_803_ = lean_ctor_get(v_inst_798_, 1);
lean_inc_n(v_toBind_803_, 2);
v_getEnv_804_ = lean_ctor_get(v_inst_799_, 0);
lean_inc(v_getEnv_804_);
lean_dec_ref(v_inst_799_);
v_toPure_805_ = lean_ctor_get(v_toApplicative_802_, 1);
lean_inc_n(v_toPure_805_, 2);
v___x_806_ = lean_box(0);
lean_inc_ref(v_inst_798_);
lean_inc(v_constName_801_);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_getConstInfoDefn___redArg___lam__0), 5, 4);
lean_closure_set(v___f_807_, 0, v_constName_801_);
lean_closure_set(v___f_807_, 1, v_inst_798_);
lean_closure_set(v___f_807_, 2, v_inst_800_);
lean_closure_set(v___f_807_, 3, v_toPure_805_);
v___x_808_ = l_instInhabitedOfMonad___redArg(v_inst_798_, v___x_806_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_isDefn_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_809_, 0, v_toPure_805_);
lean_closure_set(v___f_809_, 1, v_constName_801_);
lean_closure_set(v___f_809_, 2, v___x_808_);
v___x_810_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v_getEnv_804_, v___f_809_);
v___x_811_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_810_, v___f_807_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object* v_m_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_constName_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_getConstInfoDefn___redArg(v_inst_813_, v_inst_814_, v_inst_815_, v_constName_816_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__0(lean_object* v_constName_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_toPure_824_, lean_object* v_____do__lift_825_){
_start:
{
if (lean_obj_tag(v_____do__lift_825_) == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_toPure_824_);
v___x_826_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_827_ = 0;
v___x_828_ = l_Lean_MessageData_ofConstName(v_constName_821_, v___x_827_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_826_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_getConstInfoInduct___redArg___lam__0___closed__1, &l_Lean_getConstInfoInduct___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_throwError___redArg(v_inst_822_, v_inst_823_, v___x_831_);
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v___x_834_; 
lean_dec_ref(v_inst_823_);
lean_dec_ref(v_inst_822_);
lean_dec(v_constName_821_);
v_val_833_ = lean_ctor_get(v_____do__lift_825_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_____do__lift_825_, 1);
v___x_834_ = lean_apply_2(v_toPure_824_, lean_box(0), v_val_833_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__1(lean_object* v_constName_835_, lean_object* v_toPure_836_, lean_object* v_____do__lift_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = l_Lean_isInductiveCore_x3f(v_____do__lift_837_, v_constName_835_);
v___x_839_ = lean_apply_2(v_toPure_836_, lean_box(0), v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_constName_843_){
_start:
{
lean_object* v_toApplicative_844_; lean_object* v_toBind_845_; lean_object* v_getEnv_846_; lean_object* v_toPure_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_toApplicative_844_ = lean_ctor_get(v_inst_840_, 0);
v_toBind_845_ = lean_ctor_get(v_inst_840_, 1);
lean_inc_n(v_toBind_845_, 2);
v_getEnv_846_ = lean_ctor_get(v_inst_841_, 0);
lean_inc(v_getEnv_846_);
lean_dec_ref(v_inst_841_);
v_toPure_847_ = lean_ctor_get(v_toApplicative_844_, 1);
lean_inc_n(v_toPure_847_, 2);
lean_inc(v_constName_843_);
v___f_848_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__0), 5, 4);
lean_closure_set(v___f_848_, 0, v_constName_843_);
lean_closure_set(v___f_848_, 1, v_inst_840_);
lean_closure_set(v___f_848_, 2, v_inst_842_);
lean_closure_set(v___f_848_, 3, v_toPure_847_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__1), 3, 2);
lean_closure_set(v___f_849_, 0, v_constName_843_);
lean_closure_set(v___f_849_, 1, v_toPure_847_);
v___x_850_ = lean_apply_4(v_toBind_845_, lean_box(0), lean_box(0), v_getEnv_846_, v___f_849_);
v___x_851_ = lean_apply_4(v_toBind_845_, lean_box(0), lean_box(0), v___x_850_, v___f_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object* v_m_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_constName_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_getConstInfoInduct___redArg(v_inst_853_, v_inst_854_, v_inst_855_, v_constName_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg___lam__0(lean_object* v_constName_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_toPure_864_, lean_object* v_____do__lift_865_){
_start:
{
if (lean_obj_tag(v_____do__lift_865_) == 0)
{
lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_toPure_864_);
v___x_866_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_867_ = 0;
v___x_868_ = l_Lean_MessageData_ofConstName(v_constName_861_, v___x_867_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_obj_once(&l_Lean_getConstInfoCtor___redArg___lam__0___closed__1, &l_Lean_getConstInfoCtor___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_throwError___redArg(v_inst_862_, v_inst_863_, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; 
lean_dec_ref(v_inst_863_);
lean_dec_ref(v_inst_862_);
lean_dec(v_constName_861_);
v_val_873_ = lean_ctor_get(v_____do__lift_865_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v_____do__lift_865_, 1);
v___x_874_ = lean_apply_2(v_toPure_864_, lean_box(0), v_val_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg(lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_constName_878_){
_start:
{
lean_object* v_toApplicative_879_; lean_object* v_toBind_880_; lean_object* v_getEnv_881_; lean_object* v_toPure_882_; lean_object* v___x_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_toApplicative_879_ = lean_ctor_get(v_inst_875_, 0);
v_toBind_880_ = lean_ctor_get(v_inst_875_, 1);
lean_inc_n(v_toBind_880_, 2);
v_getEnv_881_ = lean_ctor_get(v_inst_876_, 0);
lean_inc(v_getEnv_881_);
lean_dec_ref(v_inst_876_);
v_toPure_882_ = lean_ctor_get(v_toApplicative_879_, 1);
lean_inc_n(v_toPure_882_, 2);
v___x_883_ = lean_box(0);
lean_inc_ref(v_inst_875_);
lean_inc(v_constName_878_);
v___f_884_ = lean_alloc_closure((void*)(l_Lean_getConstInfoCtor___redArg___lam__0), 5, 4);
lean_closure_set(v___f_884_, 0, v_constName_878_);
lean_closure_set(v___f_884_, 1, v_inst_875_);
lean_closure_set(v___f_884_, 2, v_inst_877_);
lean_closure_set(v___f_884_, 3, v_toPure_882_);
v___x_885_ = l_instInhabitedOfMonad___redArg(v_inst_875_, v___x_883_);
v___f_886_ = lean_alloc_closure((void*)(l_Lean_isCtor_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_886_, 0, v_toPure_882_);
lean_closure_set(v___f_886_, 1, v_constName_878_);
lean_closure_set(v___f_886_, 2, v___x_885_);
v___x_887_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v_getEnv_881_, v___f_886_);
v___x_888_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_887_, v___f_884_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object* v_m_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_constName_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_getConstInfoCtor___redArg(v_inst_890_, v_inst_891_, v_inst_892_, v_constName_893_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_getConstInfoRec___redArg___lam__0___closed__0));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg___lam__0(lean_object* v_constName_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_toPure_901_, lean_object* v_____do__lift_902_){
_start:
{
if (lean_obj_tag(v_____do__lift_902_) == 0)
{
lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v_toPure_901_);
v___x_903_ = lean_obj_once(&l_Lean_getConstInfoDefn___redArg___lam__0___closed__1, &l_Lean_getConstInfoDefn___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
v___x_904_ = 0;
v___x_905_ = l_Lean_MessageData_ofConstName(v_constName_898_, v___x_904_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_903_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l_Lean_getConstInfoRec___redArg___lam__0___closed__1, &l_Lean_getConstInfoRec___redArg___lam__0___closed__1_once, _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_throwError___redArg(v_inst_899_, v_inst_900_, v___x_908_);
return v___x_909_;
}
else
{
lean_object* v_val_910_; lean_object* v___x_911_; 
lean_dec_ref(v_inst_900_);
lean_dec_ref(v_inst_899_);
lean_dec(v_constName_898_);
v_val_910_ = lean_ctor_get(v_____do__lift_902_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v_____do__lift_902_, 1);
v___x_911_ = lean_apply_2(v_toPure_901_, lean_box(0), v_val_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg(lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_constName_915_){
_start:
{
lean_object* v_toApplicative_916_; lean_object* v_toBind_917_; lean_object* v_getEnv_918_; lean_object* v_toPure_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_toApplicative_916_ = lean_ctor_get(v_inst_912_, 0);
v_toBind_917_ = lean_ctor_get(v_inst_912_, 1);
lean_inc_n(v_toBind_917_, 2);
v_getEnv_918_ = lean_ctor_get(v_inst_913_, 0);
lean_inc(v_getEnv_918_);
lean_dec_ref(v_inst_913_);
v_toPure_919_ = lean_ctor_get(v_toApplicative_916_, 1);
lean_inc_n(v_toPure_919_, 2);
v___x_920_ = lean_box(0);
lean_inc_ref(v_inst_912_);
lean_inc(v_constName_915_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_getConstInfoRec___redArg___lam__0), 5, 4);
lean_closure_set(v___f_921_, 0, v_constName_915_);
lean_closure_set(v___f_921_, 1, v_inst_912_);
lean_closure_set(v___f_921_, 2, v_inst_914_);
lean_closure_set(v___f_921_, 3, v_toPure_919_);
v___x_922_ = l_instInhabitedOfMonad___redArg(v_inst_912_, v___x_920_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_isRec_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_923_, 0, v_toPure_919_);
lean_closure_set(v___f_923_, 1, v_constName_915_);
lean_closure_set(v___f_923_, 2, v___x_922_);
v___x_924_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v_getEnv_918_, v___f_923_);
v___x_925_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_924_, v___f_921_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object* v_m_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_constName_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_getConstInfoRec___redArg(v_inst_927_, v_inst_928_, v_inst_929_, v_constName_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__0(lean_object* v_k_932_, lean_object* v_val_933_, lean_object* v_us_934_, lean_object* v_failK_935_, lean_object* v_____do__lift_936_){
_start:
{
if (lean_obj_tag(v_____do__lift_936_) == 6)
{
lean_object* v_val_937_; lean_object* v___x_938_; 
lean_dec(v_failK_935_);
v_val_937_ = lean_ctor_get(v_____do__lift_936_, 0);
lean_inc_ref(v_val_937_);
lean_dec_ref_known(v_____do__lift_936_, 1);
v___x_938_ = lean_apply_3(v_k_932_, v_val_933_, v_us_934_, v_val_937_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v_____do__lift_936_);
lean_dec(v_us_934_);
lean_dec_ref(v_val_933_);
lean_dec(v_k_932_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_apply_1(v_failK_935_, v___x_939_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__1(lean_object* v_declName_941_, lean_object* v_failK_942_, lean_object* v_k_943_, lean_object* v_us_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_toBind_948_, lean_object* v_____do__lift_949_){
_start:
{
uint8_t v___x_953_; lean_object* v___x_954_; 
v___x_953_ = 0;
v___x_954_ = l_Lean_Environment_find_x3f(v_____do__lift_949_, v_declName_941_, v___x_953_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_toBind_948_);
lean_dec_ref(v_inst_947_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
lean_dec(v_us_944_);
lean_dec(v_k_943_);
v___x_955_ = lean_box(0);
v___x_956_ = lean_apply_1(v_failK_942_, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v_val_957_; 
v_val_957_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___x_954_, 1);
if (lean_obj_tag(v_val_957_) == 5)
{
lean_object* v_val_958_; lean_object* v_ctors_959_; 
v_val_958_ = lean_ctor_get(v_val_957_, 0);
lean_inc_ref(v_val_958_);
lean_dec_ref_known(v_val_957_, 1);
v_ctors_959_ = lean_ctor_get(v_val_958_, 4);
if (lean_obj_tag(v_ctors_959_) == 1)
{
lean_object* v_tail_960_; 
v_tail_960_ = lean_ctor_get(v_ctors_959_, 1);
if (lean_obj_tag(v_tail_960_) == 0)
{
lean_object* v_head_961_; lean_object* v___f_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_head_961_ = lean_ctor_get(v_ctors_959_, 0);
lean_inc(v_head_961_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(v___f_962_, 0, v_k_943_);
lean_closure_set(v___f_962_, 1, v_val_958_);
lean_closure_set(v___f_962_, 2, v_us_944_);
lean_closure_set(v___f_962_, 3, v_failK_942_);
v___x_963_ = l_Lean_getConstInfo___redArg(v_inst_945_, v_inst_946_, v_inst_947_, v_head_961_);
v___x_964_ = lean_apply_4(v_toBind_948_, lean_box(0), lean_box(0), v___x_963_, v___f_962_);
return v___x_964_;
}
else
{
lean_dec_ref(v_val_958_);
lean_dec(v_toBind_948_);
lean_dec_ref(v_inst_947_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
lean_dec(v_us_944_);
lean_dec(v_k_943_);
goto v___jp_950_;
}
}
else
{
lean_dec_ref(v_val_958_);
lean_dec(v_toBind_948_);
lean_dec_ref(v_inst_947_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
lean_dec(v_us_944_);
lean_dec(v_k_943_);
goto v___jp_950_;
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_val_957_);
lean_dec(v_toBind_948_);
lean_dec_ref(v_inst_947_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
lean_dec(v_us_944_);
lean_dec(v_k_943_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_apply_1(v_failK_942_, v___x_965_);
return v___x_966_;
}
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_box(0);
v___x_952_ = lean_apply_1(v_failK_942_, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg(lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_e_970_, lean_object* v_failK_971_, lean_object* v_k_972_){
_start:
{
if (lean_obj_tag(v_e_970_) == 4)
{
lean_object* v_toBind_973_; lean_object* v_declName_974_; lean_object* v_us_975_; lean_object* v_getEnv_976_; lean_object* v___f_977_; lean_object* v___x_978_; 
v_toBind_973_ = lean_ctor_get(v_inst_967_, 1);
lean_inc_n(v_toBind_973_, 2);
v_declName_974_ = lean_ctor_get(v_e_970_, 0);
lean_inc(v_declName_974_);
v_us_975_ = lean_ctor_get(v_e_970_, 1);
lean_inc(v_us_975_);
lean_dec_ref_known(v_e_970_, 2);
v_getEnv_976_ = lean_ctor_get(v_inst_968_, 0);
lean_inc(v_getEnv_976_);
v___f_977_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_977_, 0, v_declName_974_);
lean_closure_set(v___f_977_, 1, v_failK_971_);
lean_closure_set(v___f_977_, 2, v_k_972_);
lean_closure_set(v___f_977_, 3, v_us_975_);
lean_closure_set(v___f_977_, 4, v_inst_967_);
lean_closure_set(v___f_977_, 5, v_inst_968_);
lean_closure_set(v___f_977_, 6, v_inst_969_);
lean_closure_set(v___f_977_, 7, v_toBind_973_);
v___x_978_ = lean_apply_4(v_toBind_973_, lean_box(0), lean_box(0), v_getEnv_976_, v___f_977_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec(v_k_972_);
lean_dec_ref(v_e_970_);
lean_dec_ref(v_inst_969_);
lean_dec_ref(v_inst_968_);
lean_dec_ref(v_inst_967_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_apply_1(v_failK_971_, v___x_979_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure(lean_object* v_m_981_, lean_object* v_00_u03b1_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_e_986_, lean_object* v_failK_987_, lean_object* v_k_988_){
_start:
{
if (lean_obj_tag(v_e_986_) == 4)
{
lean_object* v_toBind_989_; lean_object* v_declName_990_; lean_object* v_us_991_; lean_object* v_getEnv_992_; lean_object* v___f_993_; lean_object* v___x_994_; 
v_toBind_989_ = lean_ctor_get(v_inst_983_, 1);
lean_inc_n(v_toBind_989_, 2);
v_declName_990_ = lean_ctor_get(v_e_986_, 0);
lean_inc(v_declName_990_);
v_us_991_ = lean_ctor_get(v_e_986_, 1);
lean_inc(v_us_991_);
lean_dec_ref_known(v_e_986_, 2);
v_getEnv_992_ = lean_ctor_get(v_inst_984_, 0);
lean_inc(v_getEnv_992_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_993_, 0, v_declName_990_);
lean_closure_set(v___f_993_, 1, v_failK_987_);
lean_closure_set(v___f_993_, 2, v_k_988_);
lean_closure_set(v___f_993_, 3, v_us_991_);
lean_closure_set(v___f_993_, 4, v_inst_983_);
lean_closure_set(v___f_993_, 5, v_inst_984_);
lean_closure_set(v___f_993_, 6, v_inst_985_);
lean_closure_set(v___f_993_, 7, v_toBind_989_);
v___x_994_ = lean_apply_4(v_toBind_989_, lean_box(0), lean_box(0), v_getEnv_992_, v___f_993_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_k_988_);
lean_dec_ref(v_e_986_);
lean_dec_ref(v_inst_985_);
lean_dec_ref(v_inst_984_);
lean_dec_ref(v_inst_983_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_apply_1(v_failK_987_, v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg___lam__1(lean_object* v_declName_997_, lean_object* v_failK_998_, lean_object* v_k_999_, lean_object* v_us_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_toBind_1004_, lean_object* v_____do__lift_1005_){
_start:
{
uint8_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = 0;
v___x_1013_ = l_Lean_Environment_find_x3f(v_____do__lift_1005_, v_declName_997_, v___x_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
lean_dec(v_us_1000_);
lean_dec(v_k_999_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_apply_1(v_failK_998_, v___x_1014_);
return v___x_1015_;
}
else
{
lean_object* v_val_1016_; 
v_val_1016_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1013_, 1);
if (lean_obj_tag(v_val_1016_) == 5)
{
lean_object* v_val_1017_; uint8_t v_isRec_1018_; 
v_val_1017_ = lean_ctor_get(v_val_1016_, 0);
lean_inc_ref(v_val_1017_);
lean_dec_ref_known(v_val_1016_, 1);
v_isRec_1018_ = lean_ctor_get_uint8(v_val_1017_, sizeof(void*)*6);
if (v_isRec_1018_ == 0)
{
lean_object* v_numIndices_1019_; lean_object* v_ctors_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_numIndices_1019_ = lean_ctor_get(v_val_1017_, 2);
v_ctors_1020_ = lean_ctor_get(v_val_1017_, 4);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_nat_dec_eq(v_numIndices_1019_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v_val_1017_);
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
lean_dec(v_us_1000_);
lean_dec(v_k_999_);
goto v___jp_1006_;
}
else
{
if (lean_obj_tag(v_ctors_1020_) == 1)
{
lean_object* v_tail_1023_; 
v_tail_1023_ = lean_ctor_get(v_ctors_1020_, 1);
if (lean_obj_tag(v_tail_1023_) == 0)
{
lean_object* v_head_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_head_1024_ = lean_ctor_get(v_ctors_1020_, 0);
lean_inc(v_head_1024_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1025_, 0, v_k_999_);
lean_closure_set(v___f_1025_, 1, v_val_1017_);
lean_closure_set(v___f_1025_, 2, v_us_1000_);
lean_closure_set(v___f_1025_, 3, v_failK_998_);
v___x_1026_ = l_Lean_getConstInfo___redArg(v_inst_1001_, v_inst_1002_, v_inst_1003_, v_head_1024_);
v___x_1027_ = lean_apply_4(v_toBind_1004_, lean_box(0), lean_box(0), v___x_1026_, v___f_1025_);
return v___x_1027_;
}
else
{
lean_dec_ref(v_val_1017_);
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
lean_dec(v_us_1000_);
lean_dec(v_k_999_);
goto v___jp_1009_;
}
}
else
{
lean_dec_ref(v_val_1017_);
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
lean_dec(v_us_1000_);
lean_dec(v_k_999_);
goto v___jp_1009_;
}
}
}
else
{
lean_dec_ref(v_val_1017_);
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
lean_dec(v_us_1000_);
lean_dec(v_k_999_);
goto v___jp_1006_;
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec(v_val_1016_);
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
lean_dec(v_us_1000_);
lean_dec(v_k_999_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_apply_1(v_failK_998_, v___x_1028_);
return v___x_1029_;
}
}
v___jp_1006_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_apply_1(v_failK_998_, v___x_1007_);
return v___x_1008_;
}
v___jp_1009_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_apply_1(v_failK_998_, v___x_1010_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure___redArg(lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_e_1033_, lean_object* v_failK_1034_, lean_object* v_k_1035_){
_start:
{
if (lean_obj_tag(v_e_1033_) == 4)
{
lean_object* v_toBind_1036_; lean_object* v_declName_1037_; lean_object* v_us_1038_; lean_object* v_getEnv_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; 
v_toBind_1036_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc_n(v_toBind_1036_, 2);
v_declName_1037_ = lean_ctor_get(v_e_1033_, 0);
lean_inc(v_declName_1037_);
v_us_1038_ = lean_ctor_get(v_e_1033_, 1);
lean_inc(v_us_1038_);
lean_dec_ref_known(v_e_1033_, 2);
v_getEnv_1039_ = lean_ctor_get(v_inst_1031_, 0);
lean_inc(v_getEnv_1039_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_matchConstNonRecStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1040_, 0, v_declName_1037_);
lean_closure_set(v___f_1040_, 1, v_failK_1034_);
lean_closure_set(v___f_1040_, 2, v_k_1035_);
lean_closure_set(v___f_1040_, 3, v_us_1038_);
lean_closure_set(v___f_1040_, 4, v_inst_1030_);
lean_closure_set(v___f_1040_, 5, v_inst_1031_);
lean_closure_set(v___f_1040_, 6, v_inst_1032_);
lean_closure_set(v___f_1040_, 7, v_toBind_1036_);
v___x_1041_ = lean_apply_4(v_toBind_1036_, lean_box(0), lean_box(0), v_getEnv_1039_, v___f_1040_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v_k_1035_);
lean_dec_ref(v_e_1033_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_inst_1031_);
lean_dec_ref(v_inst_1030_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_apply_1(v_failK_1034_, v___x_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstNonRecStructure(lean_object* v_m_1044_, lean_object* v_00_u03b1_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_e_1049_, lean_object* v_failK_1050_, lean_object* v_k_1051_){
_start:
{
if (lean_obj_tag(v_e_1049_) == 4)
{
lean_object* v_toBind_1052_; lean_object* v_declName_1053_; lean_object* v_us_1054_; lean_object* v_getEnv_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; 
v_toBind_1052_ = lean_ctor_get(v_inst_1046_, 1);
lean_inc_n(v_toBind_1052_, 2);
v_declName_1053_ = lean_ctor_get(v_e_1049_, 0);
lean_inc(v_declName_1053_);
v_us_1054_ = lean_ctor_get(v_e_1049_, 1);
lean_inc(v_us_1054_);
lean_dec_ref_known(v_e_1049_, 2);
v_getEnv_1055_ = lean_ctor_get(v_inst_1047_, 0);
lean_inc(v_getEnv_1055_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lean_matchConstNonRecStructure___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1056_, 0, v_declName_1053_);
lean_closure_set(v___f_1056_, 1, v_failK_1050_);
lean_closure_set(v___f_1056_, 2, v_k_1051_);
lean_closure_set(v___f_1056_, 3, v_us_1054_);
lean_closure_set(v___f_1056_, 4, v_inst_1046_);
lean_closure_set(v___f_1056_, 5, v_inst_1047_);
lean_closure_set(v___f_1056_, 6, v_inst_1048_);
lean_closure_set(v___f_1056_, 7, v_toBind_1052_);
v___x_1057_ = lean_apply_4(v_toBind_1052_, lean_box(0), lean_box(0), v_getEnv_1055_, v___f_1056_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v_k_1051_);
lean_dec_ref(v_e_1049_);
lean_dec_ref(v_inst_1048_);
lean_dec_ref(v_inst_1047_);
lean_dec_ref(v_inst_1046_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_apply_1(v_failK_1050_, v___x_1058_);
return v___x_1059_;
}
}
}
LEAN_EXPORT void l_Lean_hasCompileError_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1060_ = stack[0].m_obj;
lean_object* v_constName_1061_ = stack[1].m_obj;
uint8_t v_res_1062_;
v_res_1062_ = lean_has_compile_error(v_env_1060_, v_constName_1061_);
stack->m_num = v_res_1062_;
}
LEAN_EXPORT lean_object* l_Lean_hasCompileError___boxed(lean_object* v_env_1063_, lean_object* v_constName_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = lean_has_compile_error(v_env_1063_, v_constName_1064_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
lean_object* l_Lean_evalConst___redArg___lam__0(lean_object* v_____do__lift_1067_, lean_object* v_constName_1068_, uint8_t v_checkMeta_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v___x_1072_, lean_object* v_____do__lift_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_Lean_Environment_evalConst___redArg(v_____do__lift_1067_, v_____do__lift_1073_, v_constName_1068_, v_checkMeta_1069_);
v___x_1075_ = l_Lean_ofExcept___redArg(v_inst_1070_, v_inst_1071_, v___x_1072_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT void l_Lean_evalConst___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1067_ = stack[0].m_obj;
lean_object* v_constName_1068_ = stack[1].m_obj;
uint8_t v_checkMeta_1069_ = stack[2].m_num;
lean_object* v_inst_1070_ = stack[3].m_obj;
lean_object* v_inst_1071_ = stack[4].m_obj;
lean_object* v___x_1072_ = stack[5].m_obj;
lean_object* v_____do__lift_1073_ = stack[6].m_obj;
lean_object* v_res_1076_;
v_res_1076_ = l_Lean_evalConst___redArg___lam__0(v_____do__lift_1067_, v_constName_1068_, v_checkMeta_1069_, v_inst_1070_, v_inst_1071_, v___x_1072_, v_____do__lift_1073_);
stack->m_obj
 = v_res_1076_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0___boxed(lean_object* v_____do__lift_1077_, lean_object* v_constName_1078_, lean_object* v_checkMeta_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v___x_1082_, lean_object* v_____do__lift_1083_){
_start:
{
uint8_t v_checkMeta_boxed_1084_; lean_object* v_res_1085_; 
v_checkMeta_boxed_1084_ = lean_unbox(v_checkMeta_1079_);
v_res_1085_ = l_Lean_evalConst___redArg___lam__0(v_____do__lift_1077_, v_constName_1078_, v_checkMeta_boxed_1084_, v_inst_1080_, v_inst_1081_, v___x_1082_, v_____do__lift_1083_);
lean_dec_ref(v_____do__lift_1083_);
lean_dec(v_constName_1078_);
lean_dec_ref(v_____do__lift_1077_);
return v_res_1085_;
}
}
lean_object* l_Lean_evalConst___redArg___lam__1(lean_object* v_inst_1086_, lean_object* v_constName_1087_, uint8_t v_checkMeta_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v___x_1091_, lean_object* v_toBind_1092_, lean_object* v_____do__lift_1093_){
_start:
{
lean_object* v_getOptions_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v_getOptions_1094_ = lean_ctor_get(v_inst_1086_, 0);
lean_inc(v_getOptions_1094_);
lean_dec_ref(v_inst_1086_);
v___x_1095_ = lean_box(v_checkMeta_1088_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1096_, 0, v_____do__lift_1093_);
lean_closure_set(v___f_1096_, 1, v_constName_1087_);
lean_closure_set(v___f_1096_, 2, v___x_1095_);
lean_closure_set(v___f_1096_, 3, v_inst_1089_);
lean_closure_set(v___f_1096_, 4, v_inst_1090_);
lean_closure_set(v___f_1096_, 5, v___x_1091_);
v___x_1097_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v_getOptions_1094_, v___f_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT void l_Lean_evalConst___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1086_ = stack[0].m_obj;
lean_object* v_constName_1087_ = stack[1].m_obj;
uint8_t v_checkMeta_1088_ = stack[2].m_num;
lean_object* v_inst_1089_ = stack[3].m_obj;
lean_object* v_inst_1090_ = stack[4].m_obj;
lean_object* v___x_1091_ = stack[5].m_obj;
lean_object* v_toBind_1092_ = stack[6].m_obj;
lean_object* v_____do__lift_1093_ = stack[7].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_Lean_evalConst___redArg___lam__1(v_inst_1086_, v_constName_1087_, v_checkMeta_1088_, v_inst_1089_, v_inst_1090_, v___x_1091_, v_toBind_1092_, v_____do__lift_1093_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1___boxed(lean_object* v_inst_1099_, lean_object* v_constName_1100_, lean_object* v_checkMeta_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v___x_1104_, lean_object* v_toBind_1105_, lean_object* v_____do__lift_1106_){
_start:
{
uint8_t v_checkMeta_boxed_1107_; lean_object* v_res_1108_; 
v_checkMeta_boxed_1107_ = lean_unbox(v_checkMeta_1101_);
v_res_1108_ = l_Lean_evalConst___redArg___lam__1(v_inst_1099_, v_constName_1100_, v_checkMeta_boxed_1107_, v_inst_1102_, v_inst_1103_, v___x_1104_, v_toBind_1105_, v_____do__lift_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__2(lean_object* v_toBind_1109_, lean_object* v_getEnv_1110_, lean_object* v___f_1111_, lean_object* v_____r_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_4(v_toBind_1109_, lean_box(0), lean_box(0), v_getEnv_1110_, v___f_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__3(lean_object* v_constName_1114_, lean_object* v_toBind_1115_, lean_object* v_getEnv_1116_, lean_object* v___f_1117_, lean_object* v___x_1118_, lean_object* v___f_1119_, lean_object* v_____do__lift_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_has_compile_error(v_____do__lift_1120_, v_constName_1114_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec(v___f_1119_);
lean_dec_ref(v___x_1118_);
v___x_1122_ = lean_apply_4(v_toBind_1115_, lean_box(0), lean_box(0), v_getEnv_1116_, v___f_1117_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec(v___f_1117_);
lean_dec(v_getEnv_1116_);
v___x_1123_ = l_Lean_Elab_throwAbortCommand___redArg(v___x_1118_);
v___x_1124_ = lean_apply_4(v_toBind_1115_, lean_box(0), lean_box(0), v___x_1123_, v___f_1119_);
return v___x_1124_;
}
}
}
lean_object* l_Lean_evalConst___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_constName_1130_, uint8_t v_checkMeta_1131_){
_start:
{
lean_object* v_toBind_1132_; lean_object* v_getEnv_1133_; lean_object* v_toMonadExceptOf_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
v_toBind_1132_ = lean_ctor_get(v_inst_1126_, 1);
lean_inc_n(v_toBind_1132_, 4);
v_getEnv_1133_ = lean_ctor_get(v_inst_1127_, 0);
lean_inc_n(v_getEnv_1133_, 3);
lean_dec_ref(v_inst_1127_);
v_toMonadExceptOf_1134_ = lean_ctor_get(v_inst_1128_, 0);
lean_inc_ref(v_toMonadExceptOf_1134_);
v___x_1135_ = ((lean_object*)(l_Lean_evalConst___redArg___closed__0));
v___x_1136_ = lean_box(v_checkMeta_1131_);
lean_inc(v_constName_1130_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1137_, 0, v_inst_1129_);
lean_closure_set(v___f_1137_, 1, v_constName_1130_);
lean_closure_set(v___f_1137_, 2, v___x_1136_);
lean_closure_set(v___f_1137_, 3, v_inst_1126_);
lean_closure_set(v___f_1137_, 4, v_inst_1128_);
lean_closure_set(v___f_1137_, 5, v___x_1135_);
lean_closure_set(v___f_1137_, 6, v_toBind_1132_);
lean_inc_ref(v___f_1137_);
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1138_, 0, v_toBind_1132_);
lean_closure_set(v___f_1138_, 1, v_getEnv_1133_);
lean_closure_set(v___f_1138_, 2, v___f_1137_);
v___x_1139_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_1134_);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1140_, 0, v_constName_1130_);
lean_closure_set(v___f_1140_, 1, v_toBind_1132_);
lean_closure_set(v___f_1140_, 2, v_getEnv_1133_);
lean_closure_set(v___f_1140_, 3, v___f_1137_);
lean_closure_set(v___f_1140_, 4, v___x_1139_);
lean_closure_set(v___f_1140_, 5, v___f_1138_);
v___x_1141_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v_getEnv_1133_, v___f_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT void l_Lean_evalConst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1126_ = stack[0].m_obj;
lean_object* v_inst_1127_ = stack[1].m_obj;
lean_object* v_inst_1128_ = stack[2].m_obj;
lean_object* v_inst_1129_ = stack[3].m_obj;
lean_object* v_constName_1130_ = stack[4].m_obj;
uint8_t v_checkMeta_1131_ = stack[5].m_num;
lean_object* v_res_1142_;
v_res_1142_ = l_Lean_evalConst___redArg(v_inst_1126_, v_inst_1127_, v_inst_1128_, v_inst_1129_, v_constName_1130_, v_checkMeta_1131_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___boxed(lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_constName_1147_, lean_object* v_checkMeta_1148_){
_start:
{
uint8_t v_checkMeta_boxed_1149_; lean_object* v_res_1150_; 
v_checkMeta_boxed_1149_ = lean_unbox(v_checkMeta_1148_);
v_res_1150_ = l_Lean_evalConst___redArg(v_inst_1143_, v_inst_1144_, v_inst_1145_, v_inst_1146_, v_constName_1147_, v_checkMeta_boxed_1149_);
return v_res_1150_;
}
}
lean_object* l_Lean_evalConst(lean_object* v_m_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_00_u03b1_1156_, lean_object* v_constName_1157_, uint8_t v_checkMeta_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_evalConst___redArg(v_inst_1152_, v_inst_1153_, v_inst_1154_, v_inst_1155_, v_constName_1157_, v_checkMeta_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT void l_Lean_evalConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1152_ = stack[1].m_obj;
lean_object* v_inst_1153_ = stack[2].m_obj;
lean_object* v_inst_1154_ = stack[3].m_obj;
lean_object* v_inst_1155_ = stack[4].m_obj;
lean_object* v_constName_1157_ = stack[6].m_obj;
uint8_t v_checkMeta_1158_ = stack[7].m_num;
lean_object* v_res_1160_;
v_res_1160_ = l_Lean_evalConst(lean_box(0), v_inst_1152_, v_inst_1153_, v_inst_1154_, v_inst_1155_, lean_box(0), v_constName_1157_, v_checkMeta_1158_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___boxed(lean_object* v_m_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_00_u03b1_1166_, lean_object* v_constName_1167_, lean_object* v_checkMeta_1168_){
_start:
{
uint8_t v_checkMeta_boxed_1169_; lean_object* v_res_1170_; 
v_checkMeta_boxed_1169_ = lean_unbox(v_checkMeta_1168_);
v_res_1170_ = l_Lean_evalConst(v_m_1161_, v_inst_1162_, v_inst_1163_, v_inst_1164_, v_inst_1165_, v_00_u03b1_1166_, v_constName_1167_, v_checkMeta_boxed_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0(lean_object* v_____do__lift_1171_, lean_object* v_typeName_1172_, lean_object* v_constName_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v___x_1176_, lean_object* v_____do__lift_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_1171_, v_____do__lift_1177_, v_typeName_1172_, v_constName_1173_);
v___x_1179_ = l_Lean_ofExcept___redArg(v_inst_1174_, v_inst_1175_, v___x_1176_, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0___boxed(lean_object* v_____do__lift_1180_, lean_object* v_typeName_1181_, lean_object* v_constName_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v___x_1185_, lean_object* v_____do__lift_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_evalConstCheck___redArg___lam__0(v_____do__lift_1180_, v_typeName_1181_, v_constName_1182_, v_inst_1183_, v_inst_1184_, v___x_1185_, v_____do__lift_1186_);
lean_dec_ref(v_____do__lift_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__1(lean_object* v_inst_1188_, lean_object* v_typeName_1189_, lean_object* v_constName_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v___x_1193_, lean_object* v_toBind_1194_, lean_object* v_____do__lift_1195_){
_start:
{
lean_object* v_getOptions_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_getOptions_1196_ = lean_ctor_get(v_inst_1188_, 0);
lean_inc(v_getOptions_1196_);
lean_dec_ref(v_inst_1188_);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1197_, 0, v_____do__lift_1195_);
lean_closure_set(v___f_1197_, 1, v_typeName_1189_);
lean_closure_set(v___f_1197_, 2, v_constName_1190_);
lean_closure_set(v___f_1197_, 3, v_inst_1191_);
lean_closure_set(v___f_1197_, 4, v_inst_1192_);
lean_closure_set(v___f_1197_, 5, v___x_1193_);
v___x_1198_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v_getOptions_1196_, v___f_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg(lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_typeName_1203_, lean_object* v_constName_1204_){
_start:
{
lean_object* v_toBind_1205_; lean_object* v_getEnv_1206_; lean_object* v_toMonadExceptOf_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; 
v_toBind_1205_ = lean_ctor_get(v_inst_1199_, 1);
lean_inc_n(v_toBind_1205_, 4);
v_getEnv_1206_ = lean_ctor_get(v_inst_1200_, 0);
lean_inc_n(v_getEnv_1206_, 3);
lean_dec_ref(v_inst_1200_);
v_toMonadExceptOf_1207_ = lean_ctor_get(v_inst_1201_, 0);
lean_inc_ref(v_toMonadExceptOf_1207_);
v___x_1208_ = ((lean_object*)(l_Lean_evalConst___redArg___closed__0));
lean_inc(v_constName_1204_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1209_, 0, v_inst_1202_);
lean_closure_set(v___f_1209_, 1, v_typeName_1203_);
lean_closure_set(v___f_1209_, 2, v_constName_1204_);
lean_closure_set(v___f_1209_, 3, v_inst_1199_);
lean_closure_set(v___f_1209_, 4, v_inst_1201_);
lean_closure_set(v___f_1209_, 5, v___x_1208_);
lean_closure_set(v___f_1209_, 6, v_toBind_1205_);
lean_inc_ref(v___f_1209_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1210_, 0, v_toBind_1205_);
lean_closure_set(v___f_1210_, 1, v_getEnv_1206_);
lean_closure_set(v___f_1210_, 2, v___f_1209_);
v___x_1211_ = l_instMonadExceptOfMonadExceptOf___redArg(v_toMonadExceptOf_1207_);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1212_, 0, v_constName_1204_);
lean_closure_set(v___f_1212_, 1, v_toBind_1205_);
lean_closure_set(v___f_1212_, 2, v_getEnv_1206_);
lean_closure_set(v___f_1212_, 3, v___f_1209_);
lean_closure_set(v___f_1212_, 4, v___x_1211_);
lean_closure_set(v___f_1212_, 5, v___f_1210_);
v___x_1213_ = lean_apply_4(v_toBind_1205_, lean_box(0), lean_box(0), v_getEnv_1206_, v___f_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object* v_m_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_00_u03b1_1219_, lean_object* v_typeName_1220_, lean_object* v_constName_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_evalConstCheck___redArg(v_inst_1215_, v_inst_1216_, v_inst_1217_, v_inst_1218_, v_typeName_1220_, v_constName_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0(lean_object* v___x_1223_, lean_object* v_val_1224_, lean_object* v_toPure_1225_, lean_object* v_____do__lift_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = l_Lean_Environment_allImportedModuleNames(v_____do__lift_1226_);
v___x_1228_ = lean_array_get(v___x_1223_, v___x_1227_, v_val_1224_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
v___x_1230_ = lean_apply_2(v_toPure_1225_, lean_box(0), v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(lean_object* v___x_1231_, lean_object* v_val_1232_, lean_object* v_toPure_1233_, lean_object* v_____do__lift_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_findModuleOf_x3f___redArg___lam__0(v___x_1231_, v_val_1232_, v_toPure_1233_, v_____do__lift_1234_);
lean_dec_ref(v_____do__lift_1234_);
lean_dec(v_val_1232_);
lean_dec(v___x_1231_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1(lean_object* v_declName_1236_, lean_object* v_toPure_1237_, lean_object* v___x_1238_, lean_object* v_toBind_1239_, lean_object* v_getEnv_1240_, lean_object* v_____do__lift_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1241_, v_declName_1236_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_getEnv_1240_);
lean_dec(v_toBind_1239_);
lean_dec(v___x_1238_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_apply_2(v_toPure_1237_, lean_box(0), v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v_val_1245_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1242_, 1);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1246_, 0, v___x_1238_);
lean_closure_set(v___f_1246_, 1, v_val_1245_);
lean_closure_set(v___f_1246_, 2, v_toPure_1237_);
v___x_1247_ = lean_apply_4(v_toBind_1239_, lean_box(0), lean_box(0), v_getEnv_1240_, v___f_1246_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(lean_object* v_declName_1248_, lean_object* v_toPure_1249_, lean_object* v___x_1250_, lean_object* v_toBind_1251_, lean_object* v_getEnv_1252_, lean_object* v_____do__lift_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_findModuleOf_x3f___redArg___lam__1(v_declName_1248_, v_toPure_1249_, v___x_1250_, v_toBind_1251_, v_getEnv_1252_, v_____do__lift_1253_);
lean_dec_ref(v_____do__lift_1253_);
lean_dec(v_declName_1248_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__2(lean_object* v_inst_1255_, lean_object* v_declName_1256_, lean_object* v_toPure_1257_, lean_object* v___x_1258_, lean_object* v_toBind_1259_, lean_object* v_____r_1260_){
_start:
{
lean_object* v_getEnv_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; 
v_getEnv_1261_ = lean_ctor_get(v_inst_1255_, 0);
lean_inc_n(v_getEnv_1261_, 2);
lean_dec_ref(v_inst_1255_);
lean_inc(v_toBind_1259_);
v___f_1262_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1262_, 0, v_declName_1256_);
lean_closure_set(v___f_1262_, 1, v_toPure_1257_);
lean_closure_set(v___f_1262_, 2, v___x_1258_);
lean_closure_set(v___f_1262_, 3, v_toBind_1259_);
lean_closure_set(v___f_1262_, 4, v_getEnv_1261_);
v___x_1263_ = lean_apply_4(v_toBind_1259_, lean_box(0), lean_box(0), v_getEnv_1261_, v___f_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg(lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_declName_1267_){
_start:
{
lean_object* v_toApplicative_1268_; lean_object* v_toFunctor_1269_; lean_object* v_toBind_1270_; lean_object* v_toPure_1271_; lean_object* v_mapConst_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_toApplicative_1268_ = lean_ctor_get(v_inst_1264_, 0);
v_toFunctor_1269_ = lean_ctor_get(v_toApplicative_1268_, 0);
v_toBind_1270_ = lean_ctor_get(v_inst_1264_, 1);
lean_inc_n(v_toBind_1270_, 2);
v_toPure_1271_ = lean_ctor_get(v_toApplicative_1268_, 1);
v_mapConst_1272_ = lean_ctor_get(v_toFunctor_1269_, 1);
lean_inc(v_mapConst_1272_);
v___x_1273_ = lean_box(0);
lean_inc(v_toPure_1271_);
lean_inc(v_declName_1267_);
lean_inc_ref(v_inst_1265_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1274_, 0, v_inst_1265_);
lean_closure_set(v___f_1274_, 1, v_declName_1267_);
lean_closure_set(v___f_1274_, 2, v_toPure_1271_);
lean_closure_set(v___f_1274_, 3, v___x_1273_);
lean_closure_set(v___f_1274_, 4, v_toBind_1270_);
v___x_1275_ = l_Lean_getConstInfo___redArg(v_inst_1264_, v_inst_1265_, v_inst_1266_, v_declName_1267_);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_apply_4(v_mapConst_1272_, lean_box(0), lean_box(0), v___x_1276_, v___x_1275_);
v___x_1278_ = lean_apply_4(v_toBind_1270_, lean_box(0), lean_box(0), v___x_1277_, v___f_1274_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object* v_m_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_declName_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_findModuleOf_x3f___redArg(v_inst_1280_, v_inst_1281_, v_inst_1282_, v_declName_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg___lam__0(lean_object* v_val_1285_, lean_object* v_toPure_1286_, lean_object* v_recInfo_1287_){
_start:
{
lean_object* v_toConstantVal_1288_; lean_object* v_levelParams_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_toConstantVal_1288_ = lean_ctor_get(v_val_1285_, 0);
v_levelParams_1289_ = lean_ctor_get(v_toConstantVal_1288_, 1);
v___x_1290_ = l_List_lengthTR___redArg(v_levelParams_1289_);
v___x_1291_ = l_Lean_ConstantInfo_levelParams(v_recInfo_1287_);
v___x_1292_ = l_List_lengthTR___redArg(v___x_1291_);
lean_dec(v___x_1291_);
v___x_1293_ = lean_nat_dec_lt(v___x_1290_, v___x_1292_);
lean_dec(v___x_1292_);
lean_dec(v___x_1290_);
v___x_1294_ = lean_box(v___x_1293_);
v___x_1295_ = lean_apply_2(v_toPure_1286_, lean_box(0), v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg___lam__0___boxed(lean_object* v_val_1296_, lean_object* v_toPure_1297_, lean_object* v_recInfo_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_isLargeEliminating___redArg___lam__0(v_val_1296_, v_toPure_1297_, v_recInfo_1298_);
lean_dec_ref(v_recInfo_1298_);
lean_dec_ref(v_val_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg___lam__1(lean_object* v_toPure_1300_, lean_object* v_declName_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_toBind_1305_, lean_object* v_____x_1306_){
_start:
{
if (lean_obj_tag(v_____x_1306_) == 5)
{
lean_object* v_val_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_val_1307_ = lean_ctor_get(v_____x_1306_, 0);
lean_inc_ref(v_val_1307_);
lean_dec_ref_known(v_____x_1306_, 1);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_isLargeEliminating___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1308_, 0, v_val_1307_);
lean_closure_set(v___f_1308_, 1, v_toPure_1300_);
v___x_1309_ = l_Lean_mkRecName(v_declName_1301_);
v___x_1310_ = l_Lean_getConstInfo___redArg(v_inst_1302_, v_inst_1303_, v_inst_1304_, v___x_1309_);
v___x_1311_ = lean_apply_4(v_toBind_1305_, lean_box(0), lean_box(0), v___x_1310_, v___f_1308_);
return v___x_1311_;
}
else
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref(v_____x_1306_);
lean_dec(v_toBind_1305_);
lean_dec_ref(v_inst_1304_);
lean_dec_ref(v_inst_1303_);
lean_dec_ref(v_inst_1302_);
lean_dec(v_declName_1301_);
v___x_1312_ = 0;
v___x_1313_ = lean_box(v___x_1312_);
v___x_1314_ = lean_apply_2(v_toPure_1300_, lean_box(0), v___x_1313_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___redArg(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_declName_1318_){
_start:
{
lean_object* v_toApplicative_1319_; lean_object* v_toBind_1320_; lean_object* v_toPure_1321_; lean_object* v___x_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; 
v_toApplicative_1319_ = lean_ctor_get(v_inst_1315_, 0);
v_toBind_1320_ = lean_ctor_get(v_inst_1315_, 1);
lean_inc_n(v_toBind_1320_, 2);
v_toPure_1321_ = lean_ctor_get(v_toApplicative_1319_, 1);
lean_inc(v_toPure_1321_);
lean_inc(v_declName_1318_);
lean_inc_ref(v_inst_1317_);
lean_inc_ref(v_inst_1316_);
lean_inc_ref(v_inst_1315_);
v___x_1322_ = l_Lean_getConstInfo___redArg(v_inst_1315_, v_inst_1316_, v_inst_1317_, v_declName_1318_);
v___f_1323_ = lean_alloc_closure((void*)(l_Lean_isLargeEliminating___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1323_, 0, v_toPure_1321_);
lean_closure_set(v___f_1323_, 1, v_declName_1318_);
lean_closure_set(v___f_1323_, 2, v_inst_1315_);
lean_closure_set(v___f_1323_, 3, v_inst_1316_);
lean_closure_set(v___f_1323_, 4, v_inst_1317_);
lean_closure_set(v___f_1323_, 5, v_toBind_1320_);
v___x_1324_ = lean_apply_4(v_toBind_1320_, lean_box(0), lean_box(0), v___x_1322_, v___f_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating(lean_object* v_m_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_declName_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_isLargeEliminating___redArg(v_inst_1326_, v_inst_1327_, v_inst_1328_, v_declName_1329_);
return v___x_1330_;
}
}
lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object* v___x_1331_, lean_object* v_toPure_1332_, uint8_t v_isUnsafe_1333_, lean_object* v_____x_1334_){
_start:
{
if (lean_obj_tag(v_____x_1334_) == 6)
{
lean_object* v_val_1335_; lean_object* v_numFields_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_val_1335_ = lean_ctor_get(v_____x_1334_, 0);
v_numFields_1336_ = lean_ctor_get(v_val_1335_, 4);
v___x_1337_ = lean_nat_dec_eq(v_numFields_1336_, v___x_1331_);
v___x_1338_ = lean_box(v___x_1337_);
v___x_1339_ = lean_apply_2(v_toPure_1332_, lean_box(0), v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_box(v_isUnsafe_1333_);
v___x_1341_ = lean_apply_2(v_toPure_1332_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
}
}
LEAN_EXPORT void l_Lean_isEnumType___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1331_ = stack[0].m_obj;
lean_object* v_toPure_1332_ = stack[1].m_obj;
uint8_t v_isUnsafe_1333_ = stack[2].m_num;
lean_object* v_____x_1334_ = stack[3].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_isEnumType___redArg___lam__0(v___x_1331_, v_toPure_1332_, v_isUnsafe_1333_, v_____x_1334_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object* v___x_1343_, lean_object* v_toPure_1344_, lean_object* v_isUnsafe_1345_, lean_object* v_____x_1346_){
_start:
{
uint8_t v_isUnsafe_boxed_1347_; lean_object* v_res_1348_; 
v_isUnsafe_boxed_1347_ = lean_unbox(v_isUnsafe_1345_);
v_res_1348_ = l_Lean_isEnumType___redArg___lam__0(v___x_1343_, v_toPure_1344_, v_isUnsafe_boxed_1347_, v_____x_1346_);
lean_dec_ref(v_____x_1346_);
lean_dec(v___x_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_toBind_1352_, lean_object* v___f_1353_, lean_object* v_ctorName_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = l_Lean_getConstInfo___redArg(v_inst_1349_, v_inst_1350_, v_inst_1351_, v_ctorName_1354_);
v___x_1356_ = lean_apply_4(v_toBind_1352_, lean_box(0), lean_box(0), v___x_1355_, v___f_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object* v_toPure_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_toBind_1361_, lean_object* v_____do__lift_1362_){
_start:
{
if (lean_obj_tag(v_____do__lift_1362_) == 5)
{
lean_object* v_val_1363_; lean_object* v_toConstantVal_1364_; lean_object* v_numParams_1365_; lean_object* v_numIndices_1366_; lean_object* v_ctors_1367_; uint8_t v_isRec_1368_; uint8_t v_isUnsafe_1369_; lean_object* v_type_1370_; uint8_t v___x_1371_; 
v_val_1363_ = lean_ctor_get(v_____do__lift_1362_, 0);
lean_inc_ref(v_val_1363_);
lean_dec_ref_known(v_____do__lift_1362_, 1);
v_toConstantVal_1364_ = lean_ctor_get(v_val_1363_, 0);
v_numParams_1365_ = lean_ctor_get(v_val_1363_, 1);
lean_inc(v_numParams_1365_);
v_numIndices_1366_ = lean_ctor_get(v_val_1363_, 2);
lean_inc(v_numIndices_1366_);
v_ctors_1367_ = lean_ctor_get(v_val_1363_, 4);
lean_inc(v_ctors_1367_);
v_isRec_1368_ = lean_ctor_get_uint8(v_val_1363_, sizeof(void*)*6);
v_isUnsafe_1369_ = lean_ctor_get_uint8(v_val_1363_, sizeof(void*)*6 + 1);
v_type_1370_ = lean_ctor_get(v_toConstantVal_1364_, 2);
v___x_1371_ = l_Lean_Expr_isProp(v_type_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = l_Lean_InductiveVal_numTypeFormers(v_val_1363_);
lean_dec_ref(v_val_1363_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_dec_eq(v___x_1372_, v___x_1373_);
lean_dec(v___x_1372_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_ctors_1367_);
lean_dec(v_numIndices_1366_);
lean_dec(v_numParams_1365_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1375_ = lean_box(v___x_1374_);
v___x_1376_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_nat_dec_eq(v_numIndices_1366_, v___x_1377_);
lean_dec(v_numIndices_1366_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_ctors_1367_);
lean_dec(v_numParams_1365_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1379_ = lean_box(v___x_1378_);
v___x_1380_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1379_);
return v___x_1380_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_eq(v_numParams_1365_, v___x_1377_);
lean_dec(v_numParams_1365_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v_ctors_1367_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1382_ = lean_box(v___x_1381_);
v___x_1383_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1382_);
return v___x_1383_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = l_List_isEmpty___redArg(v_ctors_1367_);
if (v___x_1384_ == 0)
{
if (v_isRec_1368_ == 0)
{
if (v_isUnsafe_1369_ == 0)
{
lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; 
v___x_1385_ = lean_box(v_isUnsafe_1369_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1386_, 0, v___x_1377_);
lean_closure_set(v___f_1386_, 1, v_toPure_1357_);
lean_closure_set(v___f_1386_, 2, v___x_1385_);
lean_inc_ref(v_inst_1358_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1387_, 0, v_inst_1358_);
lean_closure_set(v___f_1387_, 1, v_inst_1359_);
lean_closure_set(v___f_1387_, 2, v_inst_1360_);
lean_closure_set(v___f_1387_, 3, v_toBind_1361_);
lean_closure_set(v___f_1387_, 4, v___f_1386_);
v___x_1388_ = l_List_allM___redArg(v_inst_1358_, v___f_1387_, v_ctors_1367_);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_ctors_1367_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1389_ = lean_box(v_isRec_1368_);
v___x_1390_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1389_);
return v___x_1390_;
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec(v_ctors_1367_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1391_ = lean_box(v___x_1384_);
v___x_1392_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1391_);
return v___x_1392_;
}
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec(v_ctors_1367_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1393_ = lean_box(v___x_1371_);
v___x_1394_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1393_);
return v___x_1394_;
}
}
}
}
}
else
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v_ctors_1367_);
lean_dec(v_numIndices_1366_);
lean_dec(v_numParams_1365_);
lean_dec_ref(v_val_1363_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1395_ = 0;
v___x_1396_ = lean_box(v___x_1395_);
v___x_1397_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1396_);
return v___x_1397_;
}
}
else
{
uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v_____do__lift_1362_);
lean_dec(v_toBind_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_dec_ref(v_inst_1358_);
v___x_1398_ = 0;
v___x_1399_ = lean_box(v___x_1398_);
v___x_1400_ = lean_apply_2(v_toPure_1357_, lean_box(0), v___x_1399_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg(lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_declName_1404_){
_start:
{
lean_object* v_toApplicative_1405_; lean_object* v_toBind_1406_; lean_object* v_toPure_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1401_, 0);
v_toBind_1406_ = lean_ctor_get(v_inst_1401_, 1);
lean_inc_n(v_toBind_1406_, 2);
v_toPure_1407_ = lean_ctor_get(v_toApplicative_1405_, 1);
lean_inc(v_toPure_1407_);
lean_inc_ref(v_inst_1403_);
lean_inc_ref(v_inst_1402_);
lean_inc_ref(v_inst_1401_);
v___x_1408_ = l_Lean_getConstInfo___redArg(v_inst_1401_, v_inst_1402_, v_inst_1403_, v_declName_1404_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1409_, 0, v_toPure_1407_);
lean_closure_set(v___f_1409_, 1, v_inst_1401_);
lean_closure_set(v___f_1409_, 2, v_inst_1402_);
lean_closure_set(v___f_1409_, 3, v_inst_1403_);
lean_closure_set(v___f_1409_, 4, v_toBind_1406_);
v___x_1410_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1408_, v___f_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object* v_m_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_declName_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_isEnumType___redArg(v_inst_1412_, v_inst_1413_, v_inst_1414_, v_declName_1415_);
return v___x_1416_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
lean_object* runtime_initialize_Lean_AuxRecursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Old(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
