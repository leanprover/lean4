// Lean compiler output
// Module: Lean.Compiler.LCNF.ResetReuse
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.LiveVars import Lean.Compiler.LCNF.DependsOn import Lean.Compiler.LCNF.PhaseExt
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateContImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.S.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Compiler.LCNF.ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4;
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instSingletonFVarIdFVarIdSet;
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.D.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1;
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Code.insertResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Decl.insertResetReuseCore.collectResets"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___closed__0;
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "resetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 201, 93, 114, 179, 16, 247, 72)}};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_insertResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 22, 75, 214, 119, 69, 48, 225)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 165, 194, 12, 198, 157, 117, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(105, 150, 117, 254, 63, 70, 178, 234)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 242, 201, 181, 138, 172, 149, 255)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 154, 112, 50, 132, 225, 68, 23)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 182, 243, 139, 183, 248, 56, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 130, 185, 126, 60, 87, 109, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 224, 225, 246, 174, 48, 45, 78)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 47, 104, 191, 68, 113, 248, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 193, 129, 108, 61, 130, 124, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 251, 249, 254, 208, 86, 150, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 85, 80, 162, 8, 82, 178, 101)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_28 = lean_nat_dec_eq(x_6, x_10);
if (x_28 == 0)
{
x_13 = x_28;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_7, x_11);
x_13 = x_29;
goto block_27;
}
block_27:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_8, x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_Name_getPrefix(x_5);
x_21 = l_Lean_Name_getPrefix(x_9);
x_22 = lean_name_eq(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_19);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(x_1, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_47; 
x_8 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_9, 1);
lean_dec(x_48);
x_11 = x_9;
x_12 = x_47;
goto block_46;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_44; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_10, 1);
lean_dec(x_45);
x_17 = x_10;
x_18 = x_44;
goto block_43;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_15);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_14);
if (x_18 == 0)
{
lean_ctor_set(x_17, 4, x_24);
lean_ctor_set(x_17, 3, x_25);
lean_ctor_set(x_17, 2, x_26);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_23);
x_27 = x_17;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_25);
lean_ctor_set(x_42, 4, x_24);
x_27 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_28; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_27);
x_28 = x_11;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_20);
x_28 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_instInhabitedOfMonad___redArg(x_29, x_33);
x_35 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_panic_fn(x_36, x_1);
x_38 = lean_apply_6(x_37, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = lean_unbox(x_5);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(627u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(123u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_235, 3);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 5)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_303; 
x_237 = lean_ctor_get(x_3, 1);
x_238 = lean_ctor_get(x_235, 0);
x_239 = lean_ctor_get(x_235, 1);
x_240 = lean_ctor_get(x_235, 2);
x_303 = !lean_is_exclusive(x_235);
if (x_303 == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_235, 3);
lean_dec(x_304);
x_241 = x_235;
x_242 = x_303;
goto block_302;
}
else
{
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_235);
x_241 = lean_box(0);
x_242 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_301; 
x_243 = lean_ctor_get(x_236, 0);
x_244 = lean_ctor_get(x_236, 1);
x_301 = !lean_is_exclusive(x_236);
if (x_301 == 0)
{
x_245 = x_236;
x_246 = x_301;
goto block_300;
}
else
{
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_236);
x_245 = lean_box(0);
x_246 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_247; 
x_247 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(x_1, x_243, x_4);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
x_249 = lean_unbox(x_248);
if (x_249 == 0)
{
lean_dec(x_248);
lean_del_object(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_del_object(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_inc_ref(x_237);
x_16 = x_237;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_234;
}
else
{
lean_object* x_250; uint8_t x_251; uint8_t x_289; 
lean_inc_ref(x_237);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_289 = !lean_is_exclusive(x_3);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_3, 1);
lean_dec(x_290);
x_291 = lean_ctor_get(x_3, 0);
lean_dec(x_291);
x_250 = x_3;
x_251 = x_289;
goto block_288;
}
else
{
lean_dec(x_3);
x_250 = lean_box(0);
x_251 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_1, 1);
x_253 = lean_ctor_get(x_243, 1);
x_254 = 1;
lean_inc_ref(x_244);
lean_inc_ref(x_243);
if (x_246 == 0)
{
x_255 = x_245;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_287, 0, x_243);
lean_ctor_set(x_287, 1, x_244);
x_255 = x_287;
goto block_286;
}
block_286:
{
lean_object* x_256; 
lean_inc_ref(x_240);
if (x_242 == 0)
{
lean_ctor_set(x_241, 3, x_255);
x_256 = x_241;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_285, 0, x_238);
lean_ctor_set(x_285, 1, x_239);
lean_ctor_set(x_285, 2, x_240);
lean_ctor_set(x_285, 3, x_255);
x_256 = x_285;
goto block_284;
}
block_284:
{
uint8_t x_257; uint8_t x_281; 
x_281 = lean_nat_dec_eq(x_252, x_253);
if (x_281 == 0)
{
uint8_t x_282; 
x_282 = lean_unbox(x_248);
x_257 = x_282;
goto block_280;
}
else
{
uint8_t x_283; 
x_283 = 0;
x_257 = x_283;
goto block_280;
}
block_280:
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_258, 0, x_2);
lean_ctor_set(x_258, 1, x_243);
lean_ctor_set(x_258, 2, x_244);
lean_ctor_set_uint8(x_258, sizeof(void*)*3, x_257);
x_259 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_254, x_256, x_240, x_258, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_271; 
x_260 = lean_ctor_get(x_259, 0);
x_271 = !lean_is_exclusive(x_259);
if (x_271 == 0)
{
x_261 = x_259;
x_262 = x_271;
goto block_270;
}
else
{
lean_inc(x_260);
lean_dec(x_259);
x_261 = lean_box(0);
x_262 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_263; 
if (x_251 == 0)
{
lean_ctor_set(x_250, 0, x_260);
x_263 = x_250;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_260);
lean_ctor_set(x_269, 1, x_237);
x_263 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_248);
if (x_262 == 0)
{
lean_ctor_set(x_261, 0, x_264);
x_265 = x_261;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_279; 
lean_del_object(x_250);
lean_dec(x_248);
lean_dec_ref(x_237);
x_272 = lean_ctor_get(x_259, 0);
x_279 = !lean_is_exclusive(x_259);
if (x_279 == 0)
{
x_273 = x_259;
x_274 = x_279;
goto block_278;
}
else
{
lean_inc(x_272);
lean_dec(x_259);
x_273 = lean_box(0);
x_274 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_275; 
if (x_274 == 0)
{
x_275 = x_273;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_272);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
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
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_299; 
lean_del_object(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_del_object(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_292 = lean_ctor_get(x_247, 0);
x_299 = !lean_is_exclusive(x_247);
if (x_299 == 0)
{
x_293 = x_247;
x_294 = x_299;
goto block_298;
}
else
{
lean_inc(x_292);
lean_dec(x_247);
x_293 = lean_box(0);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_294 == 0)
{
x_295 = x_293;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_292);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
}
}
else
{
lean_object* x_305; 
lean_dec(x_236);
lean_dec_ref(x_235);
x_305 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_305);
x_16 = x_305;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_234;
}
}
case 2:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_ctor_get(x_3, 0);
x_307 = lean_ctor_get(x_3, 1);
x_308 = lean_ctor_get(x_306, 2);
x_309 = lean_ctor_get(x_306, 3);
x_310 = lean_ctor_get(x_306, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_310);
lean_inc(x_2);
x_311 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(x_1, x_2, x_310, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
x_314 = lean_unbox(x_313);
if (x_314 == 0)
{
lean_dec(x_313);
lean_dec(x_312);
lean_inc_ref(x_307);
x_16 = x_307;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_234;
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; uint8_t x_358; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_315 = lean_ctor_get(x_312, 0);
x_358 = !lean_is_exclusive(x_312);
if (x_358 == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_312, 1);
lean_dec(x_359);
x_316 = x_312;
x_317 = x_358;
goto block_357;
}
else
{
lean_inc(x_315);
lean_dec(x_312);
x_316 = lean_box(0);
x_317 = x_358;
goto block_357;
}
block_357:
{
uint8_t x_318; lean_object* x_319; 
x_318 = 1;
lean_inc_ref(x_308);
lean_inc_ref(x_309);
lean_inc_ref(x_306);
x_319 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_318, x_306, x_309, x_308, x_315, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_348; 
x_320 = lean_ctor_get(x_319, 0);
x_348 = !lean_is_exclusive(x_319);
if (x_348 == 0)
{
x_321 = x_319;
x_322 = x_348;
goto block_347;
}
else
{
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_box(0);
x_322 = x_348;
goto block_347;
}
block_347:
{
lean_object* x_323; uint8_t x_331; size_t x_342; uint8_t x_343; 
x_342 = lean_ptr_addr(x_307);
x_343 = lean_usize_dec_eq(x_342, x_342);
if (x_343 == 0)
{
x_331 = x_343;
goto block_341;
}
else
{
size_t x_344; size_t x_345; uint8_t x_346; 
x_344 = lean_ptr_addr(x_306);
x_345 = lean_ptr_addr(x_320);
x_346 = lean_usize_dec_eq(x_344, x_345);
x_331 = x_346;
goto block_341;
}
block_330:
{
lean_object* x_324; 
if (x_317 == 0)
{
lean_ctor_set(x_316, 0, x_323);
x_324 = x_316;
goto block_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_323);
lean_ctor_set(x_329, 1, x_313);
x_324 = x_329;
goto block_328;
}
block_328:
{
lean_object* x_325; 
if (x_322 == 0)
{
lean_ctor_set(x_321, 0, x_324);
x_325 = x_321;
goto block_326;
}
else
{
lean_object* x_327; 
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_324);
x_325 = x_327;
goto block_326;
}
block_326:
{
return x_325;
}
}
}
block_341:
{
if (x_331 == 0)
{
lean_object* x_332; uint8_t x_333; uint8_t x_338; 
lean_inc_ref(x_307);
x_338 = !lean_is_exclusive(x_3);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_3, 1);
lean_dec(x_339);
x_340 = lean_ctor_get(x_3, 0);
lean_dec(x_340);
x_332 = x_3;
x_333 = x_338;
goto block_337;
}
else
{
lean_dec(x_3);
x_332 = lean_box(0);
x_333 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_334; 
if (x_333 == 0)
{
lean_ctor_set(x_332, 0, x_320);
x_334 = x_332;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_320);
lean_ctor_set(x_336, 1, x_307);
x_334 = x_336;
goto block_335;
}
block_335:
{
x_323 = x_334;
goto block_330;
}
}
}
else
{
lean_dec(x_320);
x_323 = x_3;
goto block_330;
}
}
}
}
else
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; uint8_t x_356; 
lean_del_object(x_316);
lean_dec(x_313);
lean_dec_ref(x_3);
x_349 = lean_ctor_get(x_319, 0);
x_356 = !lean_is_exclusive(x_319);
if (x_356 == 0)
{
x_350 = x_319;
x_351 = x_356;
goto block_355;
}
else
{
lean_inc(x_349);
lean_dec(x_319);
x_350 = lean_box(0);
x_351 = x_356;
goto block_355;
}
block_355:
{
lean_object* x_352; 
if (x_351 == 0)
{
x_352 = x_350;
goto block_353;
}
else
{
lean_object* x_354; 
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_349);
x_352 = x_354;
goto block_353;
}
block_353:
{
return x_352;
}
}
}
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_311;
}
}
case 3:
{
uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_360 = 0;
x_361 = lean_box(x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_3);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_363, 0, x_362);
return x_363;
}
case 4:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_420; 
x_364 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_364);
x_365 = lean_ctor_get(x_364, 0);
x_366 = lean_ctor_get(x_364, 1);
x_367 = lean_ctor_get(x_364, 2);
x_368 = lean_ctor_get(x_364, 3);
x_420 = !lean_is_exclusive(x_364);
if (x_420 == 0)
{
x_369 = x_364;
x_370 = x_420;
goto block_419;
}
else
{
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_364);
x_369 = lean_box(0);
x_370 = x_420;
goto block_419;
}
block_419:
{
size_t x_371; size_t x_372; lean_object* x_373; 
x_371 = lean_array_size(x_368);
x_372 = 0;
lean_inc_ref(x_368);
x_373 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(x_1, x_2, x_371, x_372, x_368, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_410; 
x_374 = lean_ctor_get(x_373, 0);
x_410 = !lean_is_exclusive(x_373);
if (x_410 == 0)
{
x_375 = x_373;
x_376 = x_410;
goto block_409;
}
else
{
lean_inc(x_374);
lean_dec(x_373);
x_375 = lean_box(0);
x_376 = x_410;
goto block_409;
}
block_409:
{
lean_object* x_377; uint8_t x_378; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; size_t x_395; size_t x_396; uint8_t x_397; 
x_385 = l_Array_unzip___redArg(x_374);
lean_dec(x_374);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec_ref(x_385);
x_395 = lean_ptr_addr(x_368);
lean_dec_ref(x_368);
x_396 = lean_ptr_addr(x_386);
x_397 = lean_usize_dec_eq(x_395, x_396);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; uint8_t x_407; 
x_407 = !lean_is_exclusive(x_3);
if (x_407 == 0)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_3, 0);
lean_dec(x_408);
x_398 = x_3;
x_399 = x_407;
goto block_406;
}
else
{
lean_dec(x_3);
x_398 = lean_box(0);
x_399 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_400; 
if (x_370 == 0)
{
lean_ctor_set(x_369, 3, x_386);
x_400 = x_369;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_405, 0, x_365);
lean_ctor_set(x_405, 1, x_366);
lean_ctor_set(x_405, 2, x_367);
lean_ctor_set(x_405, 3, x_386);
x_400 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_401; 
if (x_399 == 0)
{
lean_ctor_set(x_398, 0, x_400);
x_401 = x_398;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_403, 0, x_400);
x_401 = x_403;
goto block_402;
}
block_402:
{
x_388 = x_401;
goto block_394;
}
}
}
}
else
{
lean_dec(x_386);
lean_del_object(x_369);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
x_388 = x_3;
goto block_394;
}
block_384:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_box(x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_379);
if (x_376 == 0)
{
lean_ctor_set(x_375, 0, x_380);
x_381 = x_375;
goto block_382;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_383, 0, x_380);
x_381 = x_383;
goto block_382;
}
block_382:
{
return x_381;
}
}
block_394:
{
lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_389 = lean_unsigned_to_nat(0u);
x_390 = lean_array_get_size(x_387);
x_391 = lean_nat_dec_lt(x_389, x_390);
if (x_391 == 0)
{
lean_dec(x_387);
x_377 = x_388;
x_378 = x_391;
goto block_384;
}
else
{
if (x_391 == 0)
{
lean_dec(x_387);
x_377 = x_388;
x_378 = x_391;
goto block_384;
}
else
{
size_t x_392; uint8_t x_393; 
x_392 = lean_usize_of_nat(x_390);
x_393 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(x_387, x_372, x_392);
lean_dec(x_387);
x_377 = x_388;
x_378 = x_393;
goto block_384;
}
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_418; 
lean_del_object(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_3);
x_411 = lean_ctor_get(x_373, 0);
x_418 = !lean_is_exclusive(x_373);
if (x_418 == 0)
{
x_412 = x_373;
x_413 = x_418;
goto block_417;
}
else
{
lean_inc(x_411);
lean_dec(x_373);
x_412 = lean_box(0);
x_413 = x_418;
goto block_417;
}
block_417:
{
lean_object* x_414; 
if (x_413 == 0)
{
x_414 = x_412;
goto block_415;
}
else
{
lean_object* x_416; 
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_411);
x_414 = x_416;
goto block_415;
}
block_415:
{
return x_414;
}
}
}
}
}
case 5:
{
uint8_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_421 = 0;
x_422 = lean_box(x_421);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_3);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_424, 0, x_423);
return x_424;
}
case 6:
{
uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_425 = 0;
x_426 = lean_box(x_425);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_3);
lean_ctor_set(x_427, 1, x_426);
x_428 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_428, 0, x_427);
return x_428;
}
case 8:
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_429);
x_16 = x_429;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_234;
}
case 9:
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_430);
x_16 = x_430;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_234;
}
default: 
{
lean_object* x_431; lean_object* x_432; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_431 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
x_432 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(x_431, x_4, x_5, x_6, x_7, x_8);
return x_432;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_234:
{
lean_object* x_22; 
x_22 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(x_1, x_2, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ptr_addr(x_27);
x_29 = lean_ptr_addr(x_24);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_38; 
lean_inc_ref(x_26);
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_3, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_3, 0);
lean_dec(x_40);
x_31 = x_3;
x_32 = x_38;
goto block_37;
}
else
{
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_33; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_24);
x_33 = x_31;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_24);
x_33 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_34; 
x_34 = lean_unbox(x_25);
lean_dec(x_25);
x_10 = x_34;
x_11 = x_33;
goto block_15;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_24);
x_41 = lean_unbox(x_25);
lean_dec(x_25);
x_10 = x_41;
x_11 = x_3;
goto block_15;
}
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ptr_addr(x_45);
x_47 = lean_ptr_addr(x_42);
x_48 = lean_usize_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_56; 
lean_inc_ref(x_44);
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_3, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 0);
lean_dec(x_58);
x_49 = x_3;
x_50 = x_56;
goto block_55;
}
else
{
lean_dec(x_3);
x_49 = lean_box(0);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 1, x_42);
x_51 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_42);
x_51 = x_54;
goto block_53;
}
block_53:
{
uint8_t x_52; 
x_52 = lean_unbox(x_43);
lean_dec(x_43);
x_10 = x_52;
x_11 = x_51;
goto block_15;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_42);
x_59 = lean_unbox(x_43);
lean_dec(x_43);
x_10 = x_59;
x_11 = x_3;
goto block_15;
}
}
case 2:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_23, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_23, 1);
lean_inc(x_61);
lean_dec(x_23);
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ptr_addr(x_63);
x_65 = lean_ptr_addr(x_60);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; uint8_t x_74; 
lean_inc_ref(x_62);
x_74 = !lean_is_exclusive(x_3);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_3, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_3, 0);
lean_dec(x_76);
x_67 = x_3;
x_68 = x_74;
goto block_73;
}
else
{
lean_dec(x_3);
x_67 = lean_box(0);
x_68 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_69; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_60);
x_69 = x_67;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_60);
x_69 = x_72;
goto block_71;
}
block_71:
{
uint8_t x_70; 
x_70 = lean_unbox(x_61);
lean_dec(x_61);
x_10 = x_70;
x_11 = x_69;
goto block_15;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_60);
x_77 = lean_unbox(x_61);
lean_dec(x_61);
x_10 = x_77;
x_11 = x_3;
goto block_15;
}
}
case 7:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_23, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_23, 1);
lean_inc(x_79);
lean_dec(x_23);
x_80 = lean_ctor_get(x_3, 0);
x_81 = lean_ctor_get(x_3, 1);
x_82 = lean_ctor_get(x_3, 2);
x_83 = lean_ctor_get(x_3, 3);
x_84 = lean_ptr_addr(x_83);
x_85 = lean_ptr_addr(x_78);
x_86 = lean_usize_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; uint8_t x_94; 
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_94 = !lean_is_exclusive(x_3);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_3, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_3, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_3, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_3, 0);
lean_dec(x_98);
x_87 = x_3;
x_88 = x_94;
goto block_93;
}
else
{
lean_dec(x_3);
x_87 = lean_box(0);
x_88 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_89; 
if (x_88 == 0)
{
lean_ctor_set(x_87, 3, x_78);
x_89 = x_87;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_81);
lean_ctor_set(x_92, 2, x_82);
lean_ctor_set(x_92, 3, x_78);
x_89 = x_92;
goto block_91;
}
block_91:
{
uint8_t x_90; 
x_90 = lean_unbox(x_79);
lean_dec(x_79);
x_10 = x_90;
x_11 = x_89;
goto block_15;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_78);
x_99 = lean_unbox(x_79);
lean_dec(x_79);
x_10 = x_99;
x_11 = x_3;
goto block_15;
}
}
case 9:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; uint8_t x_110; 
x_100 = lean_ctor_get(x_23, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_23, 1);
lean_inc(x_101);
lean_dec(x_23);
x_102 = lean_ctor_get(x_3, 0);
x_103 = lean_ctor_get(x_3, 1);
x_104 = lean_ctor_get(x_3, 2);
x_105 = lean_ctor_get(x_3, 3);
x_106 = lean_ctor_get(x_3, 4);
x_107 = lean_ctor_get(x_3, 5);
x_108 = lean_ptr_addr(x_107);
x_109 = lean_ptr_addr(x_100);
x_110 = lean_usize_dec_eq(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; uint8_t x_118; 
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
x_118 = !lean_is_exclusive(x_3);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_3, 5);
lean_dec(x_119);
x_120 = lean_ctor_get(x_3, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_3, 3);
lean_dec(x_121);
x_122 = lean_ctor_get(x_3, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_3, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_3, 0);
lean_dec(x_124);
x_111 = x_3;
x_112 = x_118;
goto block_117;
}
else
{
lean_dec(x_3);
x_111 = lean_box(0);
x_112 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_113; 
if (x_112 == 0)
{
lean_ctor_set(x_111, 5, x_100);
x_113 = x_111;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_103);
lean_ctor_set(x_116, 2, x_104);
lean_ctor_set(x_116, 3, x_105);
lean_ctor_set(x_116, 4, x_106);
lean_ctor_set(x_116, 5, x_100);
x_113 = x_116;
goto block_115;
}
block_115:
{
uint8_t x_114; 
x_114 = lean_unbox(x_101);
lean_dec(x_101);
x_10 = x_114;
x_11 = x_113;
goto block_15;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_100);
x_125 = lean_unbox(x_101);
lean_dec(x_101);
x_10 = x_125;
x_11 = x_3;
goto block_15;
}
}
case 8:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; uint8_t x_134; 
x_126 = lean_ctor_get(x_23, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_23, 1);
lean_inc(x_127);
lean_dec(x_23);
x_128 = lean_ctor_get(x_3, 0);
x_129 = lean_ctor_get(x_3, 1);
x_130 = lean_ctor_get(x_3, 2);
x_131 = lean_ctor_get(x_3, 3);
x_132 = lean_ptr_addr(x_131);
x_133 = lean_ptr_addr(x_126);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; uint8_t x_142; 
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
x_142 = !lean_is_exclusive(x_3);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_3, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_3, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_3, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_3, 0);
lean_dec(x_146);
x_135 = x_3;
x_136 = x_142;
goto block_141;
}
else
{
lean_dec(x_3);
x_135 = lean_box(0);
x_136 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_137; 
if (x_136 == 0)
{
lean_ctor_set(x_135, 3, x_126);
x_137 = x_135;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_129);
lean_ctor_set(x_140, 2, x_130);
lean_ctor_set(x_140, 3, x_126);
x_137 = x_140;
goto block_139;
}
block_139:
{
uint8_t x_138; 
x_138 = lean_unbox(x_127);
lean_dec(x_127);
x_10 = x_138;
x_11 = x_137;
goto block_15;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_126);
x_147 = lean_unbox(x_127);
lean_dec(x_127);
x_10 = x_147;
x_11 = x_3;
goto block_15;
}
}
case 10:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; uint8_t x_155; 
x_148 = lean_ctor_get(x_23, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_23, 1);
lean_inc(x_149);
lean_dec(x_23);
x_150 = lean_ctor_get(x_3, 0);
x_151 = lean_ctor_get(x_3, 1);
x_152 = lean_ctor_get(x_3, 2);
x_153 = lean_ptr_addr(x_152);
x_154 = lean_ptr_addr(x_148);
x_155 = lean_usize_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; uint8_t x_163; 
lean_inc(x_151);
lean_inc(x_150);
x_163 = !lean_is_exclusive(x_3);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_3, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_3, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_3, 0);
lean_dec(x_166);
x_156 = x_3;
x_157 = x_163;
goto block_162;
}
else
{
lean_dec(x_3);
x_156 = lean_box(0);
x_157 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_158; 
if (x_157 == 0)
{
lean_ctor_set(x_156, 2, x_148);
x_158 = x_156;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_161, 0, x_150);
lean_ctor_set(x_161, 1, x_151);
lean_ctor_set(x_161, 2, x_148);
x_158 = x_161;
goto block_160;
}
block_160:
{
uint8_t x_159; 
x_159 = lean_unbox(x_149);
lean_dec(x_149);
x_10 = x_159;
x_11 = x_158;
goto block_15;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_148);
x_167 = lean_unbox(x_149);
lean_dec(x_149);
x_10 = x_167;
x_11 = x_3;
goto block_15;
}
}
case 11:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; size_t x_175; size_t x_176; uint8_t x_177; 
x_168 = lean_ctor_get(x_23, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_23, 1);
lean_inc(x_169);
lean_dec(x_23);
x_170 = lean_ctor_get(x_3, 0);
x_171 = lean_ctor_get(x_3, 1);
x_172 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_173 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_174 = lean_ctor_get(x_3, 2);
x_175 = lean_ptr_addr(x_174);
x_176 = lean_ptr_addr(x_168);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; uint8_t x_185; 
lean_inc(x_171);
lean_inc(x_170);
x_185 = !lean_is_exclusive(x_3);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_3, 2);
lean_dec(x_186);
x_187 = lean_ctor_get(x_3, 1);
lean_dec(x_187);
x_188 = lean_ctor_get(x_3, 0);
lean_dec(x_188);
x_178 = x_3;
x_179 = x_185;
goto block_184;
}
else
{
lean_dec(x_3);
x_178 = lean_box(0);
x_179 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_180; 
if (x_179 == 0)
{
lean_ctor_set(x_178, 2, x_168);
x_180 = x_178;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(x_183, 0, x_170);
lean_ctor_set(x_183, 1, x_171);
lean_ctor_set(x_183, 2, x_168);
lean_ctor_set_uint8(x_183, sizeof(void*)*3, x_172);
lean_ctor_set_uint8(x_183, sizeof(void*)*3 + 1, x_173);
x_180 = x_183;
goto block_182;
}
block_182:
{
uint8_t x_181; 
x_181 = lean_unbox(x_169);
lean_dec(x_169);
x_10 = x_181;
x_11 = x_180;
goto block_15;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_168);
x_189 = lean_unbox(x_169);
lean_dec(x_169);
x_10 = x_189;
x_11 = x_3;
goto block_15;
}
}
case 12:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; size_t x_197; size_t x_198; uint8_t x_199; 
x_190 = lean_ctor_get(x_23, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_23, 1);
lean_inc(x_191);
lean_dec(x_23);
x_192 = lean_ctor_get(x_3, 0);
x_193 = lean_ctor_get(x_3, 1);
x_194 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_195 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_196 = lean_ctor_get(x_3, 2);
x_197 = lean_ptr_addr(x_196);
x_198 = lean_ptr_addr(x_190);
x_199 = lean_usize_dec_eq(x_197, x_198);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; uint8_t x_207; 
lean_inc(x_193);
lean_inc(x_192);
x_207 = !lean_is_exclusive(x_3);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_3, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_3, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_3, 0);
lean_dec(x_210);
x_200 = x_3;
x_201 = x_207;
goto block_206;
}
else
{
lean_dec(x_3);
x_200 = lean_box(0);
x_201 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_202; 
if (x_201 == 0)
{
lean_ctor_set(x_200, 2, x_190);
x_202 = x_200;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(x_205, 0, x_192);
lean_ctor_set(x_205, 1, x_193);
lean_ctor_set(x_205, 2, x_190);
lean_ctor_set_uint8(x_205, sizeof(void*)*3, x_194);
lean_ctor_set_uint8(x_205, sizeof(void*)*3 + 1, x_195);
x_202 = x_205;
goto block_204;
}
block_204:
{
uint8_t x_203; 
x_203 = lean_unbox(x_191);
lean_dec(x_191);
x_10 = x_203;
x_11 = x_202;
goto block_15;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_190);
x_211 = lean_unbox(x_191);
lean_dec(x_191);
x_10 = x_211;
x_11 = x_3;
goto block_15;
}
}
case 13:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; size_t x_216; size_t x_217; uint8_t x_218; 
x_212 = lean_ctor_get(x_23, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_23, 1);
lean_inc(x_213);
lean_dec(x_23);
x_214 = lean_ctor_get(x_3, 0);
x_215 = lean_ctor_get(x_3, 1);
x_216 = lean_ptr_addr(x_215);
x_217 = lean_ptr_addr(x_212);
x_218 = lean_usize_dec_eq(x_216, x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; uint8_t x_226; 
lean_inc(x_214);
x_226 = !lean_is_exclusive(x_3);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_3, 1);
lean_dec(x_227);
x_228 = lean_ctor_get(x_3, 0);
lean_dec(x_228);
x_219 = x_3;
x_220 = x_226;
goto block_225;
}
else
{
lean_dec(x_3);
x_219 = lean_box(0);
x_220 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_221; 
if (x_220 == 0)
{
lean_ctor_set(x_219, 1, x_212);
x_221 = x_219;
goto block_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_224, 0, x_214);
lean_ctor_set(x_224, 1, x_212);
x_221 = x_224;
goto block_223;
}
block_223:
{
uint8_t x_222; 
x_222 = lean_unbox(x_213);
lean_dec(x_213);
x_10 = x_222;
x_11 = x_221;
goto block_15;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_212);
x_229 = lean_unbox(x_213);
lean_dec(x_213);
x_10 = x_229;
x_11 = x_3;
goto block_15;
}
}
default: 
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_dec_ref(x_3);
x_230 = lean_ctor_get(x_23, 1);
lean_inc(x_230);
lean_dec(x_23);
x_231 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
x_232 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(x_231);
x_233 = lean_unbox(x_230);
lean_dec(x_230);
x_10 = x_233;
x_11 = x_232;
goto block_15;
}
}
}
else
{
lean_dec_ref(x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_5, x_4, x_15);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_43);
x_17 = x_43;
goto block_42;
}
case 1:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_44);
x_17 = x_44;
goto block_42;
}
default: 
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_45);
x_17 = x_45;
goto block_42;
}
}
block_42:
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc(x_2);
x_18 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_33; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
x_22 = x_19;
x_23 = x_33;
goto block_32;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_14, x_20);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_21);
x_25 = x_31;
goto block_30;
}
block_30:
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_array_uset(x_16, x_4, x_25);
x_4 = x_27;
x_5 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_34 = lean_ctor_get(x_18, 0);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
x_35 = x_18;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_7 = x_4;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_9 = lean_st_ref_take(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_ctor_get(x_9, 6);
x_16 = lean_ctor_get(x_9, 7);
x_17 = lean_ctor_get(x_9, 8);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 2);
lean_dec(x_33);
x_18 = x_9;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_num___override(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_22);
x_23 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_22);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_23);
x_24 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 4, x_13);
lean_ctor_set(x_28, 5, x_14);
lean_ctor_set(x_28, 6, x_15);
lean_ctor_set(x_28, 7, x_16);
lean_ctor_set(x_28, 8, x_17);
x_24 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(x_5);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_6);
lean_inc(x_11);
x_12 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_67; 
x_13 = lean_ctor_get(x_12, 0);
x_67 = !lean_is_exclusive(x_12);
if (x_67 == 0)
{
x_14 = x_12;
x_15 = x_67;
goto block_66;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_18);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_64; 
lean_del_object(x_14);
x_22 = lean_ctor_get(x_13, 0);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_13, 1);
lean_dec(x_65);
x_23 = x_13;
x_24 = x_64;
goto block_63;
}
else
{
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_25; lean_object* x_26; 
x_25 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
x_26 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_25, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_54; 
x_27 = lean_ctor_get(x_26, 0);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
x_28 = x_26;
x_29 = x_54;
goto block_53;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_52; 
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_st_ref_take(x_6);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_52 = !lean_is_exclusive(x_31);
if (x_52 == 0)
{
x_34 = x_31;
x_35 = x_52;
goto block_51;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_52;
goto block_51;
}
block_51:
{
uint8_t x_36; lean_object* x_37; 
x_36 = 1;
lean_inc(x_30);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 11);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 0, x_30);
x_37 = x_23;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_50, 0, x_30);
lean_ctor_set(x_50, 1, x_1);
x_37 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_37);
lean_inc_ref(x_39);
x_40 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_36, x_32, x_39);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_40);
x_41 = x_34;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_33);
x_41 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_st_ref_set(x_6, x_41);
lean_dec(x_6);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_22);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_43);
x_44 = x_28;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_del_object(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_55 = lean_ctor_get(x_26, 0);
x_62 = !lean_is_exclusive(x_26);
if (x_62 == 0)
{
x_56 = x_26;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_68 = lean_ctor_get(x_12, 0);
x_75 = !lean_is_exclusive(x_12);
if (x_75 == 0)
{
x_69 = x_12;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_12);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_76 = lean_ctor_get(x_10, 0);
x_83 = !lean_is_exclusive(x_10);
if (x_83 == 0)
{
x_77 = x_10;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_10);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = 1;
x_8 = l_Lean_instSingletonFVarIdFVarIdSet;
lean_inc(x_1);
x_9 = lean_apply_1(x_8, x_1);
x_10 = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(x_7, x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_1);
return x_10;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_8;
}
else
{
if (x_8 == 0)
{
lean_dec(x_2);
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(x_2, x_5, x_9, x_10);
return x_11;
}
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_59; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_59 = !lean_is_exclusive(x_5);
if (x_59 == 0)
{
x_16 = x_5;
x_17 = x_59;
goto block_58;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_ctor_get(x_14, 2);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
if (x_17 == 0)
{
x_22 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_54; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 2);
lean_dec(x_55);
x_56 = lean_ctor_get(x_14, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_14, 0);
lean_dec(x_57);
x_26 = x_14;
x_27 = x_54;
goto block_53;
}
else
{
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_array_uget_borrowed(x_2, x_4);
x_29 = lean_array_fget(x_18, x_19);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_19, x_30);
lean_dec(x_19);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_31);
x_32 = x_26;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_31);
lean_ctor_set(x_52, 2, x_20);
x_32 = x_52;
goto block_51;
}
block_51:
{
uint8_t x_33; 
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = l_Lean_instBEqFVarId_beq(x_39, x_1);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_29);
lean_del_object(x_16);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_15);
x_7 = x_41;
goto block_11;
}
else
{
uint8_t x_42; 
x_42 = lean_unbox(x_15);
switch (x_42) {
case 0:
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_29, sizeof(void*)*3);
lean_dec(x_29);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = lean_unbox(x_15);
lean_dec(x_15);
x_33 = x_44;
goto block_38;
}
else
{
uint8_t x_45; 
lean_dec(x_15);
x_45 = 1;
x_33 = x_45;
goto block_38;
}
}
case 1:
{
uint8_t x_46; 
lean_dec(x_29);
x_46 = lean_unbox(x_15);
lean_dec(x_15);
x_33 = x_46;
goto block_38;
}
default: 
{
uint8_t x_47; 
lean_dec(x_15);
x_47 = lean_ctor_get_uint8(x_29, sizeof(void*)*3);
lean_dec(x_29);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = 0;
x_33 = x_48;
goto block_38;
}
else
{
uint8_t x_49; 
x_49 = 1;
x_33 = x_49;
goto block_38;
}
}
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_29);
lean_del_object(x_16);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_32);
lean_ctor_set(x_50, 1, x_15);
x_7 = x_50;
goto block_11;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(x_33);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_32);
x_35 = x_16;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
x_7 = x_35;
goto block_11;
}
}
}
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 9:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_86; 
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_ctor_get(x_21, 1);
x_86 = !lean_is_exclusive(x_21);
if (x_86 == 0)
{
x_24 = x_21;
x_25 = x_86;
goto block_85;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_26; 
lean_inc_ref(x_23);
lean_inc(x_22);
if (x_25 == 0)
{
x_26 = x_24;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_22);
lean_ctor_set(x_84, 1, x_23);
x_26 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_27; 
x_27 = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(x_22, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_74; 
x_28 = lean_ctor_get(x_27, 0);
x_74 = !lean_is_exclusive(x_27);
if (x_74 == 0)
{
x_29 = x_27;
x_30 = x_74;
goto block_73;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_74;
goto block_73;
}
block_73:
{
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
lean_del_object(x_29);
lean_dec_ref(x_26);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_ctor_get(x_31, 3);
lean_inc_ref(x_32);
lean_dec(x_31);
x_33 = 2;
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get_size(x_32);
x_36 = l_Array_toSubarray___redArg(x_32, x_34, x_35);
x_37 = lean_box(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_size(x_23);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(x_2, x_23, x_39, x_40, x_38);
lean_dec_ref(x_23);
lean_dec(x_2);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_50; 
x_42 = lean_ctor_get(x_41, 0);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
x_43 = x_41;
x_44 = x_50;
goto block_49;
}
else
{
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_45);
x_46 = x_43;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_51 = lean_ctor_get(x_41, 0);
x_58 = !lean_is_exclusive(x_41);
if (x_58 == 0)
{
x_52 = x_41;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_28);
lean_dec_ref(x_23);
x_59 = 1;
x_60 = l_Lean_instSingletonFVarIdFVarIdSet;
x_61 = lean_apply_1(x_60, x_2);
x_62 = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(x_59, x_26, x_61);
lean_dec(x_61);
lean_dec_ref(x_26);
if (x_62 == 0)
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_63 = 2;
x_64 = lean_box(x_63);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_64);
x_65 = x_29;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_68 = 0;
x_69 = lean_box(x_68);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_69);
x_70 = x_29;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_69);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_2);
x_75 = lean_ctor_get(x_27, 0);
x_82 = !lean_is_exclusive(x_27);
if (x_82 == 0)
{
x_76 = x_27;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_27);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
case 10:
{
lean_object* x_87; uint8_t x_88; uint8_t x_113; 
x_113 = !lean_is_exclusive(x_1);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_1, 0);
lean_dec(x_114);
x_87 = x_1;
x_88 = x_113;
goto block_112;
}
else
{
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_111; 
x_89 = lean_ctor_get(x_21, 0);
x_90 = lean_ctor_get(x_21, 1);
x_111 = !lean_is_exclusive(x_21);
if (x_111 == 0)
{
x_91 = x_21;
x_92 = x_111;
goto block_110;
}
else
{
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_21);
x_91 = lean_box(0);
x_92 = x_111;
goto block_110;
}
block_110:
{
uint8_t x_93; lean_object* x_94; 
x_93 = 1;
if (x_92 == 0)
{
x_94 = x_91;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_89);
lean_ctor_set(x_109, 1, x_90);
x_94 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Lean_instSingletonFVarIdFVarIdSet;
x_96 = lean_apply_1(x_95, x_2);
x_97 = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(x_93, x_94, x_96);
lean_dec(x_96);
lean_dec_ref(x_94);
if (x_97 == 0)
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_98 = 2;
x_99 = lean_box(x_98);
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_99);
x_100 = x_87;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_99);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_103 = 0;
x_104 = lean_box(x_103);
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_104);
x_105 = x_87;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_104);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
}
case 4:
{
lean_object* x_115; uint8_t x_116; uint8_t x_141; 
x_141 = !lean_is_exclusive(x_1);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_1, 0);
lean_dec(x_142);
x_115 = x_1;
x_116 = x_141;
goto block_140;
}
else
{
lean_dec(x_1);
x_115 = lean_box(0);
x_116 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_139; 
x_117 = lean_ctor_get(x_21, 0);
x_118 = lean_ctor_get(x_21, 1);
x_139 = !lean_is_exclusive(x_21);
if (x_139 == 0)
{
x_119 = x_21;
x_120 = x_139;
goto block_138;
}
else
{
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_21);
x_119 = lean_box(0);
x_120 = x_139;
goto block_138;
}
block_138:
{
uint8_t x_121; lean_object* x_122; 
x_121 = 1;
if (x_120 == 0)
{
x_122 = x_119;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_137, 0, x_117);
lean_ctor_set(x_137, 1, x_118);
x_122 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = l_Lean_instSingletonFVarIdFVarIdSet;
x_124 = lean_apply_1(x_123, x_2);
x_125 = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(x_121, x_122, x_124);
lean_dec(x_124);
lean_dec_ref(x_122);
if (x_125 == 0)
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_126 = 2;
x_127 = lean_box(x_126);
if (x_116 == 0)
{
lean_ctor_set(x_115, 0, x_127);
x_128 = x_115;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_127);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
else
{
uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_131 = 0;
x_132 = lean_box(x_131);
if (x_116 == 0)
{
lean_ctor_set(x_115, 0, x_132);
x_133 = x_115;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_132);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
}
default: 
{
lean_dec(x_21);
goto block_19;
}
}
}
else
{
goto block_19;
}
block_19:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = 1;
x_10 = l_Lean_instSingletonFVarIdFVarIdSet;
x_11 = lean_apply_1(x_10, x_2);
x_12 = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(x_9, x_1, x_11);
lean_dec(x_11);
lean_dec_ref(x_1);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 2;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_29);
x_9 = x_29;
goto block_28;
}
case 1:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
x_9 = x_30;
goto block_28;
}
default: 
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_31);
x_9 = x_31;
goto block_28;
}
}
block_28:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_1, x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_10, 0);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
x_21 = x_10;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget_borrowed(x_4, x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_14);
x_16 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(x_14, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ptr_addr(x_14);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = lean_array_fset(x_4, x_3, x_17);
lean_dec(x_3);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_3, x_25);
lean_dec(x_3);
x_3 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_16, 0);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
x_29 = x_16;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(245u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = 1;
x_13 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_12, x_3);
lean_inc(x_1);
x_14 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(x_13, x_1);
x_15 = 1;
if (x_14 == 0)
{
lean_object* x_16; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_11);
lean_inc_ref(x_2);
lean_inc(x_1);
x_16 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_134; 
x_17 = lean_ctor_get(x_16, 0);
x_134 = !lean_is_exclusive(x_16);
if (x_134 == 0)
{
x_18 = x_16;
x_19 = x_134;
goto block_133;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_20; lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_118; 
lean_inc(x_27);
lean_del_object(x_18);
x_29 = lean_ctor_get(x_17, 0);
x_118 = !lean_is_exclusive(x_17);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_17, 1);
lean_dec(x_119);
x_30 = x_17;
x_31 = x_118;
goto block_117;
}
else
{
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_32; 
lean_inc(x_1);
x_32 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(x_13, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_108; 
x_33 = lean_ctor_get(x_32, 0);
x_108 = !lean_is_exclusive(x_32);
if (x_108 == 0)
{
x_34 = x_32;
x_35 = x_108;
goto block_107;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_36; lean_object* x_44; uint8_t x_49; 
x_49 = lean_unbox(x_33);
lean_dec(x_33);
switch (x_49) {
case 0:
{
size_t x_50; size_t x_51; uint8_t x_52; 
lean_del_object(x_34);
lean_del_object(x_30);
lean_dec(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_50 = lean_ptr_addr(x_11);
x_51 = lean_ptr_addr(x_29);
x_52 = lean_usize_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_inc_ref(x_10);
x_59 = !lean_is_exclusive(x_3);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_3, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_3, 0);
lean_dec(x_61);
x_53 = x_3;
x_54 = x_59;
goto block_58;
}
else
{
lean_dec(x_3);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_29);
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_29);
x_55 = x_57;
goto block_56;
}
block_56:
{
x_44 = x_55;
goto block_48;
}
}
}
else
{
lean_dec(x_29);
x_44 = x_3;
goto block_48;
}
}
case 1:
{
lean_object* x_62; 
lean_del_object(x_34);
lean_del_object(x_30);
lean_dec(x_27);
x_62 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(x_1, x_2, x_29, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_86; 
x_63 = lean_ctor_get(x_62, 0);
x_86 = !lean_is_exclusive(x_62);
if (x_86 == 0)
{
x_64 = x_62;
x_65 = x_86;
goto block_85;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_66; size_t x_73; size_t x_74; uint8_t x_75; 
x_73 = lean_ptr_addr(x_11);
x_74 = lean_ptr_addr(x_63);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_inc_ref(x_10);
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_3, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 0);
lean_dec(x_84);
x_76 = x_3;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_3);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 1, x_63);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_10);
lean_ctor_set(x_80, 1, x_63);
x_78 = x_80;
goto block_79;
}
block_79:
{
x_66 = x_78;
goto block_72;
}
}
}
else
{
lean_dec(x_63);
x_66 = x_3;
goto block_72;
}
block_72:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_box(x_15);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
if (x_65 == 0)
{
lean_ctor_set(x_64, 0, x_68);
x_69 = x_64;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec_ref(x_3);
x_87 = lean_ctor_get(x_62, 0);
x_94 = !lean_is_exclusive(x_62);
if (x_94 == 0)
{
x_88 = x_62;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_62);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
default: 
{
size_t x_95; size_t x_96; uint8_t x_97; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_95 = lean_ptr_addr(x_11);
x_96 = lean_ptr_addr(x_29);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_inc_ref(x_10);
x_104 = !lean_is_exclusive(x_3);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_3, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_3, 0);
lean_dec(x_106);
x_98 = x_3;
x_99 = x_104;
goto block_103;
}
else
{
lean_dec(x_3);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
lean_ctor_set(x_98, 1, x_29);
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_10);
lean_ctor_set(x_102, 1, x_29);
x_100 = x_102;
goto block_101;
}
block_101:
{
x_36 = x_100;
goto block_43;
}
}
}
else
{
lean_dec(x_29);
x_36 = x_3;
goto block_43;
}
}
}
block_43:
{
lean_object* x_37; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_36);
x_37 = x_30;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_27);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_37);
x_38 = x_34;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
block_48:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(x_15);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_del_object(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_109 = lean_ctor_get(x_32, 0);
x_116 = !lean_is_exclusive(x_32);
if (x_116 == 0)
{
x_110 = x_32;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_32);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
}
else
{
lean_object* x_120; size_t x_121; size_t x_122; uint8_t x_123; 
lean_dec_ref(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_17, 0);
lean_inc(x_120);
lean_dec(x_17);
x_121 = lean_ptr_addr(x_11);
x_122 = lean_ptr_addr(x_120);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; uint8_t x_130; 
lean_inc_ref(x_10);
x_130 = !lean_is_exclusive(x_3);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_3, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_3, 0);
lean_dec(x_132);
x_124 = x_3;
x_125 = x_130;
goto block_129;
}
else
{
lean_dec(x_3);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
lean_ctor_set(x_124, 1, x_120);
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_10);
lean_ctor_set(x_128, 1, x_120);
x_126 = x_128;
goto block_127;
}
block_127:
{
x_20 = x_126;
goto block_26;
}
}
}
else
{
lean_dec(x_120);
x_20 = x_3;
goto block_26;
}
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_box(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_22);
x_23 = x_18;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_dec_ref(x_13);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_135 = lean_box(x_15);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_3);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
case 2:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_3, 0);
x_139 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_139);
lean_inc_ref(x_2);
lean_inc(x_1);
x_140 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_139, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_138, 2);
x_145 = lean_ctor_get(x_138, 3);
x_146 = lean_ctor_get(x_138, 4);
lean_inc(x_6);
lean_inc_ref(x_146);
x_147 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_146, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_193; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_ctor_get(x_148, 0);
x_193 = !lean_is_exclusive(x_148);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_148, 1);
lean_dec(x_194);
x_150 = x_148;
x_151 = x_193;
goto block_192;
}
else
{
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_box(0);
x_151 = x_193;
goto block_192;
}
block_192:
{
uint8_t x_152; lean_object* x_153; 
x_152 = 1;
lean_inc_ref(x_144);
lean_inc_ref(x_145);
lean_inc_ref(x_138);
x_153 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_152, x_138, x_145, x_144, x_149, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_183; 
x_154 = lean_ctor_get(x_153, 0);
x_183 = !lean_is_exclusive(x_153);
if (x_183 == 0)
{
x_155 = x_153;
x_156 = x_183;
goto block_182;
}
else
{
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_box(0);
x_156 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_157; uint8_t x_165; size_t x_176; size_t x_177; uint8_t x_178; 
x_176 = lean_ptr_addr(x_139);
x_177 = lean_ptr_addr(x_142);
x_178 = lean_usize_dec_eq(x_176, x_177);
if (x_178 == 0)
{
x_165 = x_178;
goto block_175;
}
else
{
size_t x_179; size_t x_180; uint8_t x_181; 
x_179 = lean_ptr_addr(x_138);
x_180 = lean_ptr_addr(x_154);
x_181 = lean_usize_dec_eq(x_179, x_180);
x_165 = x_181;
goto block_175;
}
block_164:
{
lean_object* x_158; 
if (x_151 == 0)
{
lean_ctor_set(x_150, 1, x_143);
lean_ctor_set(x_150, 0, x_157);
x_158 = x_150;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_157);
lean_ctor_set(x_163, 1, x_143);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_156 == 0)
{
lean_ctor_set(x_155, 0, x_158);
x_159 = x_155;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_158);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
block_175:
{
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; uint8_t x_172; 
x_172 = !lean_is_exclusive(x_3);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_3, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_3, 0);
lean_dec(x_174);
x_166 = x_3;
x_167 = x_172;
goto block_171;
}
else
{
lean_dec(x_3);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
lean_ctor_set(x_166, 1, x_142);
lean_ctor_set(x_166, 0, x_154);
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_154);
lean_ctor_set(x_170, 1, x_142);
x_168 = x_170;
goto block_169;
}
block_169:
{
x_157 = x_168;
goto block_164;
}
}
}
else
{
lean_dec(x_154);
lean_dec(x_142);
x_157 = x_3;
goto block_164;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_del_object(x_150);
lean_dec(x_143);
lean_dec(x_142);
lean_dec_ref(x_3);
x_184 = lean_ctor_get(x_153, 0);
x_191 = !lean_is_exclusive(x_153);
if (x_191 == 0)
{
x_185 = x_153;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_dec(x_153);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
}
else
{
lean_dec(x_143);
lean_dec(x_142);
lean_dec_ref(x_3);
lean_dec(x_6);
return x_147;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_140;
}
}
case 3:
{
lean_object* x_195; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_195 = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(x_3, x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_204; 
x_196 = lean_ctor_get(x_195, 0);
x_204 = !lean_is_exclusive(x_195);
if (x_204 == 0)
{
x_197 = x_195;
x_198 = x_204;
goto block_203;
}
else
{
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_box(0);
x_198 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_3);
lean_ctor_set(x_199, 1, x_196);
if (x_198 == 0)
{
lean_ctor_set(x_197, 0, x_199);
x_200 = x_197;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_199);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_212; 
lean_dec_ref(x_3);
x_205 = lean_ctor_get(x_195, 0);
x_212 = !lean_is_exclusive(x_195);
if (x_212 == 0)
{
x_206 = x_195;
x_207 = x_212;
goto block_211;
}
else
{
lean_inc(x_205);
lean_dec(x_195);
x_206 = lean_box(0);
x_207 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_208; 
if (x_207 == 0)
{
x_208 = x_206;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_205);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
}
}
case 4:
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_213);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
lean_inc_ref(x_3);
x_214 = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(x_3, x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_267; 
x_215 = lean_ctor_get(x_214, 0);
x_267 = !lean_is_exclusive(x_214);
if (x_267 == 0)
{
x_216 = x_214;
x_217 = x_267;
goto block_266;
}
else
{
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_box(0);
x_217 = x_267;
goto block_266;
}
block_266:
{
uint8_t x_218; 
x_218 = lean_unbox(x_215);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec_ref(x_213);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_3);
lean_ctor_set(x_219, 1, x_215);
if (x_217 == 0)
{
lean_ctor_set(x_216, 0, x_219);
x_220 = x_216;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_219);
x_220 = x_222;
goto block_221;
}
block_221:
{
return x_220;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_265; 
lean_del_object(x_216);
x_223 = lean_ctor_get(x_213, 0);
x_224 = lean_ctor_get(x_213, 1);
x_225 = lean_ctor_get(x_213, 2);
x_226 = lean_ctor_get(x_213, 3);
x_265 = !lean_is_exclusive(x_213);
if (x_265 == 0)
{
x_227 = x_213;
x_228 = x_265;
goto block_264;
}
else
{
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_213);
x_227 = lean_box(0);
x_228 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_226);
x_230 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(x_1, x_2, x_229, x_226, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_255; 
x_231 = lean_ctor_get(x_230, 0);
x_255 = !lean_is_exclusive(x_230);
if (x_255 == 0)
{
x_232 = x_230;
x_233 = x_255;
goto block_254;
}
else
{
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_box(0);
x_233 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_234; size_t x_240; size_t x_241; uint8_t x_242; 
x_240 = lean_ptr_addr(x_226);
lean_dec_ref(x_226);
x_241 = lean_ptr_addr(x_231);
x_242 = lean_usize_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; uint8_t x_244; uint8_t x_252; 
x_252 = !lean_is_exclusive(x_3);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_3, 0);
lean_dec(x_253);
x_243 = x_3;
x_244 = x_252;
goto block_251;
}
else
{
lean_dec(x_3);
x_243 = lean_box(0);
x_244 = x_252;
goto block_251;
}
block_251:
{
lean_object* x_245; 
if (x_228 == 0)
{
lean_ctor_set(x_227, 3, x_231);
x_245 = x_227;
goto block_249;
}
else
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_250, 0, x_223);
lean_ctor_set(x_250, 1, x_224);
lean_ctor_set(x_250, 2, x_225);
lean_ctor_set(x_250, 3, x_231);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_244 == 0)
{
lean_ctor_set(x_243, 0, x_245);
x_246 = x_243;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_248, 0, x_245);
x_246 = x_248;
goto block_247;
}
block_247:
{
x_234 = x_246;
goto block_239;
}
}
}
}
else
{
lean_dec(x_231);
lean_del_object(x_227);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
x_234 = x_3;
goto block_239;
}
block_239:
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_215);
if (x_233 == 0)
{
lean_ctor_set(x_232, 0, x_235);
x_236 = x_232;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_235);
x_236 = x_238;
goto block_237;
}
block_237:
{
return x_236;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_263; 
lean_del_object(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec(x_215);
lean_dec_ref(x_3);
x_256 = lean_ctor_get(x_230, 0);
x_263 = !lean_is_exclusive(x_230);
if (x_263 == 0)
{
x_257 = x_230;
x_258 = x_263;
goto block_262;
}
else
{
lean_inc(x_256);
lean_dec(x_230);
x_257 = lean_box(0);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_258 == 0)
{
x_259 = x_257;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_256);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_275; 
lean_dec_ref(x_3);
lean_dec_ref(x_213);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_268 = lean_ctor_get(x_214, 0);
x_275 = !lean_is_exclusive(x_214);
if (x_275 == 0)
{
x_269 = x_214;
x_270 = x_275;
goto block_274;
}
else
{
lean_inc(x_268);
lean_dec(x_214);
x_269 = lean_box(0);
x_270 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_271; 
if (x_270 == 0)
{
x_271 = x_269;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_268);
x_271 = x_273;
goto block_272;
}
block_272:
{
return x_271;
}
}
}
}
case 5:
{
lean_object* x_276; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_276 = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(x_3, x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_285; 
x_277 = lean_ctor_get(x_276, 0);
x_285 = !lean_is_exclusive(x_276);
if (x_285 == 0)
{
x_278 = x_276;
x_279 = x_285;
goto block_284;
}
else
{
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_box(0);
x_279 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_3);
lean_ctor_set(x_280, 1, x_277);
if (x_279 == 0)
{
lean_ctor_set(x_278, 0, x_280);
x_281 = x_278;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_280);
x_281 = x_283;
goto block_282;
}
block_282:
{
return x_281;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_293; 
lean_dec_ref(x_3);
x_286 = lean_ctor_get(x_276, 0);
x_293 = !lean_is_exclusive(x_276);
if (x_293 == 0)
{
x_287 = x_276;
x_288 = x_293;
goto block_292;
}
else
{
lean_inc(x_286);
lean_dec(x_276);
x_287 = lean_box(0);
x_288 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_289; 
if (x_288 == 0)
{
x_289 = x_287;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_286);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
}
case 6:
{
lean_object* x_294; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_294 = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(x_3, x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_303; 
x_295 = lean_ctor_get(x_294, 0);
x_303 = !lean_is_exclusive(x_294);
if (x_303 == 0)
{
x_296 = x_294;
x_297 = x_303;
goto block_302;
}
else
{
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_box(0);
x_297 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_3);
lean_ctor_set(x_298, 1, x_295);
if (x_297 == 0)
{
lean_ctor_set(x_296, 0, x_298);
x_299 = x_296;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_301, 0, x_298);
x_299 = x_301;
goto block_300;
}
block_300:
{
return x_299;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_311; 
lean_dec_ref(x_3);
x_304 = lean_ctor_get(x_294, 0);
x_311 = !lean_is_exclusive(x_294);
if (x_311 == 0)
{
x_305 = x_294;
x_306 = x_311;
goto block_310;
}
else
{
lean_inc(x_304);
lean_dec(x_294);
x_305 = lean_box(0);
x_306 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_307; 
if (x_306 == 0)
{
x_307 = x_305;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_304);
x_307 = x_309;
goto block_308;
}
block_308:
{
return x_307;
}
}
}
}
case 8:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; 
x_312 = lean_ctor_get(x_3, 0);
x_313 = lean_ctor_get(x_3, 1);
x_314 = lean_ctor_get(x_3, 2);
x_315 = lean_ctor_get(x_3, 3);
x_316 = 1;
x_317 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_316, x_3);
lean_inc(x_1);
x_318 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(x_317, x_1);
x_319 = 1;
if (x_318 == 0)
{
lean_object* x_320; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_315);
lean_inc_ref(x_2);
lean_inc(x_1);
x_320 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_315, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; uint8_t x_446; 
x_321 = lean_ctor_get(x_320, 0);
x_446 = !lean_is_exclusive(x_320);
if (x_446 == 0)
{
x_322 = x_320;
x_323 = x_446;
goto block_445;
}
else
{
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_box(0);
x_323 = x_446;
goto block_445;
}
block_445:
{
lean_object* x_324; lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_321, 1);
x_332 = lean_unbox(x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_428; 
lean_inc(x_331);
lean_del_object(x_322);
x_333 = lean_ctor_get(x_321, 0);
x_428 = !lean_is_exclusive(x_321);
if (x_428 == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_321, 1);
lean_dec(x_429);
x_334 = x_321;
x_335 = x_428;
goto block_427;
}
else
{
lean_inc(x_333);
lean_dec(x_321);
x_334 = lean_box(0);
x_335 = x_428;
goto block_427;
}
block_427:
{
lean_object* x_336; 
lean_inc(x_1);
x_336 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(x_317, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_418; 
x_337 = lean_ctor_get(x_336, 0);
x_418 = !lean_is_exclusive(x_336);
if (x_418 == 0)
{
x_338 = x_336;
x_339 = x_418;
goto block_417;
}
else
{
lean_inc(x_337);
lean_dec(x_336);
x_338 = lean_box(0);
x_339 = x_418;
goto block_417;
}
block_417:
{
lean_object* x_340; lean_object* x_348; uint8_t x_353; 
x_353 = lean_unbox(x_337);
lean_dec(x_337);
switch (x_353) {
case 0:
{
size_t x_354; size_t x_355; uint8_t x_356; 
lean_del_object(x_338);
lean_del_object(x_334);
lean_dec(x_331);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_354 = lean_ptr_addr(x_315);
x_355 = lean_ptr_addr(x_333);
x_356 = lean_usize_dec_eq(x_354, x_355);
if (x_356 == 0)
{
lean_object* x_357; uint8_t x_358; uint8_t x_363; 
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
x_363 = !lean_is_exclusive(x_3);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_3, 3);
lean_dec(x_364);
x_365 = lean_ctor_get(x_3, 2);
lean_dec(x_365);
x_366 = lean_ctor_get(x_3, 1);
lean_dec(x_366);
x_367 = lean_ctor_get(x_3, 0);
lean_dec(x_367);
x_357 = x_3;
x_358 = x_363;
goto block_362;
}
else
{
lean_dec(x_3);
x_357 = lean_box(0);
x_358 = x_363;
goto block_362;
}
block_362:
{
lean_object* x_359; 
if (x_358 == 0)
{
lean_ctor_set(x_357, 3, x_333);
x_359 = x_357;
goto block_360;
}
else
{
lean_object* x_361; 
x_361 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_361, 0, x_312);
lean_ctor_set(x_361, 1, x_313);
lean_ctor_set(x_361, 2, x_314);
lean_ctor_set(x_361, 3, x_333);
x_359 = x_361;
goto block_360;
}
block_360:
{
x_348 = x_359;
goto block_352;
}
}
}
else
{
lean_dec(x_333);
x_348 = x_3;
goto block_352;
}
}
case 1:
{
lean_object* x_368; 
lean_del_object(x_338);
lean_del_object(x_334);
lean_dec(x_331);
x_368 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(x_1, x_2, x_333, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; uint8_t x_371; uint8_t x_394; 
x_369 = lean_ctor_get(x_368, 0);
x_394 = !lean_is_exclusive(x_368);
if (x_394 == 0)
{
x_370 = x_368;
x_371 = x_394;
goto block_393;
}
else
{
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_box(0);
x_371 = x_394;
goto block_393;
}
block_393:
{
lean_object* x_372; size_t x_379; size_t x_380; uint8_t x_381; 
x_379 = lean_ptr_addr(x_315);
x_380 = lean_ptr_addr(x_369);
x_381 = lean_usize_dec_eq(x_379, x_380);
if (x_381 == 0)
{
lean_object* x_382; uint8_t x_383; uint8_t x_388; 
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
x_388 = !lean_is_exclusive(x_3);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_389 = lean_ctor_get(x_3, 3);
lean_dec(x_389);
x_390 = lean_ctor_get(x_3, 2);
lean_dec(x_390);
x_391 = lean_ctor_get(x_3, 1);
lean_dec(x_391);
x_392 = lean_ctor_get(x_3, 0);
lean_dec(x_392);
x_382 = x_3;
x_383 = x_388;
goto block_387;
}
else
{
lean_dec(x_3);
x_382 = lean_box(0);
x_383 = x_388;
goto block_387;
}
block_387:
{
lean_object* x_384; 
if (x_383 == 0)
{
lean_ctor_set(x_382, 3, x_369);
x_384 = x_382;
goto block_385;
}
else
{
lean_object* x_386; 
x_386 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_386, 0, x_312);
lean_ctor_set(x_386, 1, x_313);
lean_ctor_set(x_386, 2, x_314);
lean_ctor_set(x_386, 3, x_369);
x_384 = x_386;
goto block_385;
}
block_385:
{
x_372 = x_384;
goto block_378;
}
}
}
else
{
lean_dec(x_369);
x_372 = x_3;
goto block_378;
}
block_378:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_box(x_319);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
if (x_371 == 0)
{
lean_ctor_set(x_370, 0, x_374);
x_375 = x_370;
goto block_376;
}
else
{
lean_object* x_377; 
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_374);
x_375 = x_377;
goto block_376;
}
block_376:
{
return x_375;
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_402; 
lean_dec_ref(x_3);
x_395 = lean_ctor_get(x_368, 0);
x_402 = !lean_is_exclusive(x_368);
if (x_402 == 0)
{
x_396 = x_368;
x_397 = x_402;
goto block_401;
}
else
{
lean_inc(x_395);
lean_dec(x_368);
x_396 = lean_box(0);
x_397 = x_402;
goto block_401;
}
block_401:
{
lean_object* x_398; 
if (x_397 == 0)
{
x_398 = x_396;
goto block_399;
}
else
{
lean_object* x_400; 
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_395);
x_398 = x_400;
goto block_399;
}
block_399:
{
return x_398;
}
}
}
}
default: 
{
size_t x_403; size_t x_404; uint8_t x_405; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_403 = lean_ptr_addr(x_315);
x_404 = lean_ptr_addr(x_333);
x_405 = lean_usize_dec_eq(x_403, x_404);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; uint8_t x_412; 
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
x_412 = !lean_is_exclusive(x_3);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_3, 3);
lean_dec(x_413);
x_414 = lean_ctor_get(x_3, 2);
lean_dec(x_414);
x_415 = lean_ctor_get(x_3, 1);
lean_dec(x_415);
x_416 = lean_ctor_get(x_3, 0);
lean_dec(x_416);
x_406 = x_3;
x_407 = x_412;
goto block_411;
}
else
{
lean_dec(x_3);
x_406 = lean_box(0);
x_407 = x_412;
goto block_411;
}
block_411:
{
lean_object* x_408; 
if (x_407 == 0)
{
lean_ctor_set(x_406, 3, x_333);
x_408 = x_406;
goto block_409;
}
else
{
lean_object* x_410; 
x_410 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_410, 0, x_312);
lean_ctor_set(x_410, 1, x_313);
lean_ctor_set(x_410, 2, x_314);
lean_ctor_set(x_410, 3, x_333);
x_408 = x_410;
goto block_409;
}
block_409:
{
x_340 = x_408;
goto block_347;
}
}
}
else
{
lean_dec(x_333);
x_340 = x_3;
goto block_347;
}
}
}
block_347:
{
lean_object* x_341; 
if (x_335 == 0)
{
lean_ctor_set(x_334, 0, x_340);
x_341 = x_334;
goto block_345;
}
else
{
lean_object* x_346; 
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_340);
lean_ctor_set(x_346, 1, x_331);
x_341 = x_346;
goto block_345;
}
block_345:
{
lean_object* x_342; 
if (x_339 == 0)
{
lean_ctor_set(x_338, 0, x_341);
x_342 = x_338;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_344, 0, x_341);
x_342 = x_344;
goto block_343;
}
block_343:
{
return x_342;
}
}
}
block_352:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_box(x_319);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_351, 0, x_350);
return x_351;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; uint8_t x_421; uint8_t x_426; 
lean_del_object(x_334);
lean_dec(x_333);
lean_dec(x_331);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_419 = lean_ctor_get(x_336, 0);
x_426 = !lean_is_exclusive(x_336);
if (x_426 == 0)
{
x_420 = x_336;
x_421 = x_426;
goto block_425;
}
else
{
lean_inc(x_419);
lean_dec(x_336);
x_420 = lean_box(0);
x_421 = x_426;
goto block_425;
}
block_425:
{
lean_object* x_422; 
if (x_421 == 0)
{
x_422 = x_420;
goto block_423;
}
else
{
lean_object* x_424; 
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_419);
x_422 = x_424;
goto block_423;
}
block_423:
{
return x_422;
}
}
}
}
}
else
{
lean_object* x_430; size_t x_431; size_t x_432; uint8_t x_433; 
lean_dec_ref(x_317);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_430 = lean_ctor_get(x_321, 0);
lean_inc(x_430);
lean_dec(x_321);
x_431 = lean_ptr_addr(x_315);
x_432 = lean_ptr_addr(x_430);
x_433 = lean_usize_dec_eq(x_431, x_432);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; uint8_t x_440; 
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
x_440 = !lean_is_exclusive(x_3);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_441 = lean_ctor_get(x_3, 3);
lean_dec(x_441);
x_442 = lean_ctor_get(x_3, 2);
lean_dec(x_442);
x_443 = lean_ctor_get(x_3, 1);
lean_dec(x_443);
x_444 = lean_ctor_get(x_3, 0);
lean_dec(x_444);
x_434 = x_3;
x_435 = x_440;
goto block_439;
}
else
{
lean_dec(x_3);
x_434 = lean_box(0);
x_435 = x_440;
goto block_439;
}
block_439:
{
lean_object* x_436; 
if (x_435 == 0)
{
lean_ctor_set(x_434, 3, x_430);
x_436 = x_434;
goto block_437;
}
else
{
lean_object* x_438; 
x_438 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_438, 0, x_312);
lean_ctor_set(x_438, 1, x_313);
lean_ctor_set(x_438, 2, x_314);
lean_ctor_set(x_438, 3, x_430);
x_436 = x_438;
goto block_437;
}
block_437:
{
x_324 = x_436;
goto block_330;
}
}
}
else
{
lean_dec(x_430);
x_324 = x_3;
goto block_330;
}
}
block_330:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_box(x_319);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
if (x_323 == 0)
{
lean_ctor_set(x_322, 0, x_326);
x_327 = x_322;
goto block_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_326);
x_327 = x_329;
goto block_328;
}
block_328:
{
return x_327;
}
}
}
}
else
{
lean_dec_ref(x_317);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_320;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec_ref(x_317);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_447 = lean_box(x_319);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_3);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_449, 0, x_448);
return x_449;
}
}
case 9:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; lean_object* x_457; uint8_t x_458; uint8_t x_459; 
x_450 = lean_ctor_get(x_3, 0);
x_451 = lean_ctor_get(x_3, 1);
x_452 = lean_ctor_get(x_3, 2);
x_453 = lean_ctor_get(x_3, 3);
x_454 = lean_ctor_get(x_3, 4);
x_455 = lean_ctor_get(x_3, 5);
x_456 = 1;
x_457 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_456, x_3);
lean_inc(x_1);
x_458 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(x_457, x_1);
x_459 = 1;
if (x_458 == 0)
{
lean_object* x_460; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_455);
lean_inc_ref(x_2);
lean_inc(x_1);
x_460 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_455, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; uint8_t x_463; uint8_t x_594; 
x_461 = lean_ctor_get(x_460, 0);
x_594 = !lean_is_exclusive(x_460);
if (x_594 == 0)
{
x_462 = x_460;
x_463 = x_594;
goto block_593;
}
else
{
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_box(0);
x_463 = x_594;
goto block_593;
}
block_593:
{
lean_object* x_464; lean_object* x_471; uint8_t x_472; 
x_471 = lean_ctor_get(x_461, 1);
x_472 = lean_unbox(x_471);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_574; 
lean_inc(x_471);
lean_del_object(x_462);
x_473 = lean_ctor_get(x_461, 0);
x_574 = !lean_is_exclusive(x_461);
if (x_574 == 0)
{
lean_object* x_575; 
x_575 = lean_ctor_get(x_461, 1);
lean_dec(x_575);
x_474 = x_461;
x_475 = x_574;
goto block_573;
}
else
{
lean_inc(x_473);
lean_dec(x_461);
x_474 = lean_box(0);
x_475 = x_574;
goto block_573;
}
block_573:
{
lean_object* x_476; 
lean_inc(x_1);
x_476 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(x_457, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; uint8_t x_564; 
x_477 = lean_ctor_get(x_476, 0);
x_564 = !lean_is_exclusive(x_476);
if (x_564 == 0)
{
x_478 = x_476;
x_479 = x_564;
goto block_563;
}
else
{
lean_inc(x_477);
lean_dec(x_476);
x_478 = lean_box(0);
x_479 = x_564;
goto block_563;
}
block_563:
{
lean_object* x_480; lean_object* x_488; uint8_t x_493; 
x_493 = lean_unbox(x_477);
lean_dec(x_477);
switch (x_493) {
case 0:
{
size_t x_494; size_t x_495; uint8_t x_496; 
lean_del_object(x_478);
lean_del_object(x_474);
lean_dec(x_471);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_494 = lean_ptr_addr(x_455);
x_495 = lean_ptr_addr(x_473);
x_496 = lean_usize_dec_eq(x_494, x_495);
if (x_496 == 0)
{
lean_object* x_497; uint8_t x_498; uint8_t x_503; 
lean_inc_ref(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
x_503 = !lean_is_exclusive(x_3);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_504 = lean_ctor_get(x_3, 5);
lean_dec(x_504);
x_505 = lean_ctor_get(x_3, 4);
lean_dec(x_505);
x_506 = lean_ctor_get(x_3, 3);
lean_dec(x_506);
x_507 = lean_ctor_get(x_3, 2);
lean_dec(x_507);
x_508 = lean_ctor_get(x_3, 1);
lean_dec(x_508);
x_509 = lean_ctor_get(x_3, 0);
lean_dec(x_509);
x_497 = x_3;
x_498 = x_503;
goto block_502;
}
else
{
lean_dec(x_3);
x_497 = lean_box(0);
x_498 = x_503;
goto block_502;
}
block_502:
{
lean_object* x_499; 
if (x_498 == 0)
{
lean_ctor_set(x_497, 5, x_473);
x_499 = x_497;
goto block_500;
}
else
{
lean_object* x_501; 
x_501 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_501, 0, x_450);
lean_ctor_set(x_501, 1, x_451);
lean_ctor_set(x_501, 2, x_452);
lean_ctor_set(x_501, 3, x_453);
lean_ctor_set(x_501, 4, x_454);
lean_ctor_set(x_501, 5, x_473);
x_499 = x_501;
goto block_500;
}
block_500:
{
x_488 = x_499;
goto block_492;
}
}
}
else
{
lean_dec(x_473);
x_488 = x_3;
goto block_492;
}
}
case 1:
{
lean_object* x_510; 
lean_del_object(x_478);
lean_del_object(x_474);
lean_dec(x_471);
x_510 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(x_1, x_2, x_473, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; uint8_t x_513; uint8_t x_538; 
x_511 = lean_ctor_get(x_510, 0);
x_538 = !lean_is_exclusive(x_510);
if (x_538 == 0)
{
x_512 = x_510;
x_513 = x_538;
goto block_537;
}
else
{
lean_inc(x_511);
lean_dec(x_510);
x_512 = lean_box(0);
x_513 = x_538;
goto block_537;
}
block_537:
{
lean_object* x_514; size_t x_521; size_t x_522; uint8_t x_523; 
x_521 = lean_ptr_addr(x_455);
x_522 = lean_ptr_addr(x_511);
x_523 = lean_usize_dec_eq(x_521, x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; uint8_t x_530; 
lean_inc_ref(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
x_530 = !lean_is_exclusive(x_3);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_531 = lean_ctor_get(x_3, 5);
lean_dec(x_531);
x_532 = lean_ctor_get(x_3, 4);
lean_dec(x_532);
x_533 = lean_ctor_get(x_3, 3);
lean_dec(x_533);
x_534 = lean_ctor_get(x_3, 2);
lean_dec(x_534);
x_535 = lean_ctor_get(x_3, 1);
lean_dec(x_535);
x_536 = lean_ctor_get(x_3, 0);
lean_dec(x_536);
x_524 = x_3;
x_525 = x_530;
goto block_529;
}
else
{
lean_dec(x_3);
x_524 = lean_box(0);
x_525 = x_530;
goto block_529;
}
block_529:
{
lean_object* x_526; 
if (x_525 == 0)
{
lean_ctor_set(x_524, 5, x_511);
x_526 = x_524;
goto block_527;
}
else
{
lean_object* x_528; 
x_528 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_528, 0, x_450);
lean_ctor_set(x_528, 1, x_451);
lean_ctor_set(x_528, 2, x_452);
lean_ctor_set(x_528, 3, x_453);
lean_ctor_set(x_528, 4, x_454);
lean_ctor_set(x_528, 5, x_511);
x_526 = x_528;
goto block_527;
}
block_527:
{
x_514 = x_526;
goto block_520;
}
}
}
else
{
lean_dec(x_511);
x_514 = x_3;
goto block_520;
}
block_520:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_box(x_459);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
if (x_513 == 0)
{
lean_ctor_set(x_512, 0, x_516);
x_517 = x_512;
goto block_518;
}
else
{
lean_object* x_519; 
x_519 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_519, 0, x_516);
x_517 = x_519;
goto block_518;
}
block_518:
{
return x_517;
}
}
}
}
else
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; uint8_t x_546; 
lean_dec_ref(x_3);
x_539 = lean_ctor_get(x_510, 0);
x_546 = !lean_is_exclusive(x_510);
if (x_546 == 0)
{
x_540 = x_510;
x_541 = x_546;
goto block_545;
}
else
{
lean_inc(x_539);
lean_dec(x_510);
x_540 = lean_box(0);
x_541 = x_546;
goto block_545;
}
block_545:
{
lean_object* x_542; 
if (x_541 == 0)
{
x_542 = x_540;
goto block_543;
}
else
{
lean_object* x_544; 
x_544 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_544, 0, x_539);
x_542 = x_544;
goto block_543;
}
block_543:
{
return x_542;
}
}
}
}
default: 
{
size_t x_547; size_t x_548; uint8_t x_549; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_547 = lean_ptr_addr(x_455);
x_548 = lean_ptr_addr(x_473);
x_549 = lean_usize_dec_eq(x_547, x_548);
if (x_549 == 0)
{
lean_object* x_550; uint8_t x_551; uint8_t x_556; 
lean_inc_ref(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
x_556 = !lean_is_exclusive(x_3);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_557 = lean_ctor_get(x_3, 5);
lean_dec(x_557);
x_558 = lean_ctor_get(x_3, 4);
lean_dec(x_558);
x_559 = lean_ctor_get(x_3, 3);
lean_dec(x_559);
x_560 = lean_ctor_get(x_3, 2);
lean_dec(x_560);
x_561 = lean_ctor_get(x_3, 1);
lean_dec(x_561);
x_562 = lean_ctor_get(x_3, 0);
lean_dec(x_562);
x_550 = x_3;
x_551 = x_556;
goto block_555;
}
else
{
lean_dec(x_3);
x_550 = lean_box(0);
x_551 = x_556;
goto block_555;
}
block_555:
{
lean_object* x_552; 
if (x_551 == 0)
{
lean_ctor_set(x_550, 5, x_473);
x_552 = x_550;
goto block_553;
}
else
{
lean_object* x_554; 
x_554 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_554, 0, x_450);
lean_ctor_set(x_554, 1, x_451);
lean_ctor_set(x_554, 2, x_452);
lean_ctor_set(x_554, 3, x_453);
lean_ctor_set(x_554, 4, x_454);
lean_ctor_set(x_554, 5, x_473);
x_552 = x_554;
goto block_553;
}
block_553:
{
x_480 = x_552;
goto block_487;
}
}
}
else
{
lean_dec(x_473);
x_480 = x_3;
goto block_487;
}
}
}
block_487:
{
lean_object* x_481; 
if (x_475 == 0)
{
lean_ctor_set(x_474, 0, x_480);
x_481 = x_474;
goto block_485;
}
else
{
lean_object* x_486; 
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_480);
lean_ctor_set(x_486, 1, x_471);
x_481 = x_486;
goto block_485;
}
block_485:
{
lean_object* x_482; 
if (x_479 == 0)
{
lean_ctor_set(x_478, 0, x_481);
x_482 = x_478;
goto block_483;
}
else
{
lean_object* x_484; 
x_484 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_484, 0, x_481);
x_482 = x_484;
goto block_483;
}
block_483:
{
return x_482;
}
}
}
block_492:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_box(x_459);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_491, 0, x_490);
return x_491;
}
}
}
else
{
lean_object* x_565; lean_object* x_566; uint8_t x_567; uint8_t x_572; 
lean_del_object(x_474);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_565 = lean_ctor_get(x_476, 0);
x_572 = !lean_is_exclusive(x_476);
if (x_572 == 0)
{
x_566 = x_476;
x_567 = x_572;
goto block_571;
}
else
{
lean_inc(x_565);
lean_dec(x_476);
x_566 = lean_box(0);
x_567 = x_572;
goto block_571;
}
block_571:
{
lean_object* x_568; 
if (x_567 == 0)
{
x_568 = x_566;
goto block_569;
}
else
{
lean_object* x_570; 
x_570 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_570, 0, x_565);
x_568 = x_570;
goto block_569;
}
block_569:
{
return x_568;
}
}
}
}
}
else
{
lean_object* x_576; size_t x_577; size_t x_578; uint8_t x_579; 
lean_dec_ref(x_457);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_576 = lean_ctor_get(x_461, 0);
lean_inc(x_576);
lean_dec(x_461);
x_577 = lean_ptr_addr(x_455);
x_578 = lean_ptr_addr(x_576);
x_579 = lean_usize_dec_eq(x_577, x_578);
if (x_579 == 0)
{
lean_object* x_580; uint8_t x_581; uint8_t x_586; 
lean_inc_ref(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
x_586 = !lean_is_exclusive(x_3);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_587 = lean_ctor_get(x_3, 5);
lean_dec(x_587);
x_588 = lean_ctor_get(x_3, 4);
lean_dec(x_588);
x_589 = lean_ctor_get(x_3, 3);
lean_dec(x_589);
x_590 = lean_ctor_get(x_3, 2);
lean_dec(x_590);
x_591 = lean_ctor_get(x_3, 1);
lean_dec(x_591);
x_592 = lean_ctor_get(x_3, 0);
lean_dec(x_592);
x_580 = x_3;
x_581 = x_586;
goto block_585;
}
else
{
lean_dec(x_3);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
lean_ctor_set(x_580, 5, x_576);
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_584, 0, x_450);
lean_ctor_set(x_584, 1, x_451);
lean_ctor_set(x_584, 2, x_452);
lean_ctor_set(x_584, 3, x_453);
lean_ctor_set(x_584, 4, x_454);
lean_ctor_set(x_584, 5, x_576);
x_582 = x_584;
goto block_583;
}
block_583:
{
x_464 = x_582;
goto block_470;
}
}
}
else
{
lean_dec(x_576);
x_464 = x_3;
goto block_470;
}
}
block_470:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_box(x_459);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
if (x_463 == 0)
{
lean_ctor_set(x_462, 0, x_466);
x_467 = x_462;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_469, 0, x_466);
x_467 = x_469;
goto block_468;
}
block_468:
{
return x_467;
}
}
}
}
else
{
lean_dec_ref(x_457);
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_460;
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec_ref(x_457);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_595 = lean_box(x_459);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_3);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_597, 0, x_596);
return x_597;
}
}
default: 
{
lean_object* x_598; lean_object* x_599; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_598 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
x_599 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(x_598, x_4, x_5, x_6, x_7, x_8);
return x_599;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_23; 
x_11 = lean_ctor_get(x_10, 0);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
x_12 = x_10;
x_13 = x_23;
goto block_22;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_del_object(x_12);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_18);
x_19 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_10, 0);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
x_25 = x_10;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_44; 
x_8 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
x_44 = !lean_is_exclusive(x_9);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_9, 1);
lean_dec(x_45);
x_11 = x_9;
x_12 = x_44;
goto block_43;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_41; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_10, 1);
lean_dec(x_42);
x_17 = x_10;
x_18 = x_41;
goto block_40;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_15);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_14);
if (x_18 == 0)
{
lean_ctor_set(x_17, 4, x_24);
lean_ctor_set(x_17, 3, x_25);
lean_ctor_set(x_17, 2, x_26);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_23);
x_27 = x_17;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_39, 2, x_26);
lean_ctor_set(x_39, 3, x_25);
lean_ctor_set(x_39, 4, x_24);
x_27 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_28; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_27);
x_28 = x_11;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_20);
x_28 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
x_31 = l_instInhabitedOfMonad___redArg(x_29, x_30);
x_32 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_panic_fn(x_33, x_1);
x_35 = lean_apply_6(x_34, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l_Lean_instBEqFVarId_beq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__7___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l_Lean_instBEqFVarId_beq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableFVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableFVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqFVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqFVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableFVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_unsigned_to_nat(278u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
x_10 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_33; 
x_11 = lean_ctor_get(x_10, 0);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
x_12 = x_10;
x_13 = x_33;
goto block_32;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_33;
goto block_32;
}
block_32:
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_9);
x_15 = lean_ptr_addr(x_11);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_26; 
lean_inc_ref(x_8);
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
x_17 = x_1;
x_18 = x_26;
goto block_25;
}
else
{
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_11);
x_19 = x_17;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_11);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_19);
x_20 = x_12;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_1);
x_29 = x_12;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_10;
}
}
case 2:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_34, 2);
x_37 = lean_ctor_get(x_34, 3);
x_38 = lean_ctor_get(x_34, 4);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_38);
x_39 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_38, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = 1;
lean_inc_ref(x_36);
lean_inc_ref(x_37);
lean_inc_ref(x_34);
x_42 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_41, x_34, x_37, x_36, x_40, x_4);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc_ref(x_35);
x_44 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_35, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_72; 
x_45 = lean_ctor_get(x_44, 0);
x_72 = !lean_is_exclusive(x_44);
if (x_72 == 0)
{
x_46 = x_44;
x_47 = x_72;
goto block_71;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_72;
goto block_71;
}
block_71:
{
uint8_t x_48; size_t x_65; size_t x_66; uint8_t x_67; 
x_65 = lean_ptr_addr(x_35);
x_66 = lean_ptr_addr(x_45);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
x_48 = x_67;
goto block_64;
}
else
{
size_t x_68; size_t x_69; uint8_t x_70; 
x_68 = lean_ptr_addr(x_34);
x_69 = lean_ptr_addr(x_43);
x_70 = lean_usize_dec_eq(x_68, x_69);
x_48 = x_70;
goto block_64;
}
block_64:
{
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_1, 0);
lean_dec(x_60);
x_49 = x_1;
x_50 = x_58;
goto block_57;
}
else
{
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_51; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 0, x_43);
x_51 = x_49;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_45);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_51);
x_52 = x_46;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_45);
lean_dec(x_43);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_1);
x_61 = x_46;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
else
{
lean_dec(x_43);
lean_dec_ref(x_1);
return x_44;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec_ref(x_1);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_73 = lean_ctor_get(x_42, 0);
x_80 = !lean_is_exclusive(x_42);
if (x_80 == 0)
{
x_74 = x_42;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_42);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_39;
}
}
case 3:
{
lean_object* x_81; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
case 4:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_138; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_82, 0);
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_ctor_get(x_82, 2);
x_86 = lean_ctor_get(x_82, 3);
x_138 = !lean_is_exclusive(x_82);
if (x_138 == 0)
{
x_87 = x_82;
x_88 = x_138;
goto block_137;
}
else
{
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; uint8_t x_136; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_136 = !lean_is_exclusive(x_2);
if (x_136 == 0)
{
x_91 = x_2;
x_92 = x_136;
goto block_135;
}
else
{
lean_inc(x_89);
lean_dec(x_2);
x_91 = lean_box(0);
x_92 = x_136;
goto block_135;
}
block_135:
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc_ref(x_89);
x_93 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(x_89, x_85);
x_94 = lean_box(0);
lean_inc(x_85);
x_95 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(x_89, x_85, x_94);
if (x_92 == 0)
{
lean_ctor_set(x_91, 0, x_95);
x_96 = x_91;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_134, 0, x_95);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_90);
x_96 = x_134;
goto block_133;
}
block_133:
{
size_t x_97; size_t x_98; lean_object* x_99; 
x_97 = lean_array_size(x_86);
x_98 = 0;
lean_inc_ref(x_86);
lean_inc(x_85);
x_99 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(x_85, x_93, x_97, x_98, x_86, x_96, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_124; 
x_100 = lean_ctor_get(x_99, 0);
x_124 = !lean_is_exclusive(x_99);
if (x_124 == 0)
{
x_101 = x_99;
x_102 = x_124;
goto block_123;
}
else
{
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_box(0);
x_102 = x_124;
goto block_123;
}
block_123:
{
size_t x_103; size_t x_104; uint8_t x_105; 
x_103 = lean_ptr_addr(x_86);
lean_dec_ref(x_86);
x_104 = lean_ptr_addr(x_100);
x_105 = lean_usize_dec_eq(x_103, x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; uint8_t x_118; 
x_118 = !lean_is_exclusive(x_1);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_1, 0);
lean_dec(x_119);
x_106 = x_1;
x_107 = x_118;
goto block_117;
}
else
{
lean_dec(x_1);
x_106 = lean_box(0);
x_107 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_108; 
if (x_88 == 0)
{
lean_ctor_set(x_87, 3, x_100);
x_108 = x_87;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_116, 0, x_83);
lean_ctor_set(x_116, 1, x_84);
lean_ctor_set(x_116, 2, x_85);
lean_ctor_set(x_116, 3, x_100);
x_108 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_109; 
if (x_107 == 0)
{
lean_ctor_set(x_106, 0, x_108);
x_109 = x_106;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_114, 0, x_108);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_102 == 0)
{
lean_ctor_set(x_101, 0, x_109);
x_110 = x_101;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_109);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_100);
lean_del_object(x_87);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
if (x_102 == 0)
{
lean_ctor_set(x_101, 0, x_1);
x_120 = x_101;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_1);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_del_object(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_99, 0);
x_132 = !lean_is_exclusive(x_99);
if (x_132 == 0)
{
x_126 = x_99;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_99);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
}
}
}
case 5:
{
lean_object* x_139; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_1);
return x_139;
}
case 6:
{
lean_object* x_140; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_1);
return x_140;
}
case 8:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_1, 0);
x_142 = lean_ctor_get(x_1, 1);
x_143 = lean_ctor_get(x_1, 2);
x_144 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_144);
x_145 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_144, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_170; 
x_146 = lean_ctor_get(x_145, 0);
x_170 = !lean_is_exclusive(x_145);
if (x_170 == 0)
{
x_147 = x_145;
x_148 = x_170;
goto block_169;
}
else
{
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_box(0);
x_148 = x_170;
goto block_169;
}
block_169:
{
size_t x_149; size_t x_150; uint8_t x_151; 
x_149 = lean_ptr_addr(x_144);
x_150 = lean_ptr_addr(x_146);
x_151 = lean_usize_dec_eq(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; uint8_t x_161; 
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
x_161 = !lean_is_exclusive(x_1);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_1, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_1, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_1, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_1, 0);
lean_dec(x_165);
x_152 = x_1;
x_153 = x_161;
goto block_160;
}
else
{
lean_dec(x_1);
x_152 = lean_box(0);
x_153 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_154; 
if (x_153 == 0)
{
lean_ctor_set(x_152, 3, x_146);
x_154 = x_152;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_159, 0, x_141);
lean_ctor_set(x_159, 1, x_142);
lean_ctor_set(x_159, 2, x_143);
lean_ctor_set(x_159, 3, x_146);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_154);
x_155 = x_147;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_154);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_146);
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_1);
x_166 = x_147;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_1);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_145;
}
}
case 9:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_1, 0);
x_172 = lean_ctor_get(x_1, 1);
x_173 = lean_ctor_get(x_1, 2);
x_174 = lean_ctor_get(x_1, 3);
x_175 = lean_ctor_get(x_1, 4);
x_176 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_176);
x_177 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_176, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_204; 
x_178 = lean_ctor_get(x_177, 0);
x_204 = !lean_is_exclusive(x_177);
if (x_204 == 0)
{
x_179 = x_177;
x_180 = x_204;
goto block_203;
}
else
{
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_box(0);
x_180 = x_204;
goto block_203;
}
block_203:
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_176);
x_182 = lean_ptr_addr(x_178);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; uint8_t x_193; 
lean_inc_ref(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
x_193 = !lean_is_exclusive(x_1);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_1, 5);
lean_dec(x_194);
x_195 = lean_ctor_get(x_1, 4);
lean_dec(x_195);
x_196 = lean_ctor_get(x_1, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_1, 2);
lean_dec(x_197);
x_198 = lean_ctor_get(x_1, 1);
lean_dec(x_198);
x_199 = lean_ctor_get(x_1, 0);
lean_dec(x_199);
x_184 = x_1;
x_185 = x_193;
goto block_192;
}
else
{
lean_dec(x_1);
x_184 = lean_box(0);
x_185 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_186; 
if (x_185 == 0)
{
lean_ctor_set(x_184, 5, x_178);
x_186 = x_184;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_191, 0, x_171);
lean_ctor_set(x_191, 1, x_172);
lean_ctor_set(x_191, 2, x_173);
lean_ctor_set(x_191, 3, x_174);
lean_ctor_set(x_191, 4, x_175);
lean_ctor_set(x_191, 5, x_178);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_180 == 0)
{
lean_ctor_set(x_179, 0, x_186);
x_187 = x_179;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_186);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
else
{
lean_object* x_200; 
lean_dec(x_178);
if (x_180 == 0)
{
lean_ctor_set(x_179, 0, x_1);
x_200 = x_179;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_1);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_177;
}
}
default: 
{
lean_object* x_205; lean_object* x_206; 
lean_dec_ref(x_1);
x_205 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
x_206 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(x_205, x_2, x_3, x_4, x_5, x_6);
return x_206;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_35; 
x_14 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
x_15 = lean_array_uget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_5, x_4, x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_35 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(x_15, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_52; 
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_52 = l_Lean_Compiler_LCNF_CtorInfo_isScalar(x_37);
if (x_52 == 0)
{
x_39 = x_2;
goto block_51;
}
else
{
x_39 = x_52;
goto block_51;
}
block_51:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_35);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc(x_1);
x_40 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(x_1, x_37, x_38, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_36, x_41);
x_18 = x_42;
goto block_23;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_36);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 0);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
x_44 = x_40;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_dec_ref(x_36);
x_24 = x_35;
goto block_34;
}
}
}
else
{
lean_dec_ref(x_36);
x_24 = x_35;
goto block_34;
}
}
else
{
x_24 = x_35;
goto block_34;
}
block_23:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_17, x_4, x_18);
x_4 = x_20;
x_5 = x_21;
goto _start;
}
block_34:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_18 = x_25;
goto block_23;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_26 = lean_ctor_get(x_24, 0);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
x_27 = x_24;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__7___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_72; 
x_8 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
x_72 = !lean_is_exclusive(x_9);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_9, 1);
lean_dec(x_73);
x_11 = x_9;
x_12 = x_72;
goto block_71;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_69; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_69 = !lean_is_exclusive(x_10);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_10, 1);
lean_dec(x_70);
x_17 = x_10;
x_18 = x_69;
goto block_68;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_15);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_14);
if (x_18 == 0)
{
lean_ctor_set(x_17, 4, x_24);
lean_ctor_set(x_17, 3, x_25);
lean_ctor_set(x_17, 2, x_26);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_23);
x_27 = x_17;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_23);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_26);
lean_ctor_set(x_67, 3, x_25);
lean_ctor_set(x_67, 4, x_24);
x_27 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_28; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_27);
x_28 = x_11;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_27);
lean_ctor_set(x_65, 1, x_20);
x_28 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_62; 
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = lean_ctor_get(x_29, 0);
x_62 = !lean_is_exclusive(x_29);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_29, 1);
lean_dec(x_63);
x_31 = x_29;
x_32 = x_62;
goto block_61;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_59; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_59 = !lean_is_exclusive(x_30);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_30, 1);
lean_dec(x_60);
x_37 = x_30;
x_38 = x_59;
goto block_58;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
x_40 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_35);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_34);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_44);
lean_ctor_set(x_37, 3, x_45);
lean_ctor_set(x_37, 2, x_46);
lean_ctor_set(x_37, 1, x_39);
lean_ctor_set(x_37, 0, x_43);
x_47 = x_37;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_46);
lean_ctor_set(x_57, 3, x_45);
lean_ctor_set(x_57, 4, x_44);
x_47 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_48; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_40);
lean_ctor_set(x_31, 0, x_47);
x_48 = x_31;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_40);
x_48 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = lean_box(0);
x_51 = l_instInhabitedOfMonad___redArg(x_49, x_50);
x_52 = lean_panic_fn(x_51, x_1);
x_53 = lean_apply_6(x_52, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_53;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(301u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_8, 3);
if (lean_obj_tag(x_9) == 11)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_2);
x_13 = lean_box(0);
x_14 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(x_12, x_11, x_13);
x_15 = lean_st_ref_set(x_2, x_14);
x_1 = x_10;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_1 = x_17;
goto _start;
}
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_21);
lean_dec_ref(x_19);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_22 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(x_21, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_1 = x_20;
goto _start;
}
else
{
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_22;
}
}
case 3:
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_1);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 4:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_48; 
x_26 = lean_ctor_get(x_1, 0);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_27 = x_1;
x_28 = x_48;
goto block_47;
}
else
{
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_26, 3);
lean_inc_ref(x_29);
lean_dec_ref(x_26);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = lean_box(0);
x_33 = lean_nat_dec_lt(x_30, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_29);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_32);
x_34 = x_27;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_31, x_31);
if (x_37 == 0)
{
if (x_33 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_29);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_32);
x_38 = x_27;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_32);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
lean_del_object(x_27);
x_41 = 0;
x_42 = lean_usize_of_nat(x_31);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(x_29, x_41, x_42, x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_29);
return x_43;
}
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
lean_del_object(x_27);
x_44 = 0;
x_45 = lean_usize_of_nat(x_31);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(x_29, x_44, x_45, x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_29);
return x_46;
}
}
}
}
case 5:
{
lean_object* x_49; uint8_t x_50; uint8_t x_56; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_1);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_1, 0);
lean_dec(x_57);
x_49 = x_1;
x_50 = x_56;
goto block_55;
}
else
{
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
if (x_50 == 0)
{
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_51);
x_52 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
case 6:
{
lean_object* x_58; uint8_t x_59; uint8_t x_65; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_1, 0);
lean_dec(x_66);
x_58 = x_1;
x_59 = x_65;
goto block_64;
}
else
{
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_box(0);
if (x_59 == 0)
{
lean_ctor_set_tag(x_58, 0);
lean_ctor_set(x_58, 0, x_60);
x_61 = x_58;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
case 8:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_67);
lean_dec_ref(x_1);
x_1 = x_67;
goto _start;
}
case 9:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_69);
lean_dec_ref(x_1);
x_1 = x_69;
goto _start;
}
default: 
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_1);
x_71 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
x_72 = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(x_71, x_2, x_3, x_4, x_5, x_6);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_uget_borrowed(x_1, x_2);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_20);
x_11 = x_20;
goto block_17;
}
case 1:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_11 = x_21;
goto block_17;
}
default: 
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_22);
x_11 = x_22;
goto block_17;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_4);
return x_23;
}
block_17:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_33; 
x_9 = lean_ctor_get(x_2, 0);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
x_10 = x_2;
x_11 = x_33;
goto block_32;
}
else
{
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_12; 
x_12 = lean_apply_7(x_1, x_9, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
x_14 = x_12;
x_15 = x_23;
goto block_22;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_16; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_16 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_del_object(x_10);
x_24 = lean_ctor_get(x_12, 0);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
x_25 = x_12;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
x_8 = x_18;
x_9 = x_17;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
x_20 = lean_st_mk_ref(x_19);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_20);
lean_inc_ref(x_1);
x_21 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(x_1, x_20, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
x_22 = lean_st_ref_get(x_20);
lean_dec(x_20);
x_8 = x_22;
x_9 = x_17;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_24 = x_21;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_9);
x_15 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(x_1, x_14, x_10, x_11, x_12, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_36; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_11 = lean_ctor_get(x_1, 2);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
x_12 = x_1;
x_13 = x_36;
goto block_35;
}
else
{
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
x_15 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(x_14, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
x_17 = x_15;
x_18 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_16);
x_19 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_11);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_10);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
x_27 = lean_ctor_get(x_15, 0);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_28 = x_15;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_getConfig___redArg(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_22; 
x_8 = lean_ctor_get(x_7, 0);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
x_9 = x_7;
x_10 = x_22;
goto block_21;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*4 + 2);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_1);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_del_object(x_9);
x_15 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
x_16 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___closed__0);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(x_1, x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_11);
x_20 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(x_18, x_19, x_2, x_3, x_4, x_5);
return x_20;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_17;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_7, 0);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
x_24 = x_7;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
x_3 = 2;
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2506150707u);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
x_3 = 1;
x_4 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_insertResetReuse = _init_l_Lean_Compiler_LCNF_insertResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_insertResetReuse);
res = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LiveVars(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ResetReuse(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
