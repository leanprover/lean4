// Lean compiler output
// Module: Lean.Compiler.LCNF.ResetReuse
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.LiveVars import Lean.Compiler.LCNF.DependsOn import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.PropagateBorrow
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_applyOwnedness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Compiler_LCNF_instBEqOwnedness_beq(uint8_t, uint8_t);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateContImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.S.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Compiler.LCNF.ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.D.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Code.insertResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Decl.insertResetReuseCore.collectResets"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "resetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 201, 93, 114, 179, 16, 247, 72)}};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_insertResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 22, 75, 214, 119, 69, 48, 225)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object* v_c_u2081_1_, lean_object* v_c_u2082_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_name_5_; lean_object* v_size_6_; lean_object* v_usize_7_; lean_object* v_ssize_8_; lean_object* v_name_9_; lean_object* v_size_10_; lean_object* v_usize_11_; lean_object* v_ssize_12_; uint8_t v___x_13_; 
v_name_5_ = lean_ctor_get(v_c_u2081_1_, 0);
v_size_6_ = lean_ctor_get(v_c_u2081_1_, 2);
v_usize_7_ = lean_ctor_get(v_c_u2081_1_, 3);
v_ssize_8_ = lean_ctor_get(v_c_u2081_1_, 4);
v_name_9_ = lean_ctor_get(v_c_u2082_2_, 0);
v_size_10_ = lean_ctor_get(v_c_u2082_2_, 2);
v_usize_11_ = lean_ctor_get(v_c_u2082_2_, 3);
v_ssize_12_ = lean_ctor_get(v_c_u2082_2_, 4);
v___x_13_ = lean_nat_dec_eq(v_size_6_, v_size_10_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_eq(v_usize_7_, v_usize_11_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_box(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_eq(v_ssize_8_, v_ssize_12_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
else
{
uint8_t v_relaxedReuse_22_; 
v_relaxedReuse_22_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*2);
if (v_relaxedReuse_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = l_Lean_Name_getPrefix(v_name_5_);
v___x_24_ = l_Lean_Name_getPrefix(v_name_9_);
v___x_25_ = lean_name_eq(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_box(v_relaxedReuse_22_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object* v_c_u2081_30_, lean_object* v_c_u2082_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_30_, v_c_u2082_31_, v_a_32_);
lean_dec_ref(v_a_32_);
lean_dec_ref(v_c_u2082_31_);
lean_dec_ref(v_c_u2081_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object* v_c_u2081_35_, lean_object* v_c_u2082_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_35_, v_c_u2082_36_, v_a_37_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object* v_c_u2081_44_, lean_object* v_c_u2082_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(v_c_u2081_44_, v_c_u2082_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec_ref(v_c_u2082_45_);
lean_dec_ref(v_c_u2081_44_);
return v_res_52_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object* v_msg_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_56_ = lean_panic_fn_borrowed(v___x_55_, v_msg_54_);
return v___x_56_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_instMonadEIO___redArg();
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object* v_msg_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toApplicative_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_106_; 
v___x_67_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_68_ = l_StateRefT_x27_instMonad___redArg(v___x_67_);
v_toApplicative_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_68_, 1);
lean_dec(v_unused_107_);
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_106_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_toApplicative_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_106_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_toFunctor_73_; lean_object* v_toSeq_74_; lean_object* v_toSeqLeft_75_; lean_object* v_toSeqRight_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_104_; 
v_toFunctor_73_ = lean_ctor_get(v_toApplicative_69_, 0);
v_toSeq_74_ = lean_ctor_get(v_toApplicative_69_, 2);
v_toSeqLeft_75_ = lean_ctor_get(v_toApplicative_69_, 3);
v_toSeqRight_76_ = lean_ctor_get(v_toApplicative_69_, 4);
v_isSharedCheck_104_ = !lean_is_exclusive(v_toApplicative_69_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_dec(v_unused_105_);
v___x_78_ = v_toApplicative_69_;
v_isShared_79_ = v_isSharedCheck_104_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_toSeqRight_76_);
lean_inc(v_toSeqLeft_75_);
lean_inc(v_toSeq_74_);
lean_inc(v_toFunctor_73_);
lean_dec(v_toApplicative_69_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_104_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_89_; 
v___f_80_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_81_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_73_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_73_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_73_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___f_82_);
lean_ctor_set(v___x_84_, 1, v___f_83_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toSeqRight_76_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeqLeft_75_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeq_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 4, v___f_85_);
lean_ctor_set(v___x_78_, 3, v___f_86_);
lean_ctor_set(v___x_78_, 2, v___f_87_);
lean_ctor_set(v___x_78_, 1, v___f_80_);
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_89_ = v___x_78_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___f_80_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v___f_85_);
v___x_89_ = v_reuseFailAlloc_103_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___f_81_);
lean_ctor_set(v___x_71_, 0, v___x_89_);
v___x_91_ = v___x_71_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___f_81_);
v___x_91_ = v_reuseFailAlloc_102_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_3636__overap_100_; lean_object* v___x_101_; 
v___x_92_ = l_StateRefT_x27_instMonad___redArg(v___x_91_);
v___x_93_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_94_ = 0;
v___x_95_ = lean_box(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_93_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = l_instInhabitedOfMonad___redArg(v___x_92_, v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_98_, 0, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_99_, 0, v___f_98_);
v___x_3636__overap_100_ = lean_panic_fn_borrowed(v___f_99_, v_msg_60_);
lean_dec_ref(v___f_99_);
lean_inc(v___y_65_);
lean_inc_ref(v___y_64_);
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc_ref(v___y_61_);
v___x_101_ = lean_apply_6(v___x_3636__overap_100_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, lean_box(0));
return v___x_101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
v___x_121_ = lean_unbox(v___x_120_);
if (v___x_121_ == 0)
{
size_t v___x_122_; size_t v___x_123_; 
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_add(v_i_117_, v___x_122_);
v_i_117_ = v___x_123_;
goto _start;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_unbox(v___x_120_);
return v___x_125_;
}
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object* v_as_127_, lean_object* v_i_128_, lean_object* v_stop_129_){
_start:
{
size_t v_i_boxed_130_; size_t v_stop_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_i_boxed_130_ = lean_unbox_usize(v_i_128_);
lean_dec(v_i_128_);
v_stop_boxed_131_ = lean_unbox_usize(v_stop_129_);
lean_dec(v_stop_129_);
v_res_132_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_127_, v_i_boxed_130_, v_stop_boxed_131_);
lean_dec_ref(v_as_127_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_138_ = lean_unsigned_to_nat(9u);
v___x_139_ = lean_unsigned_to_nat(642u);
v___x_140_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1));
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0));
v___x_142_ = l_mkPanicMessageWithDecl(v___x_141_, v___x_140_, v___x_139_, v___x_138_, v___x_137_);
return v___x_142_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_146_ = lean_unsigned_to_nat(61u);
v___x_147_ = lean_unsigned_to_nat(125u);
v___x_148_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5));
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_150_ = l_mkPanicMessageWithDecl(v___x_149_, v___x_148_, v___x_147_, v___x_146_, v___x_145_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object* v_info_151_, lean_object* v_w_152_, lean_object* v_c_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___y_161_; lean_object* v___y_162_; lean_object* v_k_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; 
switch(lean_obj_tag(v_c_153_))
{
case 0:
{
lean_object* v_decl_387_; lean_object* v_value_388_; 
v_decl_387_ = lean_ctor_get(v_c_153_, 0);
lean_inc_ref(v_decl_387_);
v_value_388_ = lean_ctor_get(v_decl_387_, 3);
lean_inc(v_value_388_);
if (lean_obj_tag(v_value_388_) == 5)
{
lean_object* v_k_389_; lean_object* v_fvarId_390_; lean_object* v_binderName_391_; lean_object* v_type_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_447_; 
v_k_389_ = lean_ctor_get(v_c_153_, 1);
v_fvarId_390_ = lean_ctor_get(v_decl_387_, 0);
v_binderName_391_ = lean_ctor_get(v_decl_387_, 1);
v_type_392_ = lean_ctor_get(v_decl_387_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_decl_387_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_decl_387_, 3);
lean_dec(v_unused_448_);
v___x_394_ = v_decl_387_;
v_isShared_395_ = v_isSharedCheck_447_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_type_392_);
lean_inc(v_binderName_391_);
lean_inc(v_fvarId_390_);
lean_dec(v_decl_387_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_447_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_i_396_; lean_object* v_args_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_446_; 
v_i_396_ = lean_ctor_get(v_value_388_, 0);
v_args_397_ = lean_ctor_get(v_value_388_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_value_388_);
if (v_isSharedCheck_446_ == 0)
{
v___x_399_ = v_value_388_;
v_isShared_400_ = v_isSharedCheck_446_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_args_397_);
lean_inc(v_i_396_);
lean_dec(v_value_388_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_446_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; lean_object* v___x_403_; 
v___x_401_ = 1;
lean_inc_ref(v_args_397_);
lean_inc_ref(v_i_396_);
if (v_isShared_400_ == 0)
{
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_i_396_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_args_397_);
v___x_403_ = v_reuseFailAlloc_445_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
lean_inc_ref(v_type_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 3, v___x_403_);
v___x_405_ = v___x_394_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fvarId_390_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_binderName_391_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_type_392_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v___x_403_);
v___x_405_ = v_reuseFailAlloc_444_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_info_151_, v_i_396_, v_a_154_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; uint8_t v___y_409_; uint8_t v___x_430_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_430_ = lean_unbox(v_a_407_);
if (v___x_430_ == 0)
{
lean_dec(v_a_407_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v_args_397_);
lean_dec_ref(v_i_396_);
lean_dec_ref(v_type_392_);
lean_inc_ref(v_k_389_);
v_k_167_ = v_k_389_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
else
{
lean_object* v_cidx_431_; lean_object* v_cidx_432_; uint8_t v___x_433_; 
lean_inc_ref(v_k_389_);
lean_dec_ref_known(v_c_153_, 2);
v_cidx_431_ = lean_ctor_get(v_info_151_, 1);
v_cidx_432_ = lean_ctor_get(v_i_396_, 1);
v___x_433_ = lean_nat_dec_eq(v_cidx_431_, v_cidx_432_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = lean_unbox(v_a_407_);
v___y_409_ = v___x_434_;
goto v___jp_408_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = 0;
v___y_409_ = v___x_435_;
goto v___jp_408_;
}
}
v___jp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(v___x_410_, 0, v_w_152_);
lean_ctor_set(v___x_410_, 1, v_i_396_);
lean_ctor_set(v___x_410_, 2, v_args_397_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3, v___y_409_);
v___x_411_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_401_, v___x_405_, v_type_392_, v___x_410_, v_a_156_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_a_412_);
lean_ctor_set(v___x_416_, 1, v_k_389_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v_a_407_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_407_);
lean_dec_ref(v_k_389_);
v_a_422_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v___x_405_);
lean_dec_ref(v_args_397_);
lean_dec_ref(v_i_396_);
lean_dec_ref(v_type_392_);
lean_dec_ref_known(v_c_153_, 2);
lean_dec(v_w_152_);
v_a_436_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_406_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_406_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
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
lean_object* v_k_449_; 
lean_dec(v_value_388_);
lean_dec_ref(v_decl_387_);
v_k_449_ = lean_ctor_get(v_c_153_, 1);
lean_inc_ref(v_k_449_);
v_k_167_ = v_k_449_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
}
case 2:
{
lean_object* v_decl_450_; lean_object* v_k_451_; lean_object* v_params_452_; lean_object* v_type_453_; lean_object* v_value_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v_decl_450_ = lean_ctor_get(v_c_153_, 0);
v_k_451_ = lean_ctor_get(v_c_153_, 1);
v_params_452_ = lean_ctor_get(v_decl_450_, 2);
v_type_453_ = lean_ctor_get(v_decl_450_, 3);
v_value_454_ = lean_ctor_get(v_decl_450_, 4);
v___x_455_ = 1;
lean_inc_ref(v_value_454_);
lean_inc(v_w_152_);
v___x_456_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_151_, v_w_152_, v_value_454_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_snd_458_; uint8_t v___x_459_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v_snd_458_ = lean_ctor_get(v_a_457_, 1);
lean_inc(v_snd_458_);
v___x_459_ = lean_unbox(v_snd_458_);
if (v___x_459_ == 0)
{
lean_dec(v_snd_458_);
lean_dec(v_a_457_);
lean_inc_ref(v_k_451_);
v_k_167_ = v_k_451_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
else
{
lean_object* v_fst_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_w_152_);
v_fst_460_ = lean_ctor_get(v_a_457_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_457_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_a_457_, 1);
lean_dec(v_unused_510_);
v___x_462_ = v_a_457_;
v_isShared_463_ = v_isSharedCheck_509_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_fst_460_);
lean_dec(v_a_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_509_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; 
lean_inc_ref(v_params_452_);
lean_inc_ref(v_type_453_);
lean_inc_ref(v_decl_450_);
v___x_464_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_455_, v_decl_450_, v_type_453_, v_params_452_, v_fst_460_, v_a_156_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_500_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_500_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_500_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_500_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___y_470_; size_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_ptr_addr(v_k_451_);
v___x_478_ = lean_usize_dec_eq(v___x_477_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_inc_ref(v_k_451_);
v_isSharedCheck_485_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; 
v_unused_486_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_487_);
v___x_480_ = v_c_153_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_c_153_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_a_465_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_451_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
v___y_470_ = v___x_483_;
goto v___jp_469_;
}
}
}
else
{
size_t v___x_488_; size_t v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_ptr_addr(v_decl_450_);
v___x_489_ = lean_ptr_addr(v_a_465_);
v___x_490_ = lean_usize_dec_eq(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_inc_ref(v_k_451_);
v_isSharedCheck_497_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_499_);
v___x_492_ = v_c_153_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_dec(v_c_153_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_a_465_);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_451_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
v___y_470_ = v___x_495_;
goto v___jp_469_;
}
}
}
else
{
lean_dec(v_a_465_);
v___y_470_ = v_c_153_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___y_470_);
v___x_472_ = v___x_462_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___y_470_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_458_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_472_);
v___x_474_ = v___x_467_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_462_);
lean_dec(v_snd_458_);
lean_dec_ref_known(v_c_153_, 2);
v_a_501_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_464_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_464_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_c_153_, 2);
lean_dec(v_w_152_);
return v___x_456_;
}
}
case 3:
{
uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_w_152_);
v___x_511_ = 0;
v___x_512_ = lean_box(v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_c_153_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
case 4:
{
lean_object* v_cases_515_; lean_object* v_typeName_516_; lean_object* v_resultType_517_; lean_object* v_discr_518_; lean_object* v_alts_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_571_; 
v_cases_515_ = lean_ctor_get(v_c_153_, 0);
lean_inc_ref(v_cases_515_);
v_typeName_516_ = lean_ctor_get(v_cases_515_, 0);
v_resultType_517_ = lean_ctor_get(v_cases_515_, 1);
v_discr_518_ = lean_ctor_get(v_cases_515_, 2);
v_alts_519_ = lean_ctor_get(v_cases_515_, 3);
v_isSharedCheck_571_ = !lean_is_exclusive(v_cases_515_);
if (v_isSharedCheck_571_ == 0)
{
v___x_521_ = v_cases_515_;
v_isShared_522_ = v_isSharedCheck_571_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_alts_519_);
lean_inc(v_discr_518_);
lean_inc(v_resultType_517_);
lean_inc(v_typeName_516_);
lean_dec(v_cases_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_571_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; 
v_sz_523_ = lean_array_size(v_alts_519_);
v___x_524_ = ((size_t)0ULL);
lean_inc_ref(v_alts_519_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_151_, v_w_152_, v_sz_523_, v___x_524_, v_alts_519_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_562_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_562_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_562_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_562_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___x_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___y_542_; size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_538_ = l_Array_unzip___redArg(v_a_526_);
lean_dec(v_a_526_);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v___x_538_);
v___x_548_ = lean_ptr_addr(v_alts_519_);
lean_dec_ref(v_alts_519_);
v___x_549_ = lean_ptr_addr(v_fst_539_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
v_isSharedCheck_560_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_561_);
v___x_552_ = v_c_153_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_c_153_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 3, v_fst_539_);
v___x_555_ = v___x_521_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_typeName_516_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_resultType_517_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_discr_518_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_fst_539_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v___y_542_ = v___x_557_;
goto v___jp_541_;
}
}
}
}
else
{
lean_dec(v_fst_539_);
lean_del_object(v___x_521_);
lean_dec(v_discr_518_);
lean_dec_ref(v_resultType_517_);
lean_dec(v_typeName_516_);
v___y_542_ = v_c_153_;
goto v___jp_541_;
}
v___jp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = lean_box(v___y_532_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_534_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v_snd_540_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v_snd_540_);
v___y_531_ = v___y_542_;
v___y_532_ = v___x_545_;
goto v___jp_530_;
}
else
{
if (v___x_545_ == 0)
{
lean_dec(v_snd_540_);
v___y_531_ = v___y_542_;
v___y_532_ = v___x_545_;
goto v___jp_530_;
}
else
{
size_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_usize_of_nat(v___x_544_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_540_, v___x_524_, v___x_546_);
lean_dec(v_snd_540_);
v___y_531_ = v___y_542_;
v___y_532_ = v___x_547_;
goto v___jp_530_;
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_521_);
lean_dec_ref(v_alts_519_);
lean_dec(v_discr_518_);
lean_dec_ref(v_resultType_517_);
lean_dec(v_typeName_516_);
lean_dec_ref_known(v_c_153_, 1);
v_a_563_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_525_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_525_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
case 5:
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_w_152_);
v___x_572_ = 0;
v___x_573_ = lean_box(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_c_153_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
case 6:
{
uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_w_152_);
v___x_576_ = 0;
v___x_577_ = lean_box(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_c_153_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
case 8:
{
lean_object* v_k_580_; 
v_k_580_ = lean_ctor_get(v_c_153_, 3);
lean_inc_ref(v_k_580_);
v_k_167_ = v_k_580_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
case 9:
{
lean_object* v_k_581_; 
v_k_581_ = lean_ctor_get(v_c_153_, 5);
lean_inc_ref(v_k_581_);
v_k_167_ = v_k_581_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
default: 
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v_c_153_);
lean_dec(v_w_152_);
v___x_582_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
v___x_583_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_582_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_583_;
}
}
v___jp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(v___y_161_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___y_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
v___jp_166_:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_151_, v_w_152_, v_k_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
switch(lean_obj_tag(v_c_153_))
{
case 0:
{
lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v_decl_177_; lean_object* v_k_178_; size_t v___x_179_; size_t v___x_180_; uint8_t v___x_181_; 
v_fst_175_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_175_);
v_snd_176_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_176_);
lean_dec(v_a_174_);
v_decl_177_ = lean_ctor_get(v_c_153_, 0);
v_k_178_ = lean_ctor_get(v_c_153_, 1);
v___x_179_ = lean_ptr_addr(v_k_178_);
v___x_180_ = lean_ptr_addr(v_fst_175_);
v___x_181_ = lean_usize_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
lean_inc_ref(v_decl_177_);
v_isSharedCheck_189_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_190_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_191_);
v___x_183_ = v_c_153_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_c_153_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_fst_175_);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_decl_177_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_fst_175_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_unbox(v_snd_176_);
lean_dec(v_snd_176_);
v___y_161_ = v___x_187_;
v___y_162_ = v___x_186_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_192_; 
lean_dec(v_fst_175_);
v___x_192_ = lean_unbox(v_snd_176_);
lean_dec(v_snd_176_);
v___y_161_ = v___x_192_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 1:
{
lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v_decl_195_; lean_object* v_k_196_; size_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; 
v_fst_193_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_193_);
v_snd_194_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_194_);
lean_dec(v_a_174_);
v_decl_195_ = lean_ctor_get(v_c_153_, 0);
v_k_196_ = lean_ctor_get(v_c_153_, 1);
v___x_197_ = lean_ptr_addr(v_k_196_);
v___x_198_ = lean_ptr_addr(v_fst_193_);
v___x_199_ = lean_usize_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_decl_195_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_208_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_209_);
v___x_201_ = v_c_153_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_c_153_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 1, v_fst_193_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_decl_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_fst_193_);
v___x_204_ = v_reuseFailAlloc_206_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
uint8_t v___x_205_; 
v___x_205_ = lean_unbox(v_snd_194_);
lean_dec(v_snd_194_);
v___y_161_ = v___x_205_;
v___y_162_ = v___x_204_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_210_; 
lean_dec(v_fst_193_);
v___x_210_ = lean_unbox(v_snd_194_);
lean_dec(v_snd_194_);
v___y_161_ = v___x_210_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 2:
{
lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v_decl_213_; lean_object* v_k_214_; size_t v___x_215_; size_t v___x_216_; uint8_t v___x_217_; 
v_fst_211_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_211_);
v_snd_212_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_212_);
lean_dec(v_a_174_);
v_decl_213_ = lean_ctor_get(v_c_153_, 0);
v_k_214_ = lean_ctor_get(v_c_153_, 1);
v___x_215_ = lean_ptr_addr(v_k_214_);
v___x_216_ = lean_ptr_addr(v_fst_211_);
v___x_217_ = lean_usize_dec_eq(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
lean_inc_ref(v_decl_213_);
v_isSharedCheck_225_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_226_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_227_);
v___x_219_ = v_c_153_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_c_153_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v_fst_211_);
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_decl_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_fst_211_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
uint8_t v___x_223_; 
v___x_223_ = lean_unbox(v_snd_212_);
lean_dec(v_snd_212_);
v___y_161_ = v___x_223_;
v___y_162_ = v___x_222_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_228_; 
lean_dec(v_fst_211_);
v___x_228_ = lean_unbox(v_snd_212_);
lean_dec(v_snd_212_);
v___y_161_ = v___x_228_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 7:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v_fvarId_231_; lean_object* v_i_232_; lean_object* v_y_233_; lean_object* v_k_234_; size_t v___x_235_; size_t v___x_236_; uint8_t v___x_237_; 
v_fst_229_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_229_);
v_snd_230_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_230_);
lean_dec(v_a_174_);
v_fvarId_231_ = lean_ctor_get(v_c_153_, 0);
v_i_232_ = lean_ctor_get(v_c_153_, 1);
v_y_233_ = lean_ctor_get(v_c_153_, 2);
v_k_234_ = lean_ctor_get(v_c_153_, 3);
v___x_235_ = lean_ptr_addr(v_k_234_);
v___x_236_ = lean_ptr_addr(v_fst_229_);
v___x_237_ = lean_usize_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
lean_inc(v_y_233_);
lean_inc(v_i_232_);
lean_inc(v_fvarId_231_);
v_isSharedCheck_245_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_246_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_249_);
v___x_239_ = v_c_153_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_c_153_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 3, v_fst_229_);
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fvarId_231_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_i_232_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_y_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_fst_229_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_snd_230_);
lean_dec(v_snd_230_);
v___y_161_ = v___x_243_;
v___y_162_ = v___x_242_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_250_; 
lean_dec(v_fst_229_);
v___x_250_ = lean_unbox(v_snd_230_);
lean_dec(v_snd_230_);
v___y_161_ = v___x_250_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 9:
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v_fvarId_253_; lean_object* v_i_254_; lean_object* v_offset_255_; lean_object* v_y_256_; lean_object* v_ty_257_; lean_object* v_k_258_; size_t v___x_259_; size_t v___x_260_; uint8_t v___x_261_; 
v_fst_251_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_251_);
v_snd_252_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_252_);
lean_dec(v_a_174_);
v_fvarId_253_ = lean_ctor_get(v_c_153_, 0);
v_i_254_ = lean_ctor_get(v_c_153_, 1);
v_offset_255_ = lean_ctor_get(v_c_153_, 2);
v_y_256_ = lean_ctor_get(v_c_153_, 3);
v_ty_257_ = lean_ctor_get(v_c_153_, 4);
v_k_258_ = lean_ctor_get(v_c_153_, 5);
v___x_259_ = lean_ptr_addr(v_k_258_);
v___x_260_ = lean_ptr_addr(v_fst_251_);
v___x_261_ = lean_usize_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
lean_inc_ref(v_ty_257_);
lean_inc(v_y_256_);
lean_inc(v_offset_255_);
lean_inc(v_i_254_);
lean_inc(v_fvarId_253_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_270_ = lean_ctor_get(v_c_153_, 5);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_c_153_, 4);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_275_);
v___x_263_ = v_c_153_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_c_153_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 5, v_fst_251_);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fvarId_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_i_254_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_offset_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_y_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_ty_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 5, v_fst_251_);
v___x_266_ = v_reuseFailAlloc_268_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
uint8_t v___x_267_; 
v___x_267_ = lean_unbox(v_snd_252_);
lean_dec(v_snd_252_);
v___y_161_ = v___x_267_;
v___y_162_ = v___x_266_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_276_; 
lean_dec(v_fst_251_);
v___x_276_ = lean_unbox(v_snd_252_);
lean_dec(v_snd_252_);
v___y_161_ = v___x_276_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 8:
{
lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v_fvarId_279_; lean_object* v_i_280_; lean_object* v_y_281_; lean_object* v_k_282_; size_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v_fst_277_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_277_);
v_snd_278_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_278_);
lean_dec(v_a_174_);
v_fvarId_279_ = lean_ctor_get(v_c_153_, 0);
v_i_280_ = lean_ctor_get(v_c_153_, 1);
v_y_281_ = lean_ctor_get(v_c_153_, 2);
v_k_282_ = lean_ctor_get(v_c_153_, 3);
v___x_283_ = lean_ptr_addr(v_k_282_);
v___x_284_ = lean_ptr_addr(v_fst_277_);
v___x_285_ = lean_usize_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
lean_inc(v_y_281_);
lean_inc(v_i_280_);
lean_inc(v_fvarId_279_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_294_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_297_);
v___x_287_ = v_c_153_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_c_153_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 3, v_fst_277_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fvarId_279_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_i_280_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_y_281_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_fst_277_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
uint8_t v___x_291_; 
v___x_291_ = lean_unbox(v_snd_278_);
lean_dec(v_snd_278_);
v___y_161_ = v___x_291_;
v___y_162_ = v___x_290_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_298_; 
lean_dec(v_fst_277_);
v___x_298_ = lean_unbox(v_snd_278_);
lean_dec(v_snd_278_);
v___y_161_ = v___x_298_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 10:
{
lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v_fvarId_301_; lean_object* v_cidx_302_; lean_object* v_k_303_; size_t v___x_304_; size_t v___x_305_; uint8_t v___x_306_; 
v_fst_299_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_299_);
v_snd_300_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_300_);
lean_dec(v_a_174_);
v_fvarId_301_ = lean_ctor_get(v_c_153_, 0);
v_cidx_302_ = lean_ctor_get(v_c_153_, 1);
v_k_303_ = lean_ctor_get(v_c_153_, 2);
v___x_304_ = lean_ptr_addr(v_k_303_);
v___x_305_ = lean_ptr_addr(v_fst_299_);
v___x_306_ = lean_usize_dec_eq(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_cidx_302_);
lean_inc(v_fvarId_301_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_315_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_317_);
v___x_308_ = v_c_153_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_c_153_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 2, v_fst_299_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_fvarId_301_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_cidx_302_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_fst_299_);
v___x_311_ = v_reuseFailAlloc_313_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_unbox(v_snd_300_);
lean_dec(v_snd_300_);
v___y_161_ = v___x_312_;
v___y_162_ = v___x_311_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_318_; 
lean_dec(v_fst_299_);
v___x_318_ = lean_unbox(v_snd_300_);
lean_dec(v_snd_300_);
v___y_161_ = v___x_318_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 11:
{
lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v_fvarId_321_; lean_object* v_n_322_; uint8_t v_check_323_; uint8_t v_persistent_324_; lean_object* v_k_325_; size_t v___x_326_; size_t v___x_327_; uint8_t v___x_328_; 
v_fst_319_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_319_);
v_snd_320_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_320_);
lean_dec(v_a_174_);
v_fvarId_321_ = lean_ctor_get(v_c_153_, 0);
v_n_322_ = lean_ctor_get(v_c_153_, 1);
v_check_323_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*3);
v_persistent_324_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*3 + 1);
v_k_325_ = lean_ctor_get(v_c_153_, 2);
v___x_326_ = lean_ptr_addr(v_k_325_);
v___x_327_ = lean_ptr_addr(v_fst_319_);
v___x_328_ = lean_usize_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
lean_inc(v_n_322_);
lean_inc(v_fvarId_321_);
v_isSharedCheck_336_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; lean_object* v_unused_338_; lean_object* v_unused_339_; 
v_unused_337_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_339_);
v___x_330_ = v_c_153_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_c_153_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 2, v_fst_319_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_fvarId_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_n_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_fst_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*3, v_check_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*3 + 1, v_persistent_324_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
uint8_t v___x_334_; 
v___x_334_ = lean_unbox(v_snd_320_);
lean_dec(v_snd_320_);
v___y_161_ = v___x_334_;
v___y_162_ = v___x_333_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_340_; 
lean_dec(v_fst_319_);
v___x_340_ = lean_unbox(v_snd_320_);
lean_dec(v_snd_320_);
v___y_161_ = v___x_340_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 12:
{
lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v_fvarId_343_; lean_object* v_n_344_; uint8_t v_check_345_; uint8_t v_persistent_346_; lean_object* v_objs_x3f_347_; lean_object* v_k_348_; size_t v___x_349_; size_t v___x_350_; uint8_t v___x_351_; 
v_fst_341_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_341_);
v_snd_342_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_342_);
lean_dec(v_a_174_);
v_fvarId_343_ = lean_ctor_get(v_c_153_, 0);
v_n_344_ = lean_ctor_get(v_c_153_, 1);
v_check_345_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*4);
v_persistent_346_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*4 + 1);
v_objs_x3f_347_ = lean_ctor_get(v_c_153_, 2);
v_k_348_ = lean_ctor_get(v_c_153_, 3);
v___x_349_ = lean_ptr_addr(v_k_348_);
v___x_350_ = lean_ptr_addr(v_fst_341_);
v___x_351_ = lean_usize_dec_eq(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
lean_inc(v_objs_x3f_347_);
lean_inc(v_n_344_);
lean_inc(v_fvarId_343_);
v_isSharedCheck_359_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_360_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_363_);
v___x_353_ = v_c_153_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_c_153_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 3, v_fst_341_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_fvarId_343_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_n_344_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_objs_x3f_347_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_fst_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*4, v_check_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*4 + 1, v_persistent_346_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
uint8_t v___x_357_; 
v___x_357_ = lean_unbox(v_snd_342_);
lean_dec(v_snd_342_);
v___y_161_ = v___x_357_;
v___y_162_ = v___x_356_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_364_; 
lean_dec(v_fst_341_);
v___x_364_ = lean_unbox(v_snd_342_);
lean_dec(v_snd_342_);
v___y_161_ = v___x_364_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 13:
{
lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v_fvarId_367_; lean_object* v_k_368_; size_t v___x_369_; size_t v___x_370_; uint8_t v___x_371_; 
v_fst_365_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_365_);
v_snd_366_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_366_);
lean_dec(v_a_174_);
v_fvarId_367_ = lean_ctor_get(v_c_153_, 0);
v_k_368_ = lean_ctor_get(v_c_153_, 1);
v___x_369_ = lean_ptr_addr(v_k_368_);
v___x_370_ = lean_ptr_addr(v_fst_365_);
v___x_371_ = lean_usize_dec_eq(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
lean_inc(v_fvarId_367_);
v_isSharedCheck_379_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_380_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_381_);
v___x_373_ = v_c_153_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_dec(v_c_153_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 1, v_fst_365_);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_fvarId_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_fst_365_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
uint8_t v___x_377_; 
v___x_377_ = lean_unbox(v_snd_366_);
lean_dec(v_snd_366_);
v___y_161_ = v___x_377_;
v___y_162_ = v___x_376_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_382_; 
lean_dec(v_fst_365_);
v___x_382_ = lean_unbox(v_snd_366_);
lean_dec(v_snd_366_);
v___y_161_ = v___x_382_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
default: 
{
lean_object* v_snd_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_dec_ref(v_c_153_);
v_snd_383_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_383_);
lean_dec(v_a_174_);
v___x_384_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
v___x_385_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(v___x_384_);
v___x_386_ = lean_unbox(v_snd_383_);
lean_dec(v_snd_383_);
v___y_161_ = v___x_386_;
v___y_162_ = v___x_385_;
goto v___jp_160_;
}
}
}
else
{
lean_dec_ref(v_c_153_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* v_info_584_, lean_object* v_w_585_, size_t v_sz_586_, size_t v_i_587_, lean_object* v_bs_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_lt(v_i_587_, v_sz_586_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v_w_585_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_bs_588_);
return v___x_596_;
}
else
{
lean_object* v_v_597_; lean_object* v___x_598_; lean_object* v_bs_x27_599_; lean_object* v___y_601_; 
v_v_597_ = lean_array_uget(v_bs_588_, v_i_587_);
v___x_598_ = lean_unsigned_to_nat(0u);
v_bs_x27_599_ = lean_array_uset(v_bs_588_, v_i_587_, v___x_598_);
switch(lean_obj_tag(v_v_597_))
{
case 0:
{
lean_object* v_code_626_; 
v_code_626_ = lean_ctor_get(v_v_597_, 2);
lean_inc_ref(v_code_626_);
v___y_601_ = v_code_626_;
goto v___jp_600_;
}
case 1:
{
lean_object* v_code_627_; 
v_code_627_ = lean_ctor_get(v_v_597_, 1);
lean_inc_ref(v_code_627_);
v___y_601_ = v_code_627_;
goto v___jp_600_;
}
default: 
{
lean_object* v_code_628_; 
v_code_628_ = lean_ctor_get(v_v_597_, 0);
lean_inc_ref(v_code_628_);
v___y_601_ = v_code_628_;
goto v___jp_600_;
}
}
v___jp_600_:
{
lean_object* v___x_602_; 
lean_inc(v_w_585_);
v___x_602_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_584_, v_w_585_, v___y_601_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_fst_604_ = lean_ctor_get(v_a_603_, 0);
v_snd_605_ = lean_ctor_get(v_a_603_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_617_ == 0)
{
v___x_607_ = v_a_603_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v_a_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_597_, v_fst_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_snd_605_);
v___x_611_ = v_reuseFailAlloc_616_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_587_, v___x_612_);
v___x_614_ = lean_array_uset(v_bs_x27_599_, v_i_587_, v___x_611_);
v_i_587_ = v___x_613_;
v_bs_588_ = v___x_614_;
goto _start;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_bs_x27_599_);
lean_dec(v_v_597_);
lean_dec(v_w_585_);
v_a_618_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_602_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_602_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* v_info_629_, lean_object* v_w_630_, lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_bs_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_641_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_629_, v_w_630_, v_sz_boxed_640_, v_i_boxed_641_, v_bs_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v_info_629_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* v_info_643_, lean_object* v_w_644_, lean_object* v_c_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_643_, v_w_644_, v_c_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_info_643_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; lean_object* v_ngen_656_; lean_object* v_namePrefix_657_; lean_object* v_idx_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_688_; 
v___x_655_ = lean_st_ref_get(v___y_653_);
v_ngen_656_ = lean_ctor_get(v___x_655_, 2);
lean_inc_ref(v_ngen_656_);
lean_dec(v___x_655_);
v_namePrefix_657_ = lean_ctor_get(v_ngen_656_, 0);
v_idx_658_ = lean_ctor_get(v_ngen_656_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_ngen_656_);
if (v_isSharedCheck_688_ == 0)
{
v___x_660_ = v_ngen_656_;
v_isShared_661_ = v_isSharedCheck_688_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_idx_658_);
lean_inc(v_namePrefix_657_);
lean_dec(v_ngen_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_688_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_r_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_idx_658_);
lean_inc(v_namePrefix_657_);
v_r_662_ = l_Lean_Name_num___override(v_namePrefix_657_, v_idx_658_);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_idx_658_, v___x_663_);
lean_dec(v_idx_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_namePrefix_657_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_687_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v_env_668_; lean_object* v_nextMacroScope_669_; lean_object* v_auxDeclNGen_670_; lean_object* v_traceState_671_; lean_object* v_cache_672_; lean_object* v_recordedDeps_673_; lean_object* v_messages_674_; lean_object* v_infoState_675_; lean_object* v_snapshotTasks_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_685_; 
v___x_667_ = lean_st_ref_take(v___y_653_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
v_nextMacroScope_669_ = lean_ctor_get(v___x_667_, 1);
v_auxDeclNGen_670_ = lean_ctor_get(v___x_667_, 3);
v_traceState_671_ = lean_ctor_get(v___x_667_, 4);
v_cache_672_ = lean_ctor_get(v___x_667_, 5);
v_recordedDeps_673_ = lean_ctor_get(v___x_667_, 6);
v_messages_674_ = lean_ctor_get(v___x_667_, 7);
v_infoState_675_ = lean_ctor_get(v___x_667_, 8);
v_snapshotTasks_676_ = lean_ctor_get(v___x_667_, 9);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_667_, 2);
lean_dec(v_unused_686_);
v___x_678_ = v___x_667_;
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snapshotTasks_676_);
lean_inc(v_infoState_675_);
lean_inc(v_messages_674_);
lean_inc(v_recordedDeps_673_);
lean_inc(v_cache_672_);
lean_inc(v_traceState_671_);
lean_inc(v_auxDeclNGen_670_);
lean_inc(v_nextMacroScope_669_);
lean_inc(v_env_668_);
lean_dec(v___x_667_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 2, v___x_666_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_env_668_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_nextMacroScope_669_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_auxDeclNGen_670_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_traceState_671_);
lean_ctor_set(v_reuseFailAlloc_684_, 5, v_cache_672_);
lean_ctor_set(v_reuseFailAlloc_684_, 6, v_recordedDeps_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 7, v_messages_674_);
lean_ctor_set(v_reuseFailAlloc_684_, 8, v_infoState_675_);
lean_ctor_set(v_reuseFailAlloc_684_, 9, v_snapshotTasks_676_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_st_ref_put(v___y_653_, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_r_662_);
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_689_);
lean_dec(v___y_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v___x_698_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_696_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_713_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
v___x_722_ = l_Lean_Expr_const___override(v___x_721_, v___x_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* v_x_723_, lean_object* v_info_724_, lean_object* v_c_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_n(v_a_733_, 2);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_724_, v_a_733_, v_c_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_789_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_789_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_789_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_789_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_snd_739_; uint8_t v___x_740_; 
v_snd_739_ = lean_ctor_get(v_a_735_, 1);
v___x_740_ = lean_unbox(v_snd_739_);
if (v___x_740_ == 0)
{
lean_object* v_fst_741_; lean_object* v___x_743_; 
lean_dec(v_a_733_);
lean_dec(v_x_723_);
v_fst_741_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_fst_741_);
lean_dec(v_a_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_fst_741_);
v___x_743_ = v___x_737_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v_fst_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_787_; 
lean_del_object(v___x_737_);
v_fst_745_ = lean_ctor_get(v_a_735_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_a_735_, 1);
lean_dec(v_unused_788_);
v___x_747_ = v_a_735_;
v_isShared_748_ = v_isSharedCheck_787_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_fst_745_);
lean_dec(v_a_735_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_787_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
v___x_750_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_749_, v_a_728_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_778_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_778_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_778_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_778_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_size_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v_size_755_ = lean_ctor_get(v_info_724_, 2);
v___x_756_ = 1;
v___x_757_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
lean_inc(v_size_755_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 11);
lean_ctor_set(v___x_747_, 1, v_x_723_);
lean_ctor_set(v___x_747_, 0, v_size_755_);
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_size_755_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_x_723_);
v___x_759_ = v_reuseFailAlloc_777_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_lctx_762_; lean_object* v_nextIdx_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_776_; 
v___x_760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_760_, 0, v_a_733_);
lean_ctor_set(v___x_760_, 1, v_a_751_);
lean_ctor_set(v___x_760_, 2, v___x_757_);
lean_ctor_set(v___x_760_, 3, v___x_759_);
v___x_761_ = lean_st_ref_take(v_a_728_);
v_lctx_762_ = lean_ctor_get(v___x_761_, 0);
v_nextIdx_763_ = lean_ctor_get(v___x_761_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_776_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_nextIdx_763_);
lean_inc(v_lctx_762_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_inc_ref(v___x_760_);
v___x_767_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_756_, v_lctx_762_, v___x_760_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_nextIdx_763_);
v___x_769_ = v_reuseFailAlloc_775_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_st_ref_put(v_a_728_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_760_);
lean_ctor_set(v___x_771_, 1, v_fst_745_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_771_);
v___x_773_ = v___x_753_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
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
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_del_object(v___x_747_);
lean_dec(v_fst_745_);
lean_dec(v_a_733_);
lean_dec(v_x_723_);
v_a_779_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_750_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_750_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_a_733_);
lean_dec(v_x_723_);
v_a_790_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_734_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_734_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_c_725_);
lean_dec(v_x_723_);
v_a_798_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_732_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_732_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* v_x_806_, lean_object* v_info_807_, lean_object* v_c_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_806_, v_info_807_, v_c_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_info_807_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_829_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* v_x_830_, lean_object* v_as_831_, size_t v_i_832_, size_t v_stop_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_832_, v_stop_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_835_ = lean_array_uget_borrowed(v_as_831_, v_i_832_);
v___x_836_ = 1;
lean_inc(v_x_830_);
v___x_837_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_830_);
v___x_838_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_836_, v___x_835_, v___x_837_);
lean_dec(v___x_837_);
if (v___x_838_ == 0)
{
size_t v___x_839_; size_t v___x_840_; 
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_832_, v___x_839_);
v_i_832_ = v___x_840_;
goto _start;
}
else
{
lean_dec(v_x_830_);
return v___x_838_;
}
}
else
{
uint8_t v___x_842_; 
lean_dec(v_x_830_);
v___x_842_ = 0;
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* v_x_843_, lean_object* v_as_844_, lean_object* v_i_845_, lean_object* v_stop_846_){
_start:
{
size_t v_i_boxed_847_; size_t v_stop_boxed_848_; uint8_t v_res_849_; lean_object* v_r_850_; 
v_i_boxed_847_ = lean_unbox_usize(v_i_845_);
lean_dec(v_i_845_);
v_stop_boxed_848_ = lean_unbox_usize(v_stop_846_);
lean_dec(v_stop_846_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_843_, v_as_844_, v_i_boxed_847_, v_stop_boxed_848_);
lean_dec_ref(v_as_844_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* v_instr_851_, lean_object* v_x_852_){
_start:
{
if (lean_obj_tag(v_instr_851_) == 0)
{
lean_object* v_decl_853_; lean_object* v_value_854_; 
v_decl_853_ = lean_ctor_get(v_instr_851_, 0);
v_value_854_ = lean_ctor_get(v_decl_853_, 3);
if (lean_obj_tag(v_value_854_) == 5)
{
lean_object* v_args_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_args_855_ = lean_ctor_get(v_value_854_, 1);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v_args_855_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_dec(v_x_852_);
return v___x_858_;
}
else
{
if (v___x_858_ == 0)
{
lean_dec(v_x_852_);
return v___x_858_;
}
else
{
size_t v___x_859_; size_t v___x_860_; uint8_t v___x_861_; 
v___x_859_ = ((size_t)0ULL);
v___x_860_ = lean_usize_of_nat(v___x_857_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_852_, v_args_855_, v___x_859_, v___x_860_);
return v___x_861_;
}
}
}
else
{
uint8_t v___x_862_; 
lean_dec(v_x_852_);
v___x_862_ = 0;
return v___x_862_;
}
}
else
{
uint8_t v___x_863_; 
lean_dec(v_x_852_);
v___x_863_ = 0;
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* v_instr_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_864_, v_x_865_);
lean_dec_ref(v_instr_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t v_x_868_){
_start:
{
switch(v_x_868_)
{
case 0:
{
lean_object* v___x_869_; 
v___x_869_ = lean_unsigned_to_nat(0u);
return v___x_869_;
}
case 1:
{
lean_object* v___x_870_; 
v___x_870_ = lean_unsigned_to_nat(1u);
return v___x_870_;
}
default: 
{
lean_object* v___x_871_; 
v___x_871_ = lean_unsigned_to_nat(2u);
return v___x_871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object* v_x_872_){
_start:
{
uint8_t v_x_boxed_873_; lean_object* v_res_874_; 
v_x_boxed_873_ = lean_unbox(v_x_872_);
v_res_874_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_boxed_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* v_k_875_){
_start:
{
lean_inc(v_k_875_);
return v_k_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* v_k_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_876_);
lean_dec(v_k_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* v_motive_878_, lean_object* v_ctorIdx_879_, uint8_t v_t_880_, lean_object* v_h_881_, lean_object* v_k_882_){
_start:
{
lean_inc(v_k_882_);
return v_k_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* v_motive_883_, lean_object* v_ctorIdx_884_, lean_object* v_t_885_, lean_object* v_h_886_, lean_object* v_k_887_){
_start:
{
uint8_t v_t_boxed_888_; lean_object* v_res_889_; 
v_t_boxed_888_ = lean_unbox(v_t_885_);
v_res_889_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(v_motive_883_, v_ctorIdx_884_, v_t_boxed_888_, v_h_886_, v_k_887_);
lean_dec(v_k_887_);
lean_dec(v_ctorIdx_884_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* v_ownedArg_890_){
_start:
{
lean_inc(v_ownedArg_890_);
return v_ownedArg_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* v_ownedArg_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_891_);
lean_dec(v_ownedArg_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* v_motive_893_, uint8_t v_t_894_, lean_object* v_h_895_, lean_object* v_ownedArg_896_){
_start:
{
lean_inc(v_ownedArg_896_);
return v_ownedArg_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* v_motive_897_, lean_object* v_t_898_, lean_object* v_h_899_, lean_object* v_ownedArg_900_){
_start:
{
uint8_t v_t_boxed_901_; lean_object* v_res_902_; 
v_t_boxed_901_ = lean_unbox(v_t_898_);
v_res_902_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_897_, v_t_boxed_901_, v_h_899_, v_ownedArg_900_);
lean_dec(v_ownedArg_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* v_other_903_){
_start:
{
lean_inc(v_other_903_);
return v_other_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* v_other_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_904_);
lean_dec(v_other_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* v_motive_906_, uint8_t v_t_907_, lean_object* v_h_908_, lean_object* v_other_909_){
_start:
{
lean_inc(v_other_909_);
return v_other_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* v_motive_910_, lean_object* v_t_911_, lean_object* v_h_912_, lean_object* v_other_913_){
_start:
{
uint8_t v_t_boxed_914_; lean_object* v_res_915_; 
v_t_boxed_914_ = lean_unbox(v_t_911_);
v_res_915_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_910_, v_t_boxed_914_, v_h_912_, v_other_913_);
lean_dec(v_other_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* v_none_916_){
_start:
{
lean_inc(v_none_916_);
return v_none_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* v_none_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_917_);
lean_dec(v_none_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* v_motive_919_, uint8_t v_t_920_, lean_object* v_h_921_, lean_object* v_none_922_){
_start:
{
lean_inc(v_none_922_);
return v_none_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* v_motive_923_, lean_object* v_t_924_, lean_object* v_h_925_, lean_object* v_none_926_){
_start:
{
uint8_t v_t_boxed_927_; lean_object* v_res_928_; 
v_t_boxed_927_ = lean_unbox(v_t_924_);
v_res_928_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(v_motive_923_, v_t_boxed_927_, v_h_925_, v_none_926_);
lean_dec(v_none_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* v_x_929_, lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_){
_start:
{
lean_object* v_a_936_; uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_b_933_);
return v___x_941_;
}
else
{
lean_object* v_snd_942_; lean_object* v_fst_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_987_; 
v_snd_942_ = lean_ctor_get(v_b_933_, 1);
v_fst_943_ = lean_ctor_get(v_b_933_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_b_933_);
if (v_isSharedCheck_987_ == 0)
{
v___x_945_ = v_b_933_;
v_isShared_946_ = v_isSharedCheck_987_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snd_942_);
lean_inc(v_fst_943_);
lean_dec(v_b_933_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_987_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_array_947_; lean_object* v_start_948_; lean_object* v_stop_949_; uint8_t v___x_950_; 
v_array_947_ = lean_ctor_get(v_snd_942_, 0);
v_start_948_ = lean_ctor_get(v_snd_942_, 1);
v_stop_949_ = lean_ctor_get(v_snd_942_, 2);
v___x_950_ = lean_nat_dec_lt(v_start_948_, v_stop_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_952_; 
if (v_isShared_946_ == 0)
{
v___x_952_ = v___x_945_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_fst_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_snd_942_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_stop_949_);
lean_inc(v_start_948_);
lean_inc_ref(v_array_947_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_snd_942_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; 
v_unused_984_ = lean_ctor_get(v_snd_942_, 2);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_snd_942_, 1);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_snd_942_, 0);
lean_dec(v_unused_986_);
v___x_956_ = v_snd_942_;
v_isShared_957_ = v_isSharedCheck_983_;
goto v_resetjp_955_;
}
else
{
lean_dec(v_snd_942_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_983_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v_a_958_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
v___x_959_ = lean_array_fget(v_array_947_, v_start_948_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_start_948_, v___x_960_);
lean_dec(v_start_948_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_961_);
v___x_963_ = v___x_956_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_array_947_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_stop_949_);
v___x_963_ = v_reuseFailAlloc_982_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
uint8_t v___y_965_; 
if (lean_obj_tag(v_a_958_) == 1)
{
lean_object* v_fvarId_970_; uint8_t v___x_971_; 
v_fvarId_970_ = lean_ctor_get(v_a_958_, 0);
v___x_971_ = l_Lean_instBEqFVarId_beq(v_fvarId_970_, v_x_929_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec(v___x_959_);
lean_del_object(v___x_945_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_fst_943_);
lean_ctor_set(v___x_972_, 1, v___x_963_);
v_a_936_ = v___x_972_;
goto v___jp_935_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = lean_unbox(v_fst_943_);
switch(v___x_973_)
{
case 0:
{
uint8_t v_borrow_974_; 
v_borrow_974_ = lean_ctor_get_uint8(v___x_959_, sizeof(void*)*3);
lean_dec(v___x_959_);
if (v_borrow_974_ == 0)
{
uint8_t v___x_975_; 
v___x_975_ = lean_unbox(v_fst_943_);
lean_dec(v_fst_943_);
v___y_965_ = v___x_975_;
goto v___jp_964_;
}
else
{
uint8_t v___x_976_; 
lean_dec(v_fst_943_);
v___x_976_ = 1;
v___y_965_ = v___x_976_;
goto v___jp_964_;
}
}
case 1:
{
uint8_t v___x_977_; 
lean_dec(v___x_959_);
v___x_977_ = lean_unbox(v_fst_943_);
lean_dec(v_fst_943_);
v___y_965_ = v___x_977_;
goto v___jp_964_;
}
default: 
{
uint8_t v_borrow_978_; 
lean_dec(v_fst_943_);
v_borrow_978_ = lean_ctor_get_uint8(v___x_959_, sizeof(void*)*3);
lean_dec(v___x_959_);
if (v_borrow_978_ == 0)
{
uint8_t v___x_979_; 
v___x_979_ = 0;
v___y_965_ = v___x_979_;
goto v___jp_964_;
}
else
{
uint8_t v___x_980_; 
v___x_980_ = 1;
v___y_965_ = v___x_980_;
goto v___jp_964_;
}
}
}
}
}
else
{
lean_object* v___x_981_; 
lean_dec(v___x_959_);
lean_del_object(v___x_945_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_fst_943_);
lean_ctor_set(v___x_981_, 1, v___x_963_);
v_a_936_ = v___x_981_;
goto v___jp_935_;
}
v___jp_964_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_box(v___y_965_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_963_);
lean_ctor_set(v___x_945_, 0, v___x_966_);
v___x_968_ = v___x_945_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v_a_936_ = v___x_968_;
goto v___jp_935_;
}
}
}
}
}
}
}
v___jp_935_:
{
size_t v___x_937_; size_t v___x_938_; 
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_932_, v___x_937_);
v_i_932_ = v___x_938_;
v_b_933_ = v_a_936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* v_x_988_, lean_object* v_as_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_b_992_, lean_object* v___y_993_){
_start:
{
size_t v_sz_boxed_994_; size_t v_i_boxed_995_; lean_object* v_res_996_; 
v_sz_boxed_994_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_995_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_988_, v_as_989_, v_sz_boxed_994_, v_i_boxed_995_, v_b_992_);
lean_dec_ref(v_as_989_);
lean_dec(v_x_988_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* v_instr_997_, lean_object* v_x_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
if (lean_obj_tag(v_instr_997_) == 0)
{
lean_object* v_decl_1015_; lean_object* v_value_1016_; 
v_decl_1015_ = lean_ctor_get(v_instr_997_, 0);
v_value_1016_ = lean_ctor_get(v_decl_1015_, 3);
lean_inc(v_value_1016_);
switch(lean_obj_tag(v_value_1016_))
{
case 9:
{
lean_object* v_fn_1017_; lean_object* v_args_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref_known(v_instr_997_, 1);
v_fn_1017_ = lean_ctor_get(v_value_1016_, 0);
v_args_1018_ = lean_ctor_get(v_value_1016_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_value_1016_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1020_ = v_value_1016_;
v_isShared_1021_ = v_isSharedCheck_1080_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_args_1018_);
lean_inc(v_fn_1017_);
lean_dec(v_value_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1080_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
uint8_t v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = 1;
lean_inc_ref(v_args_1018_);
lean_inc(v_fn_1017_);
if (v_isShared_1021_ == 0)
{
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_fn_1017_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_args_1018_);
v___x_1024_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1017_, v_a_1003_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1070_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1070_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1070_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
if (lean_obj_tag(v_a_1026_) == 1)
{
lean_object* v_val_1030_; lean_object* v_params_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; size_t v_sz_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
lean_del_object(v___x_1028_);
lean_dec_ref(v___x_1024_);
v_val_1030_ = lean_ctor_get(v_a_1026_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v_a_1026_, 1);
v_params_1031_ = lean_ctor_get(v_val_1030_, 3);
lean_inc_ref(v_params_1031_);
lean_dec(v_val_1030_);
v___x_1032_ = 2;
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_array_get_size(v_params_1031_);
v___x_1035_ = l_Array_toSubarray___redArg(v_params_1031_, v___x_1033_, v___x_1034_);
v___x_1036_ = lean_box(v___x_1032_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
v_sz_1038_ = lean_array_size(v_args_1018_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_998_, v_args_1018_, v_sz_1038_, v___x_1039_, v___x_1037_);
lean_dec_ref(v_args_1018_);
lean_dec(v_x_998_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_fst_1045_; lean_object* v___x_1047_; 
v_fst_1045_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_fst_1045_);
lean_dec(v_a_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v_fst_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_fst_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1040_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1040_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
lean_dec(v_a_1026_);
lean_dec_ref(v_args_1018_);
v___x_1058_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_998_);
v___x_1059_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1022_, v___x_1024_, v___x_1058_);
lean_dec(v___x_1058_);
lean_dec_ref(v___x_1024_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1060_ = 2;
v___x_1061_ = lean_box(v___x_1060_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1061_);
v___x_1063_ = v___x_1028_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = 0;
v___x_1066_ = lean_box(v___x_1065_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1066_);
v___x_1068_ = v___x_1028_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_args_1018_);
lean_dec(v_x_998_);
v_a_1071_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1025_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1025_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
case 10:
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1106_; 
v_isSharedCheck_1106_ = !lean_is_exclusive(v_instr_997_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v_instr_997_, 0);
lean_dec(v_unused_1107_);
v___x_1082_ = v_instr_997_;
v_isShared_1083_ = v_isSharedCheck_1106_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v_instr_997_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1106_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_fn_1084_; lean_object* v_args_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1105_; 
v_fn_1084_ = lean_ctor_get(v_value_1016_, 0);
v_args_1085_ = lean_ctor_get(v_value_1016_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_value_1016_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1087_ = v_value_1016_;
v_isShared_1088_ = v_isSharedCheck_1105_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_args_1085_);
lean_inc(v_fn_1084_);
lean_dec(v_value_1016_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1105_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
uint8_t v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = 1;
if (v_isShared_1088_ == 0)
{
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_fn_1084_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_args_1085_);
v___x_1091_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_998_);
v___x_1093_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1089_, v___x_1091_, v___x_1092_);
lean_dec(v___x_1092_);
lean_dec_ref(v___x_1091_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = 2;
v___x_1095_ = lean_box(v___x_1094_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1095_);
v___x_1097_ = v___x_1082_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
else
{
uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1099_ = 0;
v___x_1100_ = lean_box(v___x_1099_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1100_);
v___x_1102_ = v___x_1082_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1133_; 
v_isSharedCheck_1133_ = !lean_is_exclusive(v_instr_997_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_instr_997_, 0);
lean_dec(v_unused_1134_);
v___x_1109_ = v_instr_997_;
v_isShared_1110_ = v_isSharedCheck_1133_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_instr_997_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1133_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fvarId_1111_; lean_object* v_args_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1132_; 
v_fvarId_1111_ = lean_ctor_get(v_value_1016_, 0);
v_args_1112_ = lean_ctor_get(v_value_1016_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_value_1016_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1114_ = v_value_1016_;
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_args_1112_);
lean_inc(v_fvarId_1111_);
lean_dec(v_value_1016_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint8_t v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = 1;
if (v_isShared_1115_ == 0)
{
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_fvarId_1111_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_args_1112_);
v___x_1118_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_998_);
v___x_1120_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1116_, v___x_1118_, v___x_1119_);
lean_dec(v___x_1119_);
lean_dec_ref(v___x_1118_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = 2;
v___x_1122_ = lean_box(v___x_1121_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1122_);
v___x_1124_ = v___x_1109_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1126_ = 0;
v___x_1127_ = lean_box(v___x_1126_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1127_);
v___x_1129_ = v___x_1109_;
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
}
}
}
}
default: 
{
lean_dec(v_value_1016_);
goto v___jp_1005_;
}
}
}
else
{
goto v___jp_1005_;
}
v___jp_1005_:
{
uint8_t v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = 1;
v___x_1007_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_998_);
v___x_1008_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_1006_, v_instr_997_, v___x_1007_);
lean_dec(v___x_1007_);
lean_dec_ref(v_instr_997_);
if (v___x_1008_ == 0)
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = 2;
v___x_1010_ = lean_box(v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
else
{
uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = 1;
v___x_1013_ = lean_box(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* v_instr_1135_, lean_object* v_x_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1135_, v_x_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* v_x_1144_, lean_object* v_as_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1144_, v_as_1145_, v_sz_1146_, v_i_1147_, v_b_1148_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* v_x_1156_, lean_object* v_as_1157_, lean_object* v_sz_1158_, lean_object* v_i_1159_, lean_object* v_b_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
size_t v_sz_boxed_1167_; size_t v_i_boxed_1168_; lean_object* v_res_1169_; 
v_sz_boxed_1167_ = lean_unbox_usize(v_sz_1158_);
lean_dec(v_sz_1158_);
v_i_boxed_1168_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1156_, v_as_1157_, v_sz_boxed_1167_, v_i_boxed_1168_, v_b_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_as_1157_);
lean_dec(v_x_1156_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* v_alt_1170_, lean_object* v_f_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___y_1179_; 
switch(lean_obj_tag(v_alt_1170_))
{
case 0:
{
lean_object* v_code_1198_; 
v_code_1198_ = lean_ctor_get(v_alt_1170_, 2);
lean_inc_ref(v_code_1198_);
v___y_1179_ = v_code_1198_;
goto v___jp_1178_;
}
case 1:
{
lean_object* v_code_1199_; 
v_code_1199_ = lean_ctor_get(v_alt_1170_, 1);
lean_inc_ref(v_code_1199_);
v___y_1179_ = v_code_1199_;
goto v___jp_1178_;
}
default: 
{
lean_object* v_code_1200_; 
v_code_1200_ = lean_ctor_get(v_alt_1170_, 0);
lean_inc_ref(v_code_1200_);
v___y_1179_ = v_code_1200_;
goto v___jp_1178_;
}
}
v___jp_1178_:
{
lean_object* v___x_1180_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc_ref(v___y_1172_);
v___x_1180_ = lean_apply_7(v_f_1171_, v___y_1179_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, lean_box(0));
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1189_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1189_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1189_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1170_, v_a_1181_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1187_ = v___x_1183_;
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
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_alt_1170_);
v_a_1190_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1180_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1180_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* v_alt_1201_, lean_object* v_f_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1201_, v_f_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* v_x_1210_, lean_object* v_info_1211_, lean_object* v_c_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1210_, v_info_1211_, v_c_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v_a_1213_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* v_x_1220_, lean_object* v_info_1221_, lean_object* v_i_1222_, lean_object* v_as_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_array_get_size(v_as_1223_);
v___x_1231_ = lean_nat_dec_lt(v_i_1222_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_i_1222_);
lean_dec_ref(v_info_1221_);
lean_dec(v_x_1220_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_as_1223_);
return v___x_1232_;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_a_1233_ = lean_array_fget_borrowed(v_as_1223_, v_i_1222_);
lean_inc_ref(v_info_1221_);
lean_inc(v_x_1220_);
v___x_1234_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(v___x_1234_, 0, v_x_1220_);
lean_closure_set(v___x_1234_, 1, v_info_1221_);
lean_inc(v_a_1233_);
v___x_1235_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_1233_, v___x_1234_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; size_t v___x_1237_; size_t v___x_1238_; uint8_t v___x_1239_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = lean_ptr_addr(v_a_1233_);
v___x_1238_ = lean_ptr_addr(v_a_1236_);
v___x_1239_ = lean_usize_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_i_1222_, v___x_1240_);
v___x_1242_ = lean_array_fset(v_as_1223_, v_i_1222_, v_a_1236_);
lean_dec(v_i_1222_);
v_i_1222_ = v___x_1241_;
v_as_1223_ = v___x_1242_;
goto _start;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec(v_a_1236_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_i_1222_, v___x_1244_);
lean_dec(v_i_1222_);
v_i_1222_ = v___x_1245_;
goto _start;
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_as_1223_);
lean_dec(v_i_1222_);
lean_dec_ref(v_info_1221_);
lean_dec(v_x_1220_);
v_a_1247_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1235_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1235_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_1257_ = lean_unsigned_to_nat(61u);
v___x_1258_ = lean_unsigned_to_nat(247u);
v___x_1259_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
v___x_1260_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_1261_ = l_mkPanicMessageWithDecl(v___x_1260_, v___x_1259_, v___x_1258_, v___x_1257_, v___x_1256_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* v_x_1262_, lean_object* v_info_1263_, lean_object* v_c_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
switch(lean_obj_tag(v_c_1264_))
{
case 0:
{
lean_object* v_decl_1271_; lean_object* v_k_1272_; uint8_t v___x_1273_; lean_object* v_instr_1274_; uint8_t v___x_1275_; uint8_t v___x_1276_; 
v_decl_1271_ = lean_ctor_get(v_c_1264_, 0);
v_k_1272_ = lean_ctor_get(v_c_1264_, 1);
v___x_1273_ = 1;
v_instr_1274_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1273_, v_c_1264_);
lean_inc(v_x_1262_);
v___x_1275_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1274_, v_x_1262_);
v___x_1276_ = 1;
if (v___x_1275_ == 0)
{
lean_object* v___x_1277_; 
lean_inc_ref(v_k_1272_);
lean_inc_ref(v_info_1263_);
lean_inc(v_x_1262_);
v___x_1277_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1262_, v_info_1263_, v_k_1272_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1395_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1395_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1395_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___y_1283_; lean_object* v_snd_1289_; uint8_t v___x_1290_; 
v_snd_1289_ = lean_ctor_get(v_a_1278_, 1);
v___x_1290_ = lean_unbox(v_snd_1289_);
if (v___x_1290_ == 0)
{
lean_object* v_fst_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1380_; 
lean_inc(v_snd_1289_);
lean_del_object(v___x_1280_);
v_fst_1291_ = lean_ctor_get(v_a_1278_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_a_1278_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v_a_1278_, 1);
lean_dec(v_unused_1381_);
v___x_1293_ = v_a_1278_;
v_isShared_1294_ = v_isSharedCheck_1380_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_fst_1291_);
lean_dec(v_a_1278_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1380_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; 
lean_inc(v_x_1262_);
v___x_1295_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1274_, v_x_1262_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1371_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1371_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1371_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___y_1301_; lean_object* v___y_1309_; uint8_t v___x_1313_; 
v___x_1313_ = lean_unbox(v_a_1296_);
lean_dec(v_a_1296_);
switch(v___x_1313_)
{
case 0:
{
size_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
lean_del_object(v___x_1298_);
lean_del_object(v___x_1293_);
lean_dec(v_snd_1289_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1314_ = lean_ptr_addr(v_k_1272_);
v___x_1315_ = lean_ptr_addr(v_fst_1291_);
v___x_1316_ = lean_usize_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_inc_ref(v_decl_1271_);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1324_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1325_);
v___x_1318_ = v_c_1264_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v_c_1264_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_fst_1291_);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_decl_1271_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_fst_1291_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v___y_1309_ = v___x_1321_;
goto v___jp_1308_;
}
}
}
else
{
lean_dec(v_fst_1291_);
v___y_1309_ = v_c_1264_;
goto v___jp_1308_;
}
}
case 1:
{
lean_object* v___x_1326_; 
lean_del_object(v___x_1298_);
lean_del_object(v___x_1293_);
lean_dec(v_snd_1289_);
v___x_1326_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1262_, v_info_1263_, v_fst_1291_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec_ref(v_info_1263_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1350_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1350_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1350_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___y_1332_; size_t v___x_1338_; size_t v___x_1339_; uint8_t v___x_1340_; 
v___x_1338_ = lean_ptr_addr(v_k_1272_);
v___x_1339_ = lean_ptr_addr(v_a_1327_);
v___x_1340_ = lean_usize_dec_eq(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_inc_ref(v_decl_1271_);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; lean_object* v_unused_1349_; 
v_unused_1348_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1349_);
v___x_1342_ = v_c_1264_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v_c_1264_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_a_1327_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_decl_1271_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_a_1327_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
v___y_1332_ = v___x_1345_;
goto v___jp_1331_;
}
}
}
else
{
lean_dec(v_a_1327_);
v___y_1332_ = v_c_1264_;
goto v___jp_1331_;
}
v___jp_1331_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1333_ = lean_box(v___x_1276_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___y_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1334_);
v___x_1336_ = v___x_1329_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref_known(v_c_1264_, 2);
v_a_1351_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1326_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1326_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
default: 
{
size_t v___x_1359_; size_t v___x_1360_; uint8_t v___x_1361_; 
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1359_ = lean_ptr_addr(v_k_1272_);
v___x_1360_ = lean_ptr_addr(v_fst_1291_);
v___x_1361_ = lean_usize_dec_eq(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_inc_ref(v_decl_1271_);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1369_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1370_);
v___x_1363_ = v_c_1264_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v_c_1264_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_fst_1291_);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_decl_1271_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_fst_1291_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
v___y_1301_ = v___x_1366_;
goto v___jp_1300_;
}
}
}
else
{
lean_dec(v_fst_1291_);
v___y_1301_ = v_c_1264_;
goto v___jp_1300_;
}
}
}
v___jp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___y_1301_);
v___x_1303_ = v___x_1293_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___y_1301_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_snd_1289_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1303_);
v___x_1305_ = v___x_1298_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_box(v___x_1276_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___y_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1293_);
lean_dec(v_fst_1291_);
lean_dec(v_snd_1289_);
lean_dec_ref_known(v_c_1264_, 2);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_a_1372_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1295_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1295_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v_fst_1382_; size_t v___x_1383_; size_t v___x_1384_; uint8_t v___x_1385_; 
lean_dec_ref(v_instr_1274_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_fst_1382_ = lean_ctor_get(v_a_1278_, 0);
lean_inc(v_fst_1382_);
lean_dec(v_a_1278_);
v___x_1383_ = lean_ptr_addr(v_k_1272_);
v___x_1384_ = lean_ptr_addr(v_fst_1382_);
v___x_1385_ = lean_usize_dec_eq(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_inc_ref(v_decl_1271_);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1393_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1394_);
v___x_1387_ = v_c_1264_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v_c_1264_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v_fst_1382_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_decl_1271_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_fst_1382_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
v___y_1283_ = v___x_1390_;
goto v___jp_1282_;
}
}
}
else
{
lean_dec(v_fst_1382_);
v___y_1283_ = v_c_1264_;
goto v___jp_1282_;
}
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1284_ = lean_box(v___x_1276_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___y_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1285_);
v___x_1287_ = v___x_1280_;
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
}
}
else
{
lean_dec_ref(v_instr_1274_);
lean_dec_ref_known(v_c_1264_, 2);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
return v___x_1277_;
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_instr_1274_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1396_ = lean_box(v___x_1276_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_c_1264_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
case 2:
{
lean_object* v_decl_1399_; lean_object* v_k_1400_; lean_object* v___x_1401_; 
v_decl_1399_ = lean_ctor_get(v_c_1264_, 0);
v_k_1400_ = lean_ctor_get(v_c_1264_, 1);
lean_inc_ref(v_k_1400_);
lean_inc_ref(v_info_1263_);
lean_inc(v_x_1262_);
v___x_1401_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1262_, v_info_1263_, v_k_1400_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v_params_1405_; lean_object* v_type_1406_; lean_object* v_value_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v_fst_1403_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_fst_1403_);
v_snd_1404_ = lean_ctor_get(v_a_1402_, 1);
lean_inc(v_snd_1404_);
lean_dec(v_a_1402_);
v_params_1405_ = lean_ctor_get(v_decl_1399_, 2);
v_type_1406_ = lean_ctor_get(v_decl_1399_, 3);
v_value_1407_ = lean_ctor_get(v_decl_1399_, 4);
v___x_1408_ = 1;
lean_inc_ref(v_value_1407_);
v___x_1409_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1262_, v_info_1263_, v_value_1407_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1461_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v_fst_1411_ = lean_ctor_get(v_a_1410_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_a_1410_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_a_1410_, 1);
lean_dec(v_unused_1462_);
v___x_1413_ = v_a_1410_;
v_isShared_1414_ = v_isSharedCheck_1461_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fst_1411_);
lean_dec(v_a_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1461_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; 
lean_inc_ref(v_params_1405_);
lean_inc_ref(v_type_1406_);
lean_inc_ref(v_decl_1399_);
v___x_1415_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1408_, v_decl_1399_, v_type_1406_, v_params_1405_, v_fst_1411_, v_a_1267_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1452_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1452_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1452_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___y_1421_; size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_ptr_addr(v_k_1400_);
v___x_1429_ = lean_ptr_addr(v_fst_1403_);
v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; lean_object* v_unused_1439_; 
v_unused_1438_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1439_);
v___x_1432_ = v_c_1264_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_dec(v_c_1264_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v_fst_1403_);
lean_ctor_set(v___x_1432_, 0, v_a_1416_);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_fst_1403_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v___y_1421_ = v___x_1435_;
goto v___jp_1420_;
}
}
}
else
{
size_t v___x_1440_; size_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_ptr_addr(v_decl_1399_);
v___x_1441_ = lean_ptr_addr(v_a_1416_);
v___x_1442_ = lean_usize_dec_eq(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; 
v_unused_1450_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1451_);
v___x_1444_ = v_c_1264_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_c_1264_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_fst_1403_);
lean_ctor_set(v___x_1444_, 0, v_a_1416_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1416_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_fst_1403_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
v___y_1421_ = v___x_1447_;
goto v___jp_1420_;
}
}
}
else
{
lean_dec(v_a_1416_);
lean_dec(v_fst_1403_);
v___y_1421_ = v_c_1264_;
goto v___jp_1420_;
}
}
v___jp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v_snd_1404_);
lean_ctor_set(v___x_1413_, 0, v___y_1421_);
v___x_1423_ = v___x_1413_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___y_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_snd_1404_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1423_);
v___x_1425_ = v___x_1418_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_del_object(v___x_1413_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_dec_ref_known(v_c_1264_, 2);
v_a_1453_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1415_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1415_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
else
{
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_dec_ref_known(v_c_1264_, 2);
return v___x_1409_;
}
}
else
{
lean_dec_ref_known(v_c_1264_, 2);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
return v___x_1401_;
}
}
case 3:
{
lean_object* v___x_1463_; 
lean_dec_ref(v_info_1263_);
lean_inc_ref(v_c_1264_);
v___x_1463_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1264_, v_x_1262_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_c_1264_);
lean_ctor_set(v___x_1468_, 1, v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref_known(v_c_1264_, 2);
v_a_1473_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1463_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1463_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
case 4:
{
lean_object* v_cases_1481_; lean_object* v___x_1482_; 
v_cases_1481_ = lean_ctor_get(v_c_1264_, 0);
lean_inc_ref(v_cases_1481_);
lean_inc(v_x_1262_);
lean_inc_ref(v_c_1264_);
v___x_1482_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1264_, v_x_1262_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1535_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1535_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1535_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_unbox(v_a_1483_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec_ref(v_cases_1481_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_c_1264_);
lean_ctor_set(v___x_1488_, 1, v_a_1483_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1488_);
v___x_1490_ = v___x_1485_;
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
else
{
lean_object* v_typeName_1492_; lean_object* v_resultType_1493_; lean_object* v_discr_1494_; lean_object* v_alts_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1534_; 
lean_del_object(v___x_1485_);
v_typeName_1492_ = lean_ctor_get(v_cases_1481_, 0);
v_resultType_1493_ = lean_ctor_get(v_cases_1481_, 1);
v_discr_1494_ = lean_ctor_get(v_cases_1481_, 2);
v_alts_1495_ = lean_ctor_get(v_cases_1481_, 3);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_cases_1481_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1497_ = v_cases_1481_;
v_isShared_1498_ = v_isSharedCheck_1534_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_alts_1495_);
lean_inc(v_discr_1494_);
lean_inc(v_resultType_1493_);
lean_inc(v_typeName_1492_);
lean_dec(v_cases_1481_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1534_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1495_);
v___x_1500_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1262_, v_info_1263_, v___x_1499_, v_alts_1495_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1525_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1525_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1525_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___y_1506_; size_t v___x_1511_; size_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = lean_ptr_addr(v_alts_1495_);
lean_dec_ref(v_alts_1495_);
v___x_1512_ = lean_ptr_addr(v_a_1501_);
v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1524_);
v___x_1515_ = v_c_1264_;
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_c_1264_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 3, v_a_1501_);
v___x_1518_ = v___x_1497_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_typeName_1492_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_resultType_1493_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_discr_1494_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_a_1501_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
v___y_1506_ = v___x_1520_;
goto v___jp_1505_;
}
}
}
}
else
{
lean_dec(v_a_1501_);
lean_del_object(v___x_1497_);
lean_dec(v_discr_1494_);
lean_dec_ref(v_resultType_1493_);
lean_dec(v_typeName_1492_);
v___y_1506_ = v_c_1264_;
goto v___jp_1505_;
}
v___jp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1506_);
lean_ctor_set(v___x_1507_, 1, v_a_1483_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1507_);
v___x_1509_ = v___x_1503_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_del_object(v___x_1497_);
lean_dec_ref(v_alts_1495_);
lean_dec(v_discr_1494_);
lean_dec_ref(v_resultType_1493_);
lean_dec(v_typeName_1492_);
lean_dec(v_a_1483_);
lean_dec_ref_known(v_c_1264_, 1);
v_a_1526_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1500_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1500_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v_cases_1481_);
lean_dec_ref_known(v_c_1264_, 1);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_a_1536_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1482_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1482_);
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
case 5:
{
lean_object* v___x_1544_; 
lean_dec_ref(v_info_1263_);
lean_inc_ref(v_c_1264_);
v___x_1544_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1264_, v_x_1262_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_c_1264_);
lean_ctor_set(v___x_1549_, 1, v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref_known(v_c_1264_, 1);
v_a_1554_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1544_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1544_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
case 6:
{
lean_object* v___x_1562_; 
lean_dec_ref(v_info_1263_);
lean_inc_ref(v_c_1264_);
v___x_1562_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1264_, v_x_1262_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_c_1264_);
lean_ctor_set(v___x_1567_, 1, v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref_known(v_c_1264_, 1);
v_a_1572_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1562_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1562_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_1580_; lean_object* v_i_1581_; lean_object* v_y_1582_; lean_object* v_k_1583_; uint8_t v___x_1584_; lean_object* v_instr_1585_; uint8_t v___x_1586_; uint8_t v___x_1587_; 
v_fvarId_1580_ = lean_ctor_get(v_c_1264_, 0);
v_i_1581_ = lean_ctor_get(v_c_1264_, 1);
v_y_1582_ = lean_ctor_get(v_c_1264_, 2);
v_k_1583_ = lean_ctor_get(v_c_1264_, 3);
v___x_1584_ = 1;
v_instr_1585_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1584_, v_c_1264_);
lean_inc(v_x_1262_);
v___x_1586_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1585_, v_x_1262_);
v___x_1587_ = 1;
if (v___x_1586_ == 0)
{
lean_object* v___x_1588_; 
lean_inc_ref(v_k_1583_);
lean_inc_ref(v_info_1263_);
lean_inc(v_x_1262_);
v___x_1588_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1262_, v_info_1263_, v_k_1583_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1714_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1714_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1714_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___y_1594_; lean_object* v_snd_1600_; uint8_t v___x_1601_; 
v_snd_1600_ = lean_ctor_get(v_a_1589_, 1);
v___x_1601_ = lean_unbox(v_snd_1600_);
if (v___x_1601_ == 0)
{
lean_object* v_fst_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1697_; 
lean_inc(v_snd_1600_);
lean_del_object(v___x_1591_);
v_fst_1602_ = lean_ctor_get(v_a_1589_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_a_1589_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_a_1589_, 1);
lean_dec(v_unused_1698_);
v___x_1604_ = v_a_1589_;
v_isShared_1605_ = v_isSharedCheck_1697_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_fst_1602_);
lean_dec(v_a_1589_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1697_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; 
lean_inc(v_x_1262_);
v___x_1606_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1585_, v_x_1262_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1688_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1688_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1688_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___y_1612_; lean_object* v___y_1620_; uint8_t v___x_1624_; 
v___x_1624_ = lean_unbox(v_a_1607_);
lean_dec(v_a_1607_);
switch(v___x_1624_)
{
case 0:
{
size_t v___x_1625_; size_t v___x_1626_; uint8_t v___x_1627_; 
lean_del_object(v___x_1609_);
lean_del_object(v___x_1604_);
lean_dec(v_snd_1600_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1625_ = lean_ptr_addr(v_k_1583_);
v___x_1626_ = lean_ptr_addr(v_fst_1602_);
v___x_1627_ = lean_usize_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_inc(v_y_1582_);
lean_inc(v_i_1581_);
lean_inc(v_fvarId_1580_);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1635_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1638_);
v___x_1629_ = v_c_1264_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v_c_1264_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 3, v_fst_1602_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fvarId_1580_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_i_1581_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_y_1582_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_fst_1602_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
v___y_1620_ = v___x_1632_;
goto v___jp_1619_;
}
}
}
else
{
lean_dec(v_fst_1602_);
v___y_1620_ = v_c_1264_;
goto v___jp_1619_;
}
}
case 1:
{
lean_object* v___x_1639_; 
lean_del_object(v___x_1609_);
lean_del_object(v___x_1604_);
lean_dec(v_snd_1600_);
v___x_1639_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1262_, v_info_1263_, v_fst_1602_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec_ref(v_info_1263_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1665_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1665_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1665_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___y_1645_; size_t v___x_1651_; size_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_ptr_addr(v_k_1583_);
v___x_1652_ = lean_ptr_addr(v_a_1640_);
v___x_1653_ = lean_usize_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_inc(v_y_1582_);
lean_inc(v_i_1581_);
lean_inc(v_fvarId_1580_);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; lean_object* v_unused_1664_; 
v_unused_1661_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1664_);
v___x_1655_ = v_c_1264_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_c_1264_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v_a_1640_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_fvarId_1580_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_i_1581_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_y_1582_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v_a_1640_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v___y_1645_ = v___x_1658_;
goto v___jp_1644_;
}
}
}
else
{
lean_dec(v_a_1640_);
v___y_1645_ = v_c_1264_;
goto v___jp_1644_;
}
v___jp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1646_ = lean_box(v___x_1587_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1647_);
v___x_1649_ = v___x_1642_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref_known(v_c_1264_, 4);
v_a_1666_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1639_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1639_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
default: 
{
size_t v___x_1674_; size_t v___x_1675_; uint8_t v___x_1676_; 
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1674_ = lean_ptr_addr(v_k_1583_);
v___x_1675_ = lean_ptr_addr(v_fst_1602_);
v___x_1676_ = lean_usize_dec_eq(v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_inc(v_y_1582_);
lean_inc(v_i_1581_);
lean_inc(v_fvarId_1580_);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1684_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1687_);
v___x_1678_ = v_c_1264_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v_c_1264_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 3, v_fst_1602_);
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_fvarId_1580_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_i_1581_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_y_1582_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_fst_1602_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
v___y_1612_ = v___x_1681_;
goto v___jp_1611_;
}
}
}
else
{
lean_dec(v_fst_1602_);
v___y_1612_ = v_c_1264_;
goto v___jp_1611_;
}
}
}
v___jp_1611_:
{
lean_object* v___x_1614_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___y_1612_);
v___x_1614_ = v___x_1604_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___y_1612_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_snd_1600_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1614_);
v___x_1616_ = v___x_1609_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
v___jp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = lean_box(v___x_1587_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___y_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1604_);
lean_dec(v_fst_1602_);
lean_dec(v_snd_1600_);
lean_dec_ref_known(v_c_1264_, 4);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_a_1689_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1606_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1606_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_fst_1699_; size_t v___x_1700_; size_t v___x_1701_; uint8_t v___x_1702_; 
lean_dec_ref(v_instr_1585_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_fst_1699_ = lean_ctor_get(v_a_1589_, 0);
lean_inc(v_fst_1699_);
lean_dec(v_a_1589_);
v___x_1700_ = lean_ptr_addr(v_k_1583_);
v___x_1701_ = lean_ptr_addr(v_fst_1699_);
v___x_1702_ = lean_usize_dec_eq(v___x_1700_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_inc(v_y_1582_);
lean_inc(v_i_1581_);
lean_inc(v_fvarId_1580_);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; lean_object* v_unused_1713_; 
v_unused_1710_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1713_);
v___x_1704_ = v_c_1264_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v_c_1264_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 3, v_fst_1699_);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_fvarId_1580_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_i_1581_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_y_1582_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_fst_1699_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
v___y_1594_ = v___x_1707_;
goto v___jp_1593_;
}
}
}
else
{
lean_dec(v_fst_1699_);
v___y_1594_ = v_c_1264_;
goto v___jp_1593_;
}
}
v___jp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_box(v___x_1587_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1596_);
v___x_1598_ = v___x_1591_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1585_);
lean_dec_ref_known(v_c_1264_, 4);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
return v___x_1588_;
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v_instr_1585_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1715_ = lean_box(v___x_1587_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_c_1264_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
case 9:
{
lean_object* v_fvarId_1718_; lean_object* v_i_1719_; lean_object* v_offset_1720_; lean_object* v_y_1721_; lean_object* v_ty_1722_; lean_object* v_k_1723_; uint8_t v___x_1724_; lean_object* v_instr_1725_; uint8_t v___x_1726_; uint8_t v___x_1727_; 
v_fvarId_1718_ = lean_ctor_get(v_c_1264_, 0);
v_i_1719_ = lean_ctor_get(v_c_1264_, 1);
v_offset_1720_ = lean_ctor_get(v_c_1264_, 2);
v_y_1721_ = lean_ctor_get(v_c_1264_, 3);
v_ty_1722_ = lean_ctor_get(v_c_1264_, 4);
v_k_1723_ = lean_ctor_get(v_c_1264_, 5);
v___x_1724_ = 1;
v_instr_1725_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1724_, v_c_1264_);
lean_inc(v_x_1262_);
v___x_1726_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1725_, v_x_1262_);
v___x_1727_ = 1;
if (v___x_1726_ == 0)
{
lean_object* v___x_1728_; 
lean_inc_ref(v_k_1723_);
lean_inc_ref(v_info_1263_);
lean_inc(v_x_1262_);
v___x_1728_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1262_, v_info_1263_, v_k_1723_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1862_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1862_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1862_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___y_1734_; lean_object* v_snd_1740_; uint8_t v___x_1741_; 
v_snd_1740_ = lean_ctor_get(v_a_1729_, 1);
v___x_1741_ = lean_unbox(v_snd_1740_);
if (v___x_1741_ == 0)
{
lean_object* v_fst_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1843_; 
lean_inc(v_snd_1740_);
lean_del_object(v___x_1731_);
v_fst_1742_ = lean_ctor_get(v_a_1729_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_a_1729_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_a_1729_, 1);
lean_dec(v_unused_1844_);
v___x_1744_ = v_a_1729_;
v_isShared_1745_ = v_isSharedCheck_1843_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_fst_1742_);
lean_dec(v_a_1729_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1843_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; 
lean_inc(v_x_1262_);
v___x_1746_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1725_, v_x_1262_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1834_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1834_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1834_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___y_1752_; lean_object* v___y_1760_; uint8_t v___x_1764_; 
v___x_1764_ = lean_unbox(v_a_1747_);
lean_dec(v_a_1747_);
switch(v___x_1764_)
{
case 0:
{
size_t v___x_1765_; size_t v___x_1766_; uint8_t v___x_1767_; 
lean_del_object(v___x_1749_);
lean_del_object(v___x_1744_);
lean_dec(v_snd_1740_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1765_ = lean_ptr_addr(v_k_1723_);
v___x_1766_ = lean_ptr_addr(v_fst_1742_);
v___x_1767_ = lean_usize_dec_eq(v___x_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_inc_ref(v_ty_1722_);
lean_inc(v_y_1721_);
lean_inc(v_offset_1720_);
lean_inc(v_i_1719_);
lean_inc(v_fvarId_1718_);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; lean_object* v_unused_1780_; 
v_unused_1775_ = lean_ctor_get(v_c_1264_, 5);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_c_1264_, 4);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1780_);
v___x_1769_ = v_c_1264_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v_c_1264_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 5, v_fst_1742_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_fvarId_1718_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_i_1719_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v_offset_1720_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v_y_1721_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v_ty_1722_);
lean_ctor_set(v_reuseFailAlloc_1773_, 5, v_fst_1742_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v___y_1760_ = v___x_1772_;
goto v___jp_1759_;
}
}
}
else
{
lean_dec(v_fst_1742_);
v___y_1760_ = v_c_1264_;
goto v___jp_1759_;
}
}
case 1:
{
lean_object* v___x_1781_; 
lean_del_object(v___x_1749_);
lean_del_object(v___x_1744_);
lean_dec(v_snd_1740_);
v___x_1781_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1262_, v_info_1263_, v_fst_1742_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec_ref(v_info_1263_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1809_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1809_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1809_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___y_1787_; size_t v___x_1793_; size_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = lean_ptr_addr(v_k_1723_);
v___x_1794_ = lean_ptr_addr(v_a_1782_);
v___x_1795_ = lean_usize_dec_eq(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_inc_ref(v_ty_1722_);
lean_inc(v_y_1721_);
lean_inc(v_offset_1720_);
lean_inc(v_i_1719_);
lean_inc(v_fvarId_1718_);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; lean_object* v_unused_1808_; 
v_unused_1803_ = lean_ctor_get(v_c_1264_, 5);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_c_1264_, 4);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1808_);
v___x_1797_ = v_c_1264_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_dec(v_c_1264_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 5, v_a_1782_);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_fvarId_1718_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_i_1719_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_offset_1720_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_y_1721_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_ty_1722_);
lean_ctor_set(v_reuseFailAlloc_1801_, 5, v_a_1782_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
v___y_1787_ = v___x_1800_;
goto v___jp_1786_;
}
}
}
else
{
lean_dec(v_a_1782_);
v___y_1787_ = v_c_1264_;
goto v___jp_1786_;
}
v___jp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1788_ = lean_box(v___x_1727_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___y_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1789_);
v___x_1791_ = v___x_1784_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec_ref_known(v_c_1264_, 6);
v_a_1810_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1781_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1781_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
default: 
{
size_t v___x_1818_; size_t v___x_1819_; uint8_t v___x_1820_; 
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1818_ = lean_ptr_addr(v_k_1723_);
v___x_1819_ = lean_ptr_addr(v_fst_1742_);
v___x_1820_ = lean_usize_dec_eq(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_inc_ref(v_ty_1722_);
lean_inc(v_y_1721_);
lean_inc(v_offset_1720_);
lean_inc(v_i_1719_);
lean_inc(v_fvarId_1718_);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; lean_object* v_unused_1829_; lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; 
v_unused_1828_ = lean_ctor_get(v_c_1264_, 5);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_c_1264_, 4);
lean_dec(v_unused_1829_);
v_unused_1830_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1833_);
v___x_1822_ = v_c_1264_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v_c_1264_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 5, v_fst_1742_);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fvarId_1718_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_i_1719_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_offset_1720_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v_y_1721_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v_ty_1722_);
lean_ctor_set(v_reuseFailAlloc_1826_, 5, v_fst_1742_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1752_ = v___x_1825_;
goto v___jp_1751_;
}
}
}
else
{
lean_dec(v_fst_1742_);
v___y_1752_ = v_c_1264_;
goto v___jp_1751_;
}
}
}
v___jp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___y_1752_);
v___x_1754_ = v___x_1744_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___y_1752_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_snd_1740_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1754_);
v___x_1756_ = v___x_1749_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
v___jp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_box(v___x_1727_);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___y_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_del_object(v___x_1744_);
lean_dec(v_fst_1742_);
lean_dec(v_snd_1740_);
lean_dec_ref_known(v_c_1264_, 6);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_a_1835_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1746_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1746_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
else
{
lean_object* v_fst_1845_; size_t v___x_1846_; size_t v___x_1847_; uint8_t v___x_1848_; 
lean_dec_ref(v_instr_1725_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v_fst_1845_ = lean_ctor_get(v_a_1729_, 0);
lean_inc(v_fst_1845_);
lean_dec(v_a_1729_);
v___x_1846_ = lean_ptr_addr(v_k_1723_);
v___x_1847_ = lean_ptr_addr(v_fst_1845_);
v___x_1848_ = lean_usize_dec_eq(v___x_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_inc_ref(v_ty_1722_);
lean_inc(v_y_1721_);
lean_inc(v_offset_1720_);
lean_inc(v_i_1719_);
lean_inc(v_fvarId_1718_);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_c_1264_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; 
v_unused_1856_ = lean_ctor_get(v_c_1264_, 5);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_c_1264_, 4);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_c_1264_, 3);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_c_1264_, 2);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_c_1264_, 1);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_c_1264_, 0);
lean_dec(v_unused_1861_);
v___x_1850_ = v_c_1264_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v_c_1264_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 5, v_fst_1845_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_fvarId_1718_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_i_1719_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_offset_1720_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_y_1721_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_ty_1722_);
lean_ctor_set(v_reuseFailAlloc_1854_, 5, v_fst_1845_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
v___y_1734_ = v___x_1853_;
goto v___jp_1733_;
}
}
}
else
{
lean_dec(v_fst_1845_);
v___y_1734_ = v_c_1264_;
goto v___jp_1733_;
}
}
v___jp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1735_ = lean_box(v___x_1727_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___y_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1736_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1725_);
lean_dec_ref_known(v_c_1264_, 6);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
return v___x_1728_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec_ref(v_instr_1725_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1863_ = lean_box(v___x_1727_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_c_1264_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
default: 
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec_ref(v_c_1264_);
lean_dec_ref(v_info_1263_);
lean_dec(v_x_1262_);
v___x_1866_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
v___x_1867_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_1866_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object* v_x_1868_, lean_object* v_info_1869_, lean_object* v_c_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___x_1877_; 
lean_inc_ref(v_info_1869_);
lean_inc(v_x_1868_);
v___x_1877_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1868_, v_info_1869_, v_c_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1890_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1890_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1890_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_snd_1882_; uint8_t v___x_1883_; 
v_snd_1882_ = lean_ctor_get(v_a_1878_, 1);
v___x_1883_ = lean_unbox(v_snd_1882_);
if (v___x_1883_ == 0)
{
lean_object* v_fst_1884_; lean_object* v___x_1885_; 
lean_del_object(v___x_1880_);
v_fst_1884_ = lean_ctor_get(v_a_1878_, 0);
lean_inc(v_fst_1884_);
lean_dec(v_a_1878_);
v___x_1885_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1868_, v_info_1869_, v_fst_1884_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec_ref(v_info_1869_);
return v___x_1885_;
}
else
{
lean_object* v_fst_1886_; lean_object* v___x_1888_; 
lean_dec_ref(v_info_1869_);
lean_dec(v_x_1868_);
v_fst_1886_ = lean_ctor_get(v_a_1878_, 0);
lean_inc(v_fst_1886_);
lean_dec(v_a_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_fst_1886_);
v___x_1888_ = v___x_1880_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_fst_1886_);
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
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v_info_1869_);
lean_dec(v_x_1868_);
v_a_1891_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1877_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1877_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object* v_x_1899_, lean_object* v_info_1900_, lean_object* v_i_1901_, lean_object* v_as_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1899_, v_info_1900_, v_i_1901_, v_as_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object* v_x_1910_, lean_object* v_info_1911_, lean_object* v_c_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1910_, v_info_1911_, v_c_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec_ref(v_a_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t v_pu_1920_, lean_object* v_alt_1921_, lean_object* v_f_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1921_, v_f_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object* v_pu_1930_, lean_object* v_alt_1931_, lean_object* v_f_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v_pu_boxed_1939_; lean_object* v_res_1940_; 
v_pu_boxed_1939_ = lean_unbox(v_pu_1930_);
v_res_1940_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_boxed_1939_, v_alt_1931_, v_f_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_toApplicative_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1984_; 
v___x_1948_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_1949_ = l_StateRefT_x27_instMonad___redArg(v___x_1948_);
v_toApplicative_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1949_, 1);
lean_dec(v_unused_1985_);
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1984_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_toApplicative_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1984_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_toFunctor_1954_; lean_object* v_toSeq_1955_; lean_object* v_toSeqLeft_1956_; lean_object* v_toSeqRight_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1982_; 
v_toFunctor_1954_ = lean_ctor_get(v_toApplicative_1950_, 0);
v_toSeq_1955_ = lean_ctor_get(v_toApplicative_1950_, 2);
v_toSeqLeft_1956_ = lean_ctor_get(v_toApplicative_1950_, 3);
v_toSeqRight_1957_ = lean_ctor_get(v_toApplicative_1950_, 4);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_toApplicative_1950_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_toApplicative_1950_, 1);
lean_dec(v_unused_1983_);
v___x_1959_ = v_toApplicative_1950_;
v_isShared_1960_ = v_isSharedCheck_1982_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_toSeqRight_1957_);
lean_inc(v_toSeqLeft_1956_);
lean_inc(v_toSeq_1955_);
lean_inc(v_toFunctor_1954_);
lean_dec(v_toApplicative_1950_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1982_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___f_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___f_1967_; lean_object* v___f_1968_; lean_object* v___x_1970_; 
v___f_1961_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_1962_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1954_);
v___f_1963_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1963_, 0, v_toFunctor_1954_);
v___f_1964_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1964_, 0, v_toFunctor_1954_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___f_1963_);
lean_ctor_set(v___x_1965_, 1, v___f_1964_);
v___f_1966_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1966_, 0, v_toSeqRight_1957_);
v___f_1967_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1967_, 0, v_toSeqLeft_1956_);
v___f_1968_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1968_, 0, v_toSeq_1955_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 4, v___f_1966_);
lean_ctor_set(v___x_1959_, 3, v___f_1967_);
lean_ctor_set(v___x_1959_, 2, v___f_1968_);
lean_ctor_set(v___x_1959_, 1, v___f_1961_);
lean_ctor_set(v___x_1959_, 0, v___x_1965_);
v___x_1970_ = v___x_1959_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___f_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v___f_1968_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v___f_1967_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___f_1966_);
v___x_1970_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v___f_1962_);
lean_ctor_set(v___x_1952_, 0, v___x_1970_);
v___x_1972_ = v___x_1952_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___f_1962_);
v___x_1972_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___x_5524__overap_1978_; lean_object* v___x_1979_; 
v___x_1973_ = l_StateRefT_x27_instMonad___redArg(v___x_1972_);
v___x_1974_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_1975_ = l_instInhabitedOfMonad___redArg(v___x_1973_, v___x_1974_);
v___f_1976_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1976_, 0, v___x_1975_);
v___f_1977_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1977_, 0, v___f_1976_);
v___x_5524__overap_1978_ = lean_panic_fn_borrowed(v___f_1977_, v_msg_1941_);
lean_dec_ref(v___f_1977_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc_ref(v___y_1942_);
v___x_1979_ = lean_apply_6(v___x_5524__overap_1978_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, lean_box(0));
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object* v_msg_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object* v_a_1994_, lean_object* v_fallback_1995_, lean_object* v_x_1996_){
_start:
{
if (lean_obj_tag(v_x_1996_) == 0)
{
lean_inc(v_fallback_1995_);
return v_fallback_1995_;
}
else
{
lean_object* v_key_1997_; lean_object* v_value_1998_; lean_object* v_tail_1999_; uint8_t v___x_2000_; 
v_key_1997_ = lean_ctor_get(v_x_1996_, 0);
v_value_1998_ = lean_ctor_get(v_x_1996_, 1);
v_tail_1999_ = lean_ctor_get(v_x_1996_, 2);
v___x_2000_ = l_Lean_instBEqFVarId_beq(v_key_1997_, v_a_1994_);
if (v___x_2000_ == 0)
{
v_x_1996_ = v_tail_1999_;
goto _start;
}
else
{
lean_inc(v_value_1998_);
return v_value_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object* v_a_2002_, lean_object* v_fallback_2003_, lean_object* v_x_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2002_, v_fallback_2003_, v_x_2004_);
lean_dec(v_x_2004_);
lean_dec(v_fallback_2003_);
lean_dec(v_a_2002_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object* v_m_2006_, lean_object* v_a_2007_, lean_object* v_fallback_2008_){
_start:
{
lean_object* v_buckets_2009_; lean_object* v___x_2010_; uint64_t v___x_2011_; uint64_t v___x_2012_; uint64_t v___x_2013_; uint64_t v_fold_2014_; uint64_t v___x_2015_; uint64_t v___x_2016_; uint64_t v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_buckets_2009_ = lean_ctor_get(v_m_2006_, 1);
v___x_2010_ = lean_array_get_size(v_buckets_2009_);
v___x_2011_ = l_Lean_instHashableFVarId_hash(v_a_2007_);
v___x_2012_ = 32ULL;
v___x_2013_ = lean_uint64_shift_right(v___x_2011_, v___x_2012_);
v_fold_2014_ = lean_uint64_xor(v___x_2011_, v___x_2013_);
v___x_2015_ = 16ULL;
v___x_2016_ = lean_uint64_shift_right(v_fold_2014_, v___x_2015_);
v___x_2017_ = lean_uint64_xor(v_fold_2014_, v___x_2016_);
v___x_2018_ = lean_uint64_to_usize(v___x_2017_);
v___x_2019_ = lean_usize_of_nat(v___x_2010_);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_sub(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_usize_land(v___x_2018_, v___x_2021_);
v___x_2023_ = lean_array_uget_borrowed(v_buckets_2009_, v___x_2022_);
v___x_2024_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2007_, v_fallback_2008_, v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object* v_m_2025_, lean_object* v_a_2026_, lean_object* v_fallback_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2025_, v_a_2026_, v_fallback_2027_);
lean_dec(v_fallback_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_m_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
lean_object* v_ks_2033_; lean_object* v_vs_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2058_; 
v_ks_2033_ = lean_ctor_get(v_x_2029_, 0);
v_vs_2034_ = lean_ctor_get(v_x_2029_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2029_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2036_ = v_x_2029_;
v_isShared_2037_ = v_isSharedCheck_2058_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_vs_2034_);
lean_inc(v_ks_2033_);
lean_dec(v_x_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2058_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = lean_array_get_size(v_ks_2033_);
v___x_2039_ = lean_nat_dec_lt(v_x_2030_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
lean_dec(v_x_2030_);
v___x_2040_ = lean_array_push(v_ks_2033_, v_x_2031_);
v___x_2041_ = lean_array_push(v_vs_2034_, v_x_2032_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2041_);
lean_ctor_set(v___x_2036_, 0, v___x_2040_);
v___x_2043_ = v___x_2036_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
else
{
lean_object* v_k_x27_2045_; uint8_t v___x_2046_; 
v_k_x27_2045_ = lean_array_fget_borrowed(v_ks_2033_, v_x_2030_);
v___x_2046_ = l_Lean_instBEqFVarId_beq(v_x_2031_, v_k_x27_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2048_; 
if (v_isShared_2037_ == 0)
{
v___x_2048_ = v___x_2036_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_ks_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_vs_2034_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_x_2030_, v___x_2049_);
lean_dec(v_x_2030_);
v_x_2029_ = v___x_2048_;
v_x_2030_ = v___x_2050_;
goto _start;
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2053_ = lean_array_fset(v_ks_2033_, v_x_2030_, v_x_2031_);
v___x_2054_ = lean_array_fset(v_vs_2034_, v_x_2030_, v_x_2032_);
lean_dec(v_x_2030_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2054_);
lean_ctor_set(v___x_2036_, 0, v___x_2053_);
v___x_2056_ = v___x_2036_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object* v_n_2059_, lean_object* v_k_2060_, lean_object* v_v_2061_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_n_2059_, v___x_2062_, v_k_2060_, v_v_2061_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object* v_x_2065_, size_t v_x_2066_, size_t v_x_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
if (lean_obj_tag(v_x_2065_) == 0)
{
lean_object* v_es_2070_; size_t v___x_2071_; size_t v___x_2072_; lean_object* v_j_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_es_2070_ = lean_ctor_get(v_x_2065_, 0);
v___x_2071_ = ((size_t)31ULL);
v___x_2072_ = lean_usize_land(v_x_2066_, v___x_2071_);
v_j_2073_ = lean_usize_to_nat(v___x_2072_);
v___x_2074_ = lean_array_get_size(v_es_2070_);
v___x_2075_ = lean_nat_dec_lt(v_j_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec(v_j_2073_);
lean_dec(v_x_2069_);
lean_dec(v_x_2068_);
return v_x_2065_;
}
else
{
lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2114_; 
lean_inc_ref(v_es_2070_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_x_2065_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v_x_2065_, 0);
lean_dec(v_unused_2115_);
v___x_2077_ = v_x_2065_;
v_isShared_2078_ = v_isSharedCheck_2114_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v_x_2065_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2114_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_v_2079_; lean_object* v___x_2080_; lean_object* v_xs_x27_2081_; lean_object* v___y_2083_; 
v_v_2079_ = lean_array_fget(v_es_2070_, v_j_2073_);
v___x_2080_ = lean_box(0);
v_xs_x27_2081_ = lean_array_fset(v_es_2070_, v_j_2073_, v___x_2080_);
switch(lean_obj_tag(v_v_2079_))
{
case 0:
{
lean_object* v_key_2088_; lean_object* v_val_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2099_; 
v_key_2088_ = lean_ctor_get(v_v_2079_, 0);
v_val_2089_ = lean_ctor_get(v_v_2079_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_v_2079_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2091_ = v_v_2079_;
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_val_2089_);
lean_inc(v_key_2088_);
lean_dec(v_v_2079_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
uint8_t v___x_2093_; 
v___x_2093_ = l_Lean_instBEqFVarId_beq(v_x_2068_, v_key_2088_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_del_object(v___x_2091_);
v___x_2094_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2088_, v_val_2089_, v_x_2068_, v_x_2069_);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
v___y_2083_ = v___x_2095_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2097_; 
lean_dec(v_val_2089_);
lean_dec(v_key_2088_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v_x_2069_);
lean_ctor_set(v___x_2091_, 0, v_x_2068_);
v___x_2097_ = v___x_2091_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_x_2068_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_x_2069_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v___y_2083_ = v___x_2097_;
goto v___jp_2082_;
}
}
}
}
case 1:
{
lean_object* v_node_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2112_; 
v_node_2100_ = lean_ctor_get(v_v_2079_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_v_2079_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2102_ = v_v_2079_;
v_isShared_2103_ = v_isSharedCheck_2112_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_node_2100_);
lean_dec(v_v_2079_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2112_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
size_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2104_ = ((size_t)5ULL);
v___x_2105_ = lean_usize_shift_right(v_x_2066_, v___x_2104_);
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_x_2067_, v___x_2106_);
v___x_2108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_2100_, v___x_2105_, v___x_2107_, v_x_2068_, v_x_2069_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2108_);
v___x_2110_ = v___x_2102_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
v___y_2083_ = v___x_2110_;
goto v___jp_2082_;
}
}
}
default: 
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v_x_2068_);
lean_ctor_set(v___x_2113_, 1, v_x_2069_);
v___y_2083_ = v___x_2113_;
goto v___jp_2082_;
}
}
v___jp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_array_fset(v_xs_x27_2081_, v_j_2073_, v___y_2083_);
lean_dec(v_j_2073_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2084_);
v___x_2086_ = v___x_2077_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
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
}
else
{
lean_object* v_ks_2116_; lean_object* v_vs_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2135_; 
v_ks_2116_ = lean_ctor_get(v_x_2065_, 0);
v_vs_2117_ = lean_ctor_get(v_x_2065_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_x_2065_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2119_ = v_x_2065_;
v_isShared_2120_ = v_isSharedCheck_2135_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_vs_2117_);
lean_inc(v_ks_2116_);
lean_dec(v_x_2065_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2135_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_ks_2116_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_vs_2117_);
v___x_2122_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v_newNode_2123_; size_t v___x_2124_; uint8_t v___x_2125_; 
v_newNode_2123_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_2122_, v_x_2068_, v_x_2069_);
v___x_2124_ = ((size_t)7ULL);
v___x_2125_ = lean_usize_dec_le(v___x_2124_, v_x_2067_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2126_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2123_);
v___x_2127_ = lean_unsigned_to_nat(4u);
v___x_2128_ = lean_nat_dec_lt(v___x_2126_, v___x_2127_);
lean_dec(v___x_2126_);
if (v___x_2128_ == 0)
{
lean_object* v_ks_2129_; lean_object* v_vs_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_ks_2129_ = lean_ctor_get(v_newNode_2123_, 0);
lean_inc_ref(v_ks_2129_);
v_vs_2130_ = lean_ctor_get(v_newNode_2123_, 1);
lean_inc_ref(v_vs_2130_);
lean_dec_ref(v_newNode_2123_);
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2133_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_2067_, v_ks_2129_, v_vs_2130_, v___x_2131_, v___x_2132_);
lean_dec_ref(v_vs_2130_);
lean_dec_ref(v_ks_2129_);
return v___x_2133_;
}
else
{
return v_newNode_2123_;
}
}
else
{
return v_newNode_2123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t v_depth_2136_, lean_object* v_keys_2137_, lean_object* v_vals_2138_, lean_object* v_i_2139_, lean_object* v_entries_2140_){
_start:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_array_get_size(v_keys_2137_);
v___x_2142_ = lean_nat_dec_lt(v_i_2139_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec(v_i_2139_);
return v_entries_2140_;
}
else
{
lean_object* v_k_2143_; lean_object* v_v_2144_; uint64_t v___x_2145_; size_t v_h_2146_; size_t v___x_2147_; lean_object* v___x_2148_; size_t v___x_2149_; size_t v___x_2150_; size_t v___x_2151_; size_t v_h_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_k_2143_ = lean_array_fget_borrowed(v_keys_2137_, v_i_2139_);
v_v_2144_ = lean_array_fget_borrowed(v_vals_2138_, v_i_2139_);
v___x_2145_ = l_Lean_instHashableFVarId_hash(v_k_2143_);
v_h_2146_ = lean_uint64_to_usize(v___x_2145_);
v___x_2147_ = ((size_t)5ULL);
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = ((size_t)1ULL);
v___x_2150_ = lean_usize_sub(v_depth_2136_, v___x_2149_);
v___x_2151_ = lean_usize_mul(v___x_2147_, v___x_2150_);
v_h_2152_ = lean_usize_shift_right(v_h_2146_, v___x_2151_);
v___x_2153_ = lean_nat_add(v_i_2139_, v___x_2148_);
lean_dec(v_i_2139_);
lean_inc(v_v_2144_);
lean_inc(v_k_2143_);
v___x_2154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2140_, v_h_2152_, v_depth_2136_, v_k_2143_, v_v_2144_);
v_i_2139_ = v___x_2153_;
v_entries_2140_ = v___x_2154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_2156_, lean_object* v_keys_2157_, lean_object* v_vals_2158_, lean_object* v_i_2159_, lean_object* v_entries_2160_){
_start:
{
size_t v_depth_boxed_2161_; lean_object* v_res_2162_; 
v_depth_boxed_2161_ = lean_unbox_usize(v_depth_2156_);
lean_dec(v_depth_2156_);
v_res_2162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2161_, v_keys_2157_, v_vals_2158_, v_i_2159_, v_entries_2160_);
lean_dec_ref(v_vals_2158_);
lean_dec_ref(v_keys_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
size_t v_x_6168__boxed_2168_; size_t v_x_6169__boxed_2169_; lean_object* v_res_2170_; 
v_x_6168__boxed_2168_ = lean_unbox_usize(v_x_2164_);
lean_dec(v_x_2164_);
v_x_6169__boxed_2169_ = lean_unbox_usize(v_x_2165_);
lean_dec(v_x_2165_);
v_res_2170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2163_, v_x_6168__boxed_2168_, v_x_6169__boxed_2169_, v_x_2166_, v_x_2167_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
uint64_t v___x_2174_; size_t v___x_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = l_Lean_instHashableFVarId_hash(v_x_2172_);
v___x_2175_ = lean_uint64_to_usize(v___x_2174_);
v___x_2176_ = ((size_t)1ULL);
v___x_2177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2171_, v___x_2175_, v___x_2176_, v_x_2172_, v_x_2173_);
return v___x_2177_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2178_, lean_object* v_i_2179_, lean_object* v_k_2180_){
_start:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_array_get_size(v_keys_2178_);
v___x_2182_ = lean_nat_dec_lt(v_i_2179_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_dec(v_i_2179_);
return v___x_2182_;
}
else
{
lean_object* v_k_x27_2183_; uint8_t v___x_2184_; 
v_k_x27_2183_ = lean_array_fget_borrowed(v_keys_2178_, v_i_2179_);
v___x_2184_ = l_Lean_instBEqFVarId_beq(v_k_2180_, v_k_x27_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_unsigned_to_nat(1u);
v___x_2186_ = lean_nat_add(v_i_2179_, v___x_2185_);
lean_dec(v_i_2179_);
v_i_2179_ = v___x_2186_;
goto _start;
}
else
{
lean_dec(v_i_2179_);
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2188_, lean_object* v_i_2189_, lean_object* v_k_2190_){
_start:
{
uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_res_2191_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2188_, v_i_2189_, v_k_2190_);
lean_dec(v_k_2190_);
lean_dec_ref(v_keys_2188_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2193_, size_t v_x_2194_, lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2193_) == 0)
{
lean_object* v_es_2196_; lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; lean_object* v_j_2200_; lean_object* v___x_2201_; 
v_es_2196_ = lean_ctor_get(v_x_2193_, 0);
v___x_2197_ = lean_box(2);
v___x_2198_ = ((size_t)31ULL);
v___x_2199_ = lean_usize_land(v_x_2194_, v___x_2198_);
v_j_2200_ = lean_usize_to_nat(v___x_2199_);
v___x_2201_ = lean_array_get_borrowed(v___x_2197_, v_es_2196_, v_j_2200_);
lean_dec(v_j_2200_);
switch(lean_obj_tag(v___x_2201_))
{
case 0:
{
lean_object* v_key_2202_; uint8_t v___x_2203_; 
v_key_2202_ = lean_ctor_get(v___x_2201_, 0);
v___x_2203_ = l_Lean_instBEqFVarId_beq(v_x_2195_, v_key_2202_);
return v___x_2203_;
}
case 1:
{
lean_object* v_node_2204_; size_t v___x_2205_; size_t v___x_2206_; 
v_node_2204_ = lean_ctor_get(v___x_2201_, 0);
v___x_2205_ = ((size_t)5ULL);
v___x_2206_ = lean_usize_shift_right(v_x_2194_, v___x_2205_);
v_x_2193_ = v_node_2204_;
v_x_2194_ = v___x_2206_;
goto _start;
}
default: 
{
uint8_t v___x_2208_; 
v___x_2208_ = 0;
return v___x_2208_;
}
}
}
else
{
lean_object* v_ks_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_ks_2209_ = lean_ctor_get(v_x_2193_, 0);
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2209_, v___x_2210_, v_x_2195_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_){
_start:
{
size_t v_x_6346__boxed_2215_; uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_x_6346__boxed_2215_ = lean_unbox_usize(v_x_2213_);
lean_dec(v_x_2213_);
v_res_2216_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2212_, v_x_6346__boxed_2215_, v_x_2214_);
lean_dec(v_x_2214_);
lean_dec_ref(v_x_2212_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
uint64_t v___x_2220_; size_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = l_Lean_instHashableFVarId_hash(v_x_2219_);
v___x_2221_ = lean_uint64_to_usize(v___x_2220_);
v___x_2222_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2218_, v___x_2221_, v_x_2219_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
uint8_t v_res_2225_; lean_object* v_r_2226_; 
v_res_2225_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2223_, v_x_2224_);
lean_dec(v_x_2224_);
lean_dec_ref(v_x_2223_);
v_r_2226_ = lean_box(v_res_2225_);
return v_r_2226_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2228_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2229_ = lean_unsigned_to_nat(59u);
v___x_2230_ = lean_unsigned_to_nat(281u);
v___x_2231_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2232_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2233_ = l_mkPanicMessageWithDecl(v___x_2232_, v___x_2231_, v___x_2230_, v___x_2229_, v___x_2228_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
switch(lean_obj_tag(v_c_2234_))
{
case 0:
{
lean_object* v_decl_2241_; lean_object* v_k_2242_; lean_object* v___x_2243_; 
v_decl_2241_ = lean_ctor_get(v_c_2234_, 0);
v_k_2242_ = lean_ctor_get(v_c_2234_, 1);
lean_inc_ref(v_k_2242_);
v___x_2243_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2242_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2266_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2266_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2266_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
size_t v___x_2248_; size_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2248_ = lean_ptr_addr(v_k_2242_);
v___x_2249_ = lean_ptr_addr(v_a_2244_);
v___x_2250_ = lean_usize_dec_eq(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2260_; 
lean_inc_ref(v_decl_2241_);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_c_2234_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; lean_object* v_unused_2262_; 
v_unused_2261_ = lean_ctor_get(v_c_2234_, 1);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_c_2234_, 0);
lean_dec(v_unused_2262_);
v___x_2252_ = v_c_2234_;
v_isShared_2253_ = v_isSharedCheck_2260_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v_c_2234_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2260_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v_a_2244_);
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_decl_2241_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_a_2244_);
v___x_2255_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2257_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2255_);
v___x_2257_ = v___x_2246_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v___x_2264_; 
lean_dec(v_a_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_c_2234_);
v___x_2264_ = v___x_2246_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_c_2234_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2234_, 2);
return v___x_2243_;
}
}
case 2:
{
lean_object* v_decl_2267_; lean_object* v_k_2268_; lean_object* v_params_2269_; lean_object* v_type_2270_; lean_object* v_value_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; 
v_decl_2267_ = lean_ctor_get(v_c_2234_, 0);
v_k_2268_ = lean_ctor_get(v_c_2234_, 1);
v_params_2269_ = lean_ctor_get(v_decl_2267_, 2);
v_type_2270_ = lean_ctor_get(v_decl_2267_, 3);
v_value_2271_ = lean_ctor_get(v_decl_2267_, 4);
v___x_2272_ = 1;
lean_inc_ref(v_value_2271_);
v___x_2273_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2271_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
lean_inc_ref(v_params_2269_);
lean_inc_ref(v_type_2270_);
lean_inc_ref(v_decl_2267_);
v___x_2275_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2272_, v_decl_2267_, v_type_2270_, v_params_2269_, v_a_2274_, v_a_2237_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
lean_inc_ref(v_k_2268_);
v___x_2277_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2268_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2315_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2315_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2315_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
size_t v___x_2282_; size_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2282_ = lean_ptr_addr(v_k_2268_);
v___x_2283_ = lean_ptr_addr(v_a_2278_);
v___x_2284_ = lean_usize_dec_eq(v___x_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2294_; 
v_isSharedCheck_2294_ = !lean_is_exclusive(v_c_2234_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2295_ = lean_ctor_get(v_c_2234_, 1);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_c_2234_, 0);
lean_dec(v_unused_2296_);
v___x_2286_ = v_c_2234_;
v_isShared_2287_ = v_isSharedCheck_2294_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v_c_2234_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2294_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 1, v_a_2278_);
lean_ctor_set(v___x_2286_, 0, v_a_2276_);
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2276_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_a_2278_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2289_);
v___x_2291_ = v___x_2280_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
size_t v___x_2297_; size_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = lean_ptr_addr(v_decl_2267_);
v___x_2298_ = lean_ptr_addr(v_a_2276_);
v___x_2299_ = lean_usize_dec_eq(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2309_; 
v_isSharedCheck_2309_ = !lean_is_exclusive(v_c_2234_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2310_ = lean_ctor_get(v_c_2234_, 1);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_c_2234_, 0);
lean_dec(v_unused_2311_);
v___x_2301_ = v_c_2234_;
v_isShared_2302_ = v_isSharedCheck_2309_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v_c_2234_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2309_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v_a_2278_);
lean_ctor_set(v___x_2301_, 0, v_a_2276_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2276_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_2278_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2304_);
v___x_2306_ = v___x_2280_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v___x_2313_; 
lean_dec(v_a_2278_);
lean_dec(v_a_2276_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v_c_2234_);
v___x_2313_ = v___x_2280_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_c_2234_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
lean_dec(v_a_2276_);
lean_dec_ref_known(v_c_2234_, 2);
return v___x_2277_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref_known(v_c_2234_, 2);
v_a_2316_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2275_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2275_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2234_, 2);
return v___x_2273_;
}
}
case 3:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_c_2234_);
return v___x_2324_;
}
case 4:
{
lean_object* v_cases_2325_; lean_object* v_typeName_2326_; lean_object* v_resultType_2327_; lean_object* v_discr_2328_; lean_object* v_alts_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2382_; 
v_cases_2325_ = lean_ctor_get(v_c_2234_, 0);
lean_inc_ref(v_cases_2325_);
v_typeName_2326_ = lean_ctor_get(v_cases_2325_, 0);
v_resultType_2327_ = lean_ctor_get(v_cases_2325_, 1);
v_discr_2328_ = lean_ctor_get(v_cases_2325_, 2);
v_alts_2329_ = lean_ctor_get(v_cases_2325_, 3);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_cases_2325_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2331_ = v_cases_2325_;
v_isShared_2332_ = v_isSharedCheck_2382_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_alts_2329_);
lean_inc(v_discr_2328_);
lean_inc(v_resultType_2327_);
lean_inc(v_typeName_2326_);
lean_dec(v_cases_2325_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2382_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_alreadyFound_2333_; uint8_t v_relaxedReuse_2334_; lean_object* v_ownedness_2335_; uint8_t v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; uint8_t v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; size_t v_sz_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v_alreadyFound_2333_ = lean_ctor_get(v_a_2235_, 0);
v_relaxedReuse_2334_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*2);
v_ownedness_2335_ = lean_ctor_get(v_a_2235_, 1);
v___x_2336_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2333_, v_discr_2328_);
v___x_2337_ = 0;
v___x_2338_ = lean_box(v___x_2337_);
v___x_2339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2335_, v_discr_2328_, v___x_2338_);
lean_dec(v___x_2338_);
v___x_2340_ = 1;
v___x_2341_ = lean_unbox(v___x_2339_);
lean_dec(v___x_2339_);
v___x_2342_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2341_, v___x_2340_);
v___x_2343_ = lean_box(0);
lean_inc_n(v_discr_2328_, 2);
lean_inc_ref(v_alreadyFound_2333_);
v___x_2344_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2333_, v_discr_2328_, v___x_2343_);
lean_inc_ref(v_ownedness_2335_);
v___x_2345_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v_ownedness_2335_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*2, v_relaxedReuse_2334_);
v_sz_2346_ = lean_array_size(v_alts_2329_);
v___x_2347_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2329_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2342_, v_discr_2328_, v___x_2336_, v_sz_2346_, v___x_2347_, v_alts_2329_, v___x_2345_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec_ref_known(v___x_2345_, 2);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2373_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2373_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2373_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
size_t v___x_2353_; size_t v___x_2354_; uint8_t v___x_2355_; 
v___x_2353_ = lean_ptr_addr(v_alts_2329_);
lean_dec_ref(v_alts_2329_);
v___x_2354_ = lean_ptr_addr(v_a_2349_);
v___x_2355_ = lean_usize_dec_eq(v___x_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2368_; 
v_isSharedCheck_2368_ = !lean_is_exclusive(v_c_2234_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v_c_2234_, 0);
lean_dec(v_unused_2369_);
v___x_2357_ = v_c_2234_;
v_isShared_2358_ = v_isSharedCheck_2368_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v_c_2234_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2368_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 3, v_a_2349_);
v___x_2360_ = v___x_2331_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_typeName_2326_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_resultType_2327_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_discr_2328_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v_a_2349_);
v___x_2360_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2360_);
v___x_2362_ = v___x_2357_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2362_);
v___x_2364_ = v___x_2351_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
else
{
lean_object* v___x_2371_; 
lean_dec(v_a_2349_);
lean_del_object(v___x_2331_);
lean_dec(v_discr_2328_);
lean_dec_ref(v_resultType_2327_);
lean_dec(v_typeName_2326_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_c_2234_);
v___x_2371_ = v___x_2351_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_c_2234_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_del_object(v___x_2331_);
lean_dec_ref(v_alts_2329_);
lean_dec(v_discr_2328_);
lean_dec_ref(v_resultType_2327_);
lean_dec(v_typeName_2326_);
lean_dec_ref_known(v_c_2234_, 1);
v_a_2374_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2348_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2348_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
case 5:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_c_2234_);
return v___x_2383_;
}
case 6:
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_c_2234_);
return v___x_2384_;
}
case 8:
{
lean_object* v_fvarId_2385_; lean_object* v_i_2386_; lean_object* v_y_2387_; lean_object* v_k_2388_; lean_object* v___x_2389_; 
v_fvarId_2385_ = lean_ctor_get(v_c_2234_, 0);
v_i_2386_ = lean_ctor_get(v_c_2234_, 1);
v_y_2387_ = lean_ctor_get(v_c_2234_, 2);
v_k_2388_ = lean_ctor_get(v_c_2234_, 3);
lean_inc_ref(v_k_2388_);
v___x_2389_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2388_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2414_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2414_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2414_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
size_t v___x_2394_; size_t v___x_2395_; uint8_t v___x_2396_; 
v___x_2394_ = lean_ptr_addr(v_k_2388_);
v___x_2395_ = lean_ptr_addr(v_a_2390_);
v___x_2396_ = lean_usize_dec_eq(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2406_; 
lean_inc(v_y_2387_);
lean_inc(v_i_2386_);
lean_inc(v_fvarId_2385_);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_c_2234_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; lean_object* v_unused_2408_; lean_object* v_unused_2409_; lean_object* v_unused_2410_; 
v_unused_2407_ = lean_ctor_get(v_c_2234_, 3);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_c_2234_, 2);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_c_2234_, 1);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_c_2234_, 0);
lean_dec(v_unused_2410_);
v___x_2398_ = v_c_2234_;
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v_c_2234_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 3, v_a_2390_);
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_fvarId_2385_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_i_2386_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_y_2387_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_a_2390_);
v___x_2401_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2401_);
v___x_2403_ = v___x_2392_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v___x_2412_; 
lean_dec(v_a_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v_c_2234_);
v___x_2412_ = v___x_2392_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_c_2234_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2234_, 4);
return v___x_2389_;
}
}
case 9:
{
lean_object* v_fvarId_2415_; lean_object* v_i_2416_; lean_object* v_offset_2417_; lean_object* v_y_2418_; lean_object* v_ty_2419_; lean_object* v_k_2420_; lean_object* v___x_2421_; 
v_fvarId_2415_ = lean_ctor_get(v_c_2234_, 0);
v_i_2416_ = lean_ctor_get(v_c_2234_, 1);
v_offset_2417_ = lean_ctor_get(v_c_2234_, 2);
v_y_2418_ = lean_ctor_get(v_c_2234_, 3);
v_ty_2419_ = lean_ctor_get(v_c_2234_, 4);
v_k_2420_ = lean_ctor_get(v_c_2234_, 5);
lean_inc_ref(v_k_2420_);
v___x_2421_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2420_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2448_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2448_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2448_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
size_t v___x_2426_; size_t v___x_2427_; uint8_t v___x_2428_; 
v___x_2426_ = lean_ptr_addr(v_k_2420_);
v___x_2427_ = lean_ptr_addr(v_a_2422_);
v___x_2428_ = lean_usize_dec_eq(v___x_2426_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2438_; 
lean_inc_ref(v_ty_2419_);
lean_inc(v_y_2418_);
lean_inc(v_offset_2417_);
lean_inc(v_i_2416_);
lean_inc(v_fvarId_2415_);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_c_2234_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; lean_object* v_unused_2440_; lean_object* v_unused_2441_; lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; 
v_unused_2439_ = lean_ctor_get(v_c_2234_, 5);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_c_2234_, 4);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_c_2234_, 3);
lean_dec(v_unused_2441_);
v_unused_2442_ = lean_ctor_get(v_c_2234_, 2);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_c_2234_, 1);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_c_2234_, 0);
lean_dec(v_unused_2444_);
v___x_2430_ = v_c_2234_;
v_isShared_2431_ = v_isSharedCheck_2438_;
goto v_resetjp_2429_;
}
else
{
lean_dec(v_c_2234_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2438_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 5, v_a_2422_);
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_fvarId_2415_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_i_2416_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_offset_2417_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_y_2418_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_ty_2419_);
lean_ctor_set(v_reuseFailAlloc_2437_, 5, v_a_2422_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2433_);
v___x_2435_ = v___x_2424_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v___x_2446_; 
lean_dec(v_a_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_c_2234_);
v___x_2446_ = v___x_2424_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_c_2234_);
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
else
{
lean_dec_ref_known(v_c_2234_, 6);
return v___x_2421_;
}
}
default: 
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_c_2234_);
v___x_2449_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2450_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2449_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
return v___x_2450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2459_, lean_object* v_discr_2460_, uint8_t v___x_2461_, size_t v_sz_2462_, size_t v_i_2463_, lean_object* v_bs_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = lean_usize_dec_lt(v_i_2463_, v_sz_2462_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_dec(v_discr_2460_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_bs_2464_);
return v___x_2472_;
}
else
{
lean_object* v___f_2473_; lean_object* v_v_2474_; lean_object* v___x_2475_; lean_object* v_bs_x27_2476_; lean_object* v_a_2478_; lean_object* v___y_2484_; lean_object* v___x_2494_; 
v___f_2473_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2474_ = lean_array_uget(v_bs_2464_, v_i_2463_);
v___x_2475_ = lean_unsigned_to_nat(0u);
v_bs_x27_2476_ = lean_array_uset(v_bs_2464_, v_i_2463_, v___x_2475_);
v___x_2494_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2474_, v___f_2473_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
if (lean_obj_tag(v_a_2495_) == 1)
{
lean_object* v_info_2496_; lean_object* v_code_2497_; uint8_t v___y_2499_; uint8_t v___x_2511_; 
v_info_2496_ = lean_ctor_get(v_a_2495_, 0);
v_code_2497_ = lean_ctor_get(v_a_2495_, 1);
v___x_2511_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2496_);
if (v___x_2511_ == 0)
{
v___y_2499_ = v___x_2461_;
goto v___jp_2498_;
}
else
{
v___y_2499_ = v___x_2511_;
goto v___jp_2498_;
}
v___jp_2498_:
{
if (v___y_2499_ == 0)
{
if (v___x_2459_ == 0)
{
lean_object* v___x_2500_; 
lean_dec_ref_known(v___x_2494_, 1);
lean_inc_ref(v_code_2497_);
lean_inc_ref(v_info_2496_);
lean_inc(v_discr_2460_);
v___x_2500_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2460_, v_info_2496_, v_code_2497_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2495_, v_a_2501_);
v_a_2478_ = v___x_2502_;
goto v___jp_2477_;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref_known(v_a_2495_, 2);
lean_dec_ref(v_bs_x27_2476_);
lean_dec(v_discr_2460_);
v_a_2503_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2500_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2500_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2495_, 2);
v___y_2484_ = v___x_2494_;
goto v___jp_2483_;
}
}
else
{
lean_dec_ref_known(v_a_2495_, 2);
v___y_2484_ = v___x_2494_;
goto v___jp_2483_;
}
}
}
else
{
lean_dec_ref_known(v_a_2495_, 1);
v___y_2484_ = v___x_2494_;
goto v___jp_2483_;
}
}
else
{
v___y_2484_ = v___x_2494_;
goto v___jp_2483_;
}
v___jp_2477_:
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((size_t)1ULL);
v___x_2480_ = lean_usize_add(v_i_2463_, v___x_2479_);
v___x_2481_ = lean_array_uset(v_bs_x27_2476_, v_i_2463_, v_a_2478_);
v_i_2463_ = v___x_2480_;
v_bs_2464_ = v___x_2481_;
goto _start;
}
v___jp_2483_:
{
if (lean_obj_tag(v___y_2484_) == 0)
{
lean_object* v_a_2485_; 
v_a_2485_ = lean_ctor_get(v___y_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___y_2484_, 1);
v_a_2478_ = v_a_2485_;
goto v___jp_2477_;
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v_bs_x27_2476_);
lean_dec(v_discr_2460_);
v_a_2486_ = lean_ctor_get(v___y_2484_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___y_2484_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___y_2484_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___y_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2512_, lean_object* v_discr_2513_, lean_object* v___x_2514_, lean_object* v_sz_2515_, lean_object* v_i_2516_, lean_object* v_bs_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v___x_6407__boxed_2524_; uint8_t v___x_6409__boxed_2525_; size_t v_sz_boxed_2526_; size_t v_i_boxed_2527_; lean_object* v_res_2528_; 
v___x_6407__boxed_2524_ = lean_unbox(v___x_2512_);
v___x_6409__boxed_2525_ = lean_unbox(v___x_2514_);
v_sz_boxed_2526_ = lean_unbox_usize(v_sz_2515_);
lean_dec(v_sz_2515_);
v_i_boxed_2527_ = lean_unbox_usize(v_i_2516_);
lean_dec(v_i_2516_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6407__boxed_2524_, v_discr_2513_, v___x_6409__boxed_2525_, v_sz_boxed_2526_, v_i_boxed_2527_, v_bs_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2528_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2530_, v_x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2533_, lean_object* v_x_2534_, lean_object* v_x_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2533_, v_x_2534_, v_x_2535_);
lean_dec(v_x_2535_);
lean_dec_ref(v_x_2534_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2538_, lean_object* v_m_2539_, lean_object* v_a_2540_, lean_object* v_fallback_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2539_, v_a_2540_, v_fallback_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2543_, lean_object* v_m_2544_, lean_object* v_a_2545_, lean_object* v_fallback_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2543_, v_m_2544_, v_a_2545_, v_fallback_2546_);
lean_dec(v_fallback_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_m_2544_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2549_, v_x_2550_, v_x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2553_, lean_object* v_x_2554_, size_t v_x_2555_, lean_object* v_x_2556_){
_start:
{
uint8_t v___x_2557_; 
v___x_2557_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2554_, v_x_2555_, v_x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_){
_start:
{
size_t v_x_6978__boxed_2562_; uint8_t v_res_2563_; lean_object* v_r_2564_; 
v_x_6978__boxed_2562_ = lean_unbox_usize(v_x_2560_);
lean_dec(v_x_2560_);
v_res_2563_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2558_, v_x_2559_, v_x_6978__boxed_2562_, v_x_2561_);
lean_dec(v_x_2561_);
lean_dec_ref(v_x_2559_);
v_r_2564_ = lean_box(v_res_2563_);
return v_r_2564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2565_, lean_object* v_a_2566_, lean_object* v_fallback_2567_, lean_object* v_x_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2566_, v_fallback_2567_, v_x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2570_, lean_object* v_a_2571_, lean_object* v_fallback_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2570_, v_a_2571_, v_fallback_2572_, v_x_2573_);
lean_dec(v_x_2573_);
lean_dec(v_fallback_2572_);
lean_dec(v_a_2571_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2575_, lean_object* v_x_2576_, size_t v_x_2577_, size_t v_x_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2576_, v_x_2577_, v_x_2578_, v_x_2579_, v_x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_){
_start:
{
size_t v_x_6994__boxed_2588_; size_t v_x_6995__boxed_2589_; lean_object* v_res_2590_; 
v_x_6994__boxed_2588_ = lean_unbox_usize(v_x_2584_);
lean_dec(v_x_2584_);
v_x_6995__boxed_2589_ = lean_unbox_usize(v_x_2585_);
lean_dec(v_x_2585_);
v_res_2590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2582_, v_x_2583_, v_x_6994__boxed_2588_, v_x_6995__boxed_2589_, v_x_2586_, v_x_2587_);
return v_res_2590_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2591_, lean_object* v_keys_2592_, lean_object* v_vals_2593_, lean_object* v_heq_2594_, lean_object* v_i_2595_, lean_object* v_k_2596_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2592_, v_i_2595_, v_k_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2598_, lean_object* v_keys_2599_, lean_object* v_vals_2600_, lean_object* v_heq_2601_, lean_object* v_i_2602_, lean_object* v_k_2603_){
_start:
{
uint8_t v_res_2604_; lean_object* v_r_2605_; 
v_res_2604_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2598_, v_keys_2599_, v_vals_2600_, v_heq_2601_, v_i_2602_, v_k_2603_);
lean_dec(v_k_2603_);
lean_dec_ref(v_vals_2600_);
lean_dec_ref(v_keys_2599_);
v_r_2605_ = lean_box(v_res_2604_);
return v_r_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2606_, lean_object* v_n_2607_, lean_object* v_k_2608_, lean_object* v_v_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_2607_, v_k_2608_, v_v_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2611_, size_t v_depth_2612_, lean_object* v_keys_2613_, lean_object* v_vals_2614_, lean_object* v_heq_2615_, lean_object* v_i_2616_, lean_object* v_entries_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2612_, v_keys_2613_, v_vals_2614_, v_i_2616_, v_entries_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2619_, lean_object* v_depth_2620_, lean_object* v_keys_2621_, lean_object* v_vals_2622_, lean_object* v_heq_2623_, lean_object* v_i_2624_, lean_object* v_entries_2625_){
_start:
{
size_t v_depth_boxed_2626_; lean_object* v_res_2627_; 
v_depth_boxed_2626_ = lean_unbox_usize(v_depth_2620_);
lean_dec(v_depth_2620_);
v_res_2627_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_2619_, v_depth_boxed_2626_, v_keys_2621_, v_vals_2622_, v_heq_2623_, v_i_2624_, v_entries_2625_);
lean_dec_ref(v_vals_2622_);
lean_dec_ref(v_keys_2621_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2629_, v_x_2630_, v_x_2631_, v_x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_toApplicative_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2707_; 
v___x_2643_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2644_ = l_StateRefT_x27_instMonad___redArg(v___x_2643_);
v_toApplicative_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___x_2644_, 1);
lean_dec(v_unused_2708_);
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2707_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_toApplicative_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2707_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_toFunctor_2649_; lean_object* v_toSeq_2650_; lean_object* v_toSeqLeft_2651_; lean_object* v_toSeqRight_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2705_; 
v_toFunctor_2649_ = lean_ctor_get(v_toApplicative_2645_, 0);
v_toSeq_2650_ = lean_ctor_get(v_toApplicative_2645_, 2);
v_toSeqLeft_2651_ = lean_ctor_get(v_toApplicative_2645_, 3);
v_toSeqRight_2652_ = lean_ctor_get(v_toApplicative_2645_, 4);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_toApplicative_2645_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v_toApplicative_2645_, 1);
lean_dec(v_unused_2706_);
v___x_2654_ = v_toApplicative_2645_;
v_isShared_2655_ = v_isSharedCheck_2705_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_toSeqRight_2652_);
lean_inc(v_toSeqLeft_2651_);
lean_inc(v_toSeq_2650_);
lean_inc(v_toFunctor_2649_);
lean_dec(v_toApplicative_2645_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2705_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___f_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___f_2662_; lean_object* v___f_2663_; lean_object* v___x_2665_; 
v___f_2656_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2657_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2649_);
v___f_2658_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2658_, 0, v_toFunctor_2649_);
v___f_2659_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2659_, 0, v_toFunctor_2649_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___f_2658_);
lean_ctor_set(v___x_2660_, 1, v___f_2659_);
v___f_2661_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2661_, 0, v_toSeqRight_2652_);
v___f_2662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2662_, 0, v_toSeqLeft_2651_);
v___f_2663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2663_, 0, v_toSeq_2650_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 4, v___f_2661_);
lean_ctor_set(v___x_2654_, 3, v___f_2662_);
lean_ctor_set(v___x_2654_, 2, v___f_2663_);
lean_ctor_set(v___x_2654_, 1, v___f_2656_);
lean_ctor_set(v___x_2654_, 0, v___x_2660_);
v___x_2665_ = v___x_2654_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___f_2656_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v___f_2663_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v___f_2662_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v___f_2661_);
v___x_2665_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___f_2657_);
lean_ctor_set(v___x_2647_, 0, v___x_2665_);
v___x_2667_ = v___x_2647_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___f_2657_);
v___x_2667_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v_toApplicative_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2701_; 
v___x_2668_ = l_StateRefT_x27_instMonad___redArg(v___x_2667_);
v_toApplicative_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2702_);
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2701_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_toApplicative_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2701_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_toFunctor_2673_; lean_object* v_toSeq_2674_; lean_object* v_toSeqLeft_2675_; lean_object* v_toSeqRight_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2699_; 
v_toFunctor_2673_ = lean_ctor_get(v_toApplicative_2669_, 0);
v_toSeq_2674_ = lean_ctor_get(v_toApplicative_2669_, 2);
v_toSeqLeft_2675_ = lean_ctor_get(v_toApplicative_2669_, 3);
v_toSeqRight_2676_ = lean_ctor_get(v_toApplicative_2669_, 4);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_toApplicative_2669_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v_toApplicative_2669_, 1);
lean_dec(v_unused_2700_);
v___x_2678_ = v_toApplicative_2669_;
v_isShared_2679_ = v_isSharedCheck_2699_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_toSeqRight_2676_);
lean_inc(v_toSeqLeft_2675_);
lean_inc(v_toSeq_2674_);
lean_inc(v_toFunctor_2673_);
lean_dec(v_toApplicative_2669_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2699_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___f_2680_; lean_object* v___f_2681_; lean_object* v___f_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___f_2685_; lean_object* v___f_2686_; lean_object* v___f_2687_; lean_object* v___x_2689_; 
v___f_2680_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2681_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2673_);
v___f_2682_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2682_, 0, v_toFunctor_2673_);
v___f_2683_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2683_, 0, v_toFunctor_2673_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___f_2682_);
lean_ctor_set(v___x_2684_, 1, v___f_2683_);
v___f_2685_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2685_, 0, v_toSeqRight_2676_);
v___f_2686_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2686_, 0, v_toSeqLeft_2675_);
v___f_2687_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2687_, 0, v_toSeq_2674_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 4, v___f_2685_);
lean_ctor_set(v___x_2678_, 3, v___f_2686_);
lean_ctor_set(v___x_2678_, 2, v___f_2687_);
lean_ctor_set(v___x_2678_, 1, v___f_2680_);
lean_ctor_set(v___x_2678_, 0, v___x_2684_);
v___x_2689_ = v___x_2678_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___f_2680_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v___f_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v___f_2686_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v___f_2685_);
v___x_2689_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___f_2681_);
lean_ctor_set(v___x_2671_, 0, v___x_2689_);
v___x_2691_ = v___x_2671_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___f_2681_);
v___x_2691_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2546__overap_2695_; lean_object* v___x_2696_; 
v___x_2692_ = l_StateRefT_x27_instMonad___redArg(v___x_2691_);
v___x_2693_ = lean_box(0);
v___x_2694_ = l_instInhabitedOfMonad___redArg(v___x_2692_, v___x_2693_);
v___x_2546__overap_2695_ = lean_panic_fn_borrowed(v___x_2694_, v_msg_2636_);
lean_dec(v___x_2694_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
v___x_2696_ = lean_apply_6(v___x_2546__overap_2695_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, lean_box(0));
return v___x_2696_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
return v_res_2716_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2718_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2719_ = lean_unsigned_to_nat(61u);
v___x_2720_ = lean_unsigned_to_nat(304u);
v___x_2721_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2722_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2723_ = l_mkPanicMessageWithDecl(v___x_2722_, v___x_2721_, v___x_2720_, v___x_2719_, v___x_2718_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
switch(lean_obj_tag(v_c_2724_))
{
case 0:
{
lean_object* v_decl_2731_; lean_object* v_value_2732_; 
v_decl_2731_ = lean_ctor_get(v_c_2724_, 0);
v_value_2732_ = lean_ctor_get(v_decl_2731_, 3);
if (lean_obj_tag(v_value_2732_) == 11)
{
lean_object* v_k_2733_; lean_object* v_var_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_inc_ref(v_value_2732_);
v_k_2733_ = lean_ctor_get(v_c_2724_, 1);
lean_inc_ref(v_k_2733_);
lean_dec_ref_known(v_c_2724_, 2);
v_var_2734_ = lean_ctor_get(v_value_2732_, 1);
lean_inc(v_var_2734_);
lean_dec_ref_known(v_value_2732_, 2);
v___x_2735_ = lean_st_ref_take(v_a_2725_);
v___x_2736_ = lean_box(0);
v___x_2737_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2735_, v_var_2734_, v___x_2736_);
v___x_2738_ = lean_st_ref_put(v_a_2725_, v___x_2737_);
v_c_2724_ = v_k_2733_;
goto _start;
}
else
{
lean_object* v_k_2740_; 
v_k_2740_ = lean_ctor_get(v_c_2724_, 1);
lean_inc_ref(v_k_2740_);
lean_dec_ref_known(v_c_2724_, 2);
v_c_2724_ = v_k_2740_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2742_; lean_object* v_k_2743_; lean_object* v_value_2744_; lean_object* v___x_2745_; 
v_decl_2742_ = lean_ctor_get(v_c_2724_, 0);
lean_inc_ref(v_decl_2742_);
v_k_2743_ = lean_ctor_get(v_c_2724_, 1);
lean_inc_ref(v_k_2743_);
lean_dec_ref_known(v_c_2724_, 2);
v_value_2744_ = lean_ctor_get(v_decl_2742_, 4);
lean_inc_ref(v_value_2744_);
lean_dec_ref(v_decl_2742_);
v___x_2745_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2744_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_dec_ref_known(v___x_2745_, 1);
v_c_2724_ = v_k_2743_;
goto _start;
}
else
{
lean_dec_ref(v_k_2743_);
return v___x_2745_;
}
}
case 3:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec_ref_known(v_c_2724_, 2);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
case 4:
{
lean_object* v_cases_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2771_; 
v_cases_2749_ = lean_ctor_get(v_c_2724_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_c_2724_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2751_ = v_c_2724_;
v_isShared_2752_ = v_isSharedCheck_2771_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_cases_2749_);
lean_dec(v_c_2724_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2771_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_alts_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_alts_2753_ = lean_ctor_get(v_cases_2749_, 3);
lean_inc_ref(v_alts_2753_);
lean_dec_ref(v_cases_2749_);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = lean_array_get_size(v_alts_2753_);
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_nat_dec_lt(v___x_2754_, v___x_2755_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2759_; 
lean_dec_ref(v_alts_2753_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2756_);
v___x_2759_ = v___x_2751_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2756_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_nat_dec_le(v___x_2755_, v___x_2755_);
if (v___x_2761_ == 0)
{
if (v___x_2757_ == 0)
{
lean_object* v___x_2763_; 
lean_dec_ref(v_alts_2753_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2756_);
v___x_2763_ = v___x_2751_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2756_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
else
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
lean_del_object(v___x_2751_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = lean_usize_of_nat(v___x_2755_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2753_, v___x_2765_, v___x_2766_, v___x_2756_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec_ref(v_alts_2753_);
return v___x_2767_;
}
}
else
{
size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
lean_del_object(v___x_2751_);
v___x_2768_ = ((size_t)0ULL);
v___x_2769_ = lean_usize_of_nat(v___x_2755_);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2753_, v___x_2768_, v___x_2769_, v___x_2756_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec_ref(v_alts_2753_);
return v___x_2770_;
}
}
}
}
case 5:
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v_isSharedCheck_2779_ = !lean_is_exclusive(v_c_2724_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_c_2724_, 0);
lean_dec(v_unused_2780_);
v___x_2773_ = v_c_2724_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_c_2724_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = lean_box(0);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
case 6:
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2788_; 
v_isSharedCheck_2788_ = !lean_is_exclusive(v_c_2724_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v_c_2724_, 0);
lean_dec(v_unused_2789_);
v___x_2782_ = v_c_2724_;
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v_c_2724_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_box(0);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
case 8:
{
lean_object* v_k_2790_; 
v_k_2790_ = lean_ctor_get(v_c_2724_, 3);
lean_inc_ref(v_k_2790_);
lean_dec_ref_known(v_c_2724_, 4);
v_c_2724_ = v_k_2790_;
goto _start;
}
case 9:
{
lean_object* v_k_2792_; 
v_k_2792_ = lean_ctor_get(v_c_2724_, 5);
lean_inc_ref(v_k_2792_);
lean_dec_ref_known(v_c_2724_, 6);
v_c_2724_ = v_k_2792_;
goto _start;
}
default: 
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec_ref(v_c_2724_);
v___x_2794_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2795_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2794_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
return v___x_2795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2796_, size_t v_i_2797_, size_t v_stop_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___y_2807_; uint8_t v___x_2813_; 
v___x_2813_ = lean_usize_dec_eq(v_i_2797_, v_stop_2798_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_array_uget_borrowed(v_as_2796_, v_i_2797_);
switch(lean_obj_tag(v___x_2814_))
{
case 0:
{
lean_object* v_code_2815_; 
v_code_2815_ = lean_ctor_get(v___x_2814_, 2);
lean_inc_ref(v_code_2815_);
v___y_2807_ = v_code_2815_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_code_2816_; 
v_code_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc_ref(v_code_2816_);
v___y_2807_ = v_code_2816_;
goto v___jp_2806_;
}
default: 
{
lean_object* v_code_2817_; 
v_code_2817_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_ref(v_code_2817_);
v___y_2807_ = v_code_2817_;
goto v___jp_2806_;
}
}
}
else
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_b_2799_);
return v___x_2818_;
}
v___jp_2806_:
{
lean_object* v___x_2808_; 
v___x_2808_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2807_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; size_t v___x_2810_; size_t v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2797_, v___x_2810_);
v_i_2797_ = v___x_2811_;
v_b_2799_ = v_a_2809_;
goto _start;
}
else
{
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2819_, lean_object* v_i_2820_, lean_object* v_stop_2821_, lean_object* v_b_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
size_t v_i_boxed_2829_; size_t v_stop_boxed_2830_; lean_object* v_res_2831_; 
v_i_boxed_2829_ = lean_unbox_usize(v_i_2820_);
lean_dec(v_i_2820_);
v_stop_boxed_2830_ = lean_unbox_usize(v_stop_2821_);
lean_dec(v_stop_2821_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2819_, v_i_boxed_2829_, v_stop_boxed_2830_, v_b_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v_as_2819_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
return v_res_2839_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2840_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg(){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___boxed(lean_object* v___dummy_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
return v_res_2846_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2850_, lean_object* v_v_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
if (lean_obj_tag(v_v_2851_) == 0)
{
lean_object* v_code_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2882_; 
v_code_2858_ = lean_ctor_get(v_v_2851_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_v_2851_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2860_ = v_v_2851_;
v_isShared_2861_ = v_isSharedCheck_2882_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_code_2858_);
lean_dec(v_v_2851_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2882_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; 
lean_inc(v___y_2856_);
lean_inc_ref(v___y_2855_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
lean_inc_ref(v___y_2852_);
v___x_2862_ = lean_apply_7(v_f_2850_, v_code_2858_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, lean_box(0));
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2873_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2873_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2873_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v_a_2863_);
v___x_2868_ = v___x_2860_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2868_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_del_object(v___x_2860_);
v_a_2874_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2862_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2862_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
else
{
lean_object* v___x_2883_; 
lean_dec_ref(v_f_2850_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_v_2851_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2884_, lean_object* v_v_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2884_, v_v_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2893_, lean_object* v_f_2894_, lean_object* v_v_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2894_, v_v_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2903_, lean_object* v_f_2904_, lean_object* v_v_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_pu_boxed_2912_; lean_object* v_res_2913_; 
v_pu_boxed_2912_ = lean_unbox(v_pu_2903_);
v_res_2913_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_2912_, v_f_2904_, v_v_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_alreadyFound_2922_; uint8_t v_relaxedReuse_2923_; lean_object* v_ownedness_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; uint8_t v_relaxedReuse_2931_; 
v_relaxedReuse_2931_ = lean_ctor_get_uint8(v___y_2915_, sizeof(void*)*2);
if (v_relaxedReuse_2931_ == 0)
{
lean_object* v_ownedness_2932_; lean_object* v___x_2933_; 
v_ownedness_2932_ = lean_ctor_get(v___y_2915_, 1);
v___x_2933_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v_alreadyFound_2922_ = v___x_2933_;
v_relaxedReuse_2923_ = v_relaxedReuse_2931_;
v_ownedness_2924_ = v_ownedness_2932_;
v___y_2925_ = v___y_2916_;
v___y_2926_ = v___y_2917_;
v___y_2927_ = v___y_2918_;
v___y_2928_ = v___y_2919_;
goto v___jp_2921_;
}
else
{
lean_object* v_ownedness_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_ownedness_2934_ = lean_ctor_get(v___y_2915_, 1);
v___x_2935_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2936_ = lean_st_mk_ref(v___x_2935_);
lean_inc_ref(v_code_2914_);
v___x_2937_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_2914_, v___x_2936_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2938_; 
lean_dec_ref_known(v___x_2937_, 1);
v___x_2938_ = lean_st_ref_get(v___x_2936_);
lean_dec(v___x_2936_);
v_alreadyFound_2922_ = v___x_2938_;
v_relaxedReuse_2923_ = v_relaxedReuse_2931_;
v_ownedness_2924_ = v_ownedness_2934_;
v___y_2925_ = v___y_2916_;
v___y_2926_ = v___y_2917_;
v___y_2927_ = v___y_2918_;
v___y_2928_ = v___y_2919_;
goto v___jp_2921_;
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v___x_2936_);
lean_dec_ref(v_code_2914_);
v_a_2939_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2937_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2937_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
v___jp_2921_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_inc_ref(v_ownedness_2924_);
v___x_2929_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2929_, 0, v_alreadyFound_2922_);
lean_ctor_set(v___x_2929_, 1, v_ownedness_2924_);
lean_ctor_set_uint8(v___x_2929_, sizeof(void*)*2, v_relaxedReuse_2923_);
v___x_2930_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_2914_, v___x_2929_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec_ref_known(v___x_2929_, 2);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_toSignature_2963_; lean_object* v_value_2964_; uint8_t v_recursive_2965_; lean_object* v_inlineAttr_x3f_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2991_; 
v_toSignature_2963_ = lean_ctor_get(v_decl_2956_, 0);
v_value_2964_ = lean_ctor_get(v_decl_2956_, 1);
v_recursive_2965_ = lean_ctor_get_uint8(v_decl_2956_, sizeof(void*)*3);
v_inlineAttr_x3f_2966_ = lean_ctor_get(v_decl_2956_, 2);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_decl_2956_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2968_ = v_decl_2956_;
v_isShared_2969_ = v_isSharedCheck_2991_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_inlineAttr_x3f_2966_);
lean_inc(v_value_2964_);
lean_inc(v_toSignature_2963_);
lean_dec(v_decl_2956_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2991_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___f_2970_; lean_object* v___x_2971_; 
v___f_2970_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_2971_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_2970_, v_value_2964_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2982_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v_a_2972_);
v___x_2977_ = v___x_2968_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_toSignature_2963_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_a_2972_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_inlineAttr_x3f_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2981_, sizeof(void*)*3, v_recursive_2965_);
v___x_2977_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2979_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2977_);
v___x_2979_ = v___x_2974_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_del_object(v___x_2968_);
lean_dec(v_inlineAttr_x3f_2966_);
lean_dec_ref(v_toSignature_2963_);
v_a_2983_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2971_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2971_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3001_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3034_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3034_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3034_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
uint8_t v_resetReuse_3011_; 
v_resetReuse_3011_ = lean_ctor_get_uint8(v_a_3007_, sizeof(void*)*4 + 2);
lean_dec(v_a_3007_);
if (v_resetReuse_3011_ == 0)
{
lean_object* v___x_3013_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_decl_3000_);
v___x_3013_ = v___x_3009_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_decl_3000_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
else
{
lean_object* v___x_3015_; 
lean_del_object(v___x_3009_);
lean_inc_ref(v_decl_3000_);
v___x_3015_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc_n(v_a_3016_, 2);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_3000_, v_a_3016_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_3020_ = 0;
lean_inc(v_a_3016_);
v___x_3021_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v_a_3016_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*2, v___x_3020_);
v___x_3022_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3018_, v___x_3021_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec_ref_known(v___x_3021_, 2);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3024_, 0, v___x_3019_);
lean_ctor_set(v___x_3024_, 1, v_a_3016_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*2, v_resetReuse_3011_);
v___x_3025_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3023_, v___x_3024_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec_ref_known(v___x_3024_, 2);
return v___x_3025_;
}
else
{
lean_dec(v_a_3016_);
return v___x_3022_;
}
}
else
{
lean_dec(v_a_3016_);
return v___x_3017_;
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_decl_3000_);
v_a_3026_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3015_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3015_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v_decl_3000_);
v_a_3035_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3006_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3006_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
return v_res_3049_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3056_ = 2;
v___x_3057_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3058_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3057_, v___x_3056_, v___x_3055_, v___x_3054_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3059_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_unsigned_to_nat(2506150707u);
v___x_3116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3117_ = l_Lean_Name_num___override(v___x_3116_, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3120_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3121_ = l_Lean_Name_str___override(v___x_3120_, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3124_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3125_ = l_Lean_Name_str___override(v___x_3124_, v___x_3123_);
return v___x_3125_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_unsigned_to_nat(2u);
v___x_3127_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3128_ = l_Lean_Name_num___override(v___x_3127_, v___x_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3130_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3131_ = 1;
v___x_3132_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3133_ = l_Lean_registerTraceClass(v___x_3130_, v___x_3131_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3135_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_insertResetReuse = _init_l_Lean_Compiler_LCNF_insertResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_insertResetReuse);
res = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
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
lean_object* initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
