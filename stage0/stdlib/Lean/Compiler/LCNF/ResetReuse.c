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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_applyOwnedness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_name_5_; lean_object* v_size_6_; lean_object* v_usize_7_; lean_object* v_ssize_8_; lean_object* v_name_9_; lean_object* v_size_10_; lean_object* v_usize_11_; lean_object* v_ssize_12_; uint8_t v___y_14_; uint8_t v___x_28_; 
v_name_5_ = lean_ctor_get(v_c_u2081_1_, 0);
v_size_6_ = lean_ctor_get(v_c_u2081_1_, 2);
v_usize_7_ = lean_ctor_get(v_c_u2081_1_, 3);
v_ssize_8_ = lean_ctor_get(v_c_u2081_1_, 4);
v_name_9_ = lean_ctor_get(v_c_u2082_2_, 0);
v_size_10_ = lean_ctor_get(v_c_u2082_2_, 2);
v_usize_11_ = lean_ctor_get(v_c_u2082_2_, 3);
v_ssize_12_ = lean_ctor_get(v_c_u2082_2_, 4);
v___x_28_ = lean_nat_dec_eq(v_size_6_, v_size_10_);
if (v___x_28_ == 0)
{
v___y_14_ = v___x_28_;
goto v___jp_13_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = lean_nat_dec_eq(v_usize_7_, v_usize_11_);
v___y_14_ = v___x_29_;
goto v___jp_13_;
}
v___jp_13_:
{
if (v___y_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(v___y_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = lean_nat_dec_eq(v_ssize_8_, v_ssize_12_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_box(v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
else
{
uint8_t v_relaxedReuse_20_; 
v_relaxedReuse_20_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*2);
if (v_relaxedReuse_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_21_ = l_Lean_Name_getPrefix(v_name_5_);
v___x_22_ = l_Lean_Name_getPrefix(v_name_9_);
v___x_23_ = lean_name_eq(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_box(v_relaxedReuse_20_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
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
uint8_t v___x_53_; lean_object* v___x_54_; 
v___x_53_ = 1;
v___x_54_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object* v_msg_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_57_ = lean_panic_fn_borrowed(v___x_56_, v_msg_55_);
return v___x_57_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_instMonadEIO(lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_toApplicative_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_107_; 
v___x_68_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_69_ = l_StateRefT_x27_instMonad___redArg(v___x_68_);
v_toApplicative_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v___x_69_, 1);
lean_dec(v_unused_108_);
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_107_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_toApplicative_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_107_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_toFunctor_74_; lean_object* v_toSeq_75_; lean_object* v_toSeqLeft_76_; lean_object* v_toSeqRight_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_105_; 
v_toFunctor_74_ = lean_ctor_get(v_toApplicative_70_, 0);
v_toSeq_75_ = lean_ctor_get(v_toApplicative_70_, 2);
v_toSeqLeft_76_ = lean_ctor_get(v_toApplicative_70_, 3);
v_toSeqRight_77_ = lean_ctor_get(v_toApplicative_70_, 4);
v_isSharedCheck_105_ = !lean_is_exclusive(v_toApplicative_70_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v_toApplicative_70_, 1);
lean_dec(v_unused_106_);
v___x_79_ = v_toApplicative_70_;
v_isShared_80_ = v_isSharedCheck_105_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_toSeqRight_77_);
lean_inc(v_toSeqLeft_76_);
lean_inc(v_toSeq_75_);
lean_inc(v_toFunctor_74_);
lean_dec(v_toApplicative_70_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_105_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_90_; 
v___f_81_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_82_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_74_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_74_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_84_, 0, v_toFunctor_74_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___f_83_);
lean_ctor_set(v___x_85_, 1, v___f_84_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeqRight_77_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeqLeft_76_);
v___f_88_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_88_, 0, v_toSeq_75_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 4, v___f_86_);
lean_ctor_set(v___x_79_, 3, v___f_87_);
lean_ctor_set(v___x_79_, 2, v___f_88_);
lean_ctor_set(v___x_79_, 1, v___f_81_);
lean_ctor_set(v___x_79_, 0, v___x_85_);
v___x_90_ = v___x_79_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___f_81_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v___f_88_);
lean_ctor_set(v_reuseFailAlloc_104_, 3, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_104_, 4, v___f_86_);
v___x_90_ = v_reuseFailAlloc_104_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_92_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___f_82_);
lean_ctor_set(v___x_72_, 0, v___x_90_);
v___x_92_ = v___x_72_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___f_82_);
v___x_92_ = v_reuseFailAlloc_103_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_3796__overap_101_; lean_object* v___x_102_; 
v___x_93_ = l_StateRefT_x27_instMonad___redArg(v___x_92_);
v___x_94_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_95_ = 0;
v___x_96_ = lean_box(v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_94_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = l_instInhabitedOfMonad___redArg(v___x_93_, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_99_, 0, v___x_98_);
v___f_100_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_100_, 0, v___f_99_);
v___x_3796__overap_101_ = lean_panic_fn_borrowed(v___f_100_, v_msg_61_);
lean_dec_ref(v___f_100_);
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc_ref(v___y_62_);
v___x_102_ = lean_apply_6(v___x_3796__overap_101_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, lean_box(0));
return v___x_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object* v_as_117_, size_t v_i_118_, size_t v_stop_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_eq(v_i_118_, v_stop_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_uget_borrowed(v_as_117_, v_i_118_);
v___x_122_ = lean_unbox(v___x_121_);
if (v___x_122_ == 0)
{
size_t v___x_123_; size_t v___x_124_; 
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_i_118_, v___x_123_);
v_i_118_ = v___x_124_;
goto _start;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_unbox(v___x_121_);
return v___x_126_;
}
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object* v_as_128_, lean_object* v_i_129_, lean_object* v_stop_130_){
_start:
{
size_t v_i_boxed_131_; size_t v_stop_boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_i_boxed_131_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_130_);
lean_dec(v_stop_130_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_128_, v_i_boxed_131_, v_stop_boxed_132_);
lean_dec_ref(v_as_128_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_139_ = lean_unsigned_to_nat(9u);
v___x_140_ = lean_unsigned_to_nat(633u);
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1));
v___x_142_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0));
v___x_143_ = l_mkPanicMessageWithDecl(v___x_142_, v___x_141_, v___x_140_, v___x_139_, v___x_138_);
return v___x_143_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_147_ = lean_unsigned_to_nat(61u);
v___x_148_ = lean_unsigned_to_nat(125u);
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5));
v___x_150_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_151_ = l_mkPanicMessageWithDecl(v___x_150_, v___x_149_, v___x_148_, v___x_147_, v___x_146_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object* v_info_152_, lean_object* v_w_153_, lean_object* v_c_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
uint8_t v___y_162_; lean_object* v___y_163_; lean_object* v_k_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; 
switch(lean_obj_tag(v_c_154_))
{
case 0:
{
lean_object* v_decl_388_; lean_object* v_value_389_; 
v_decl_388_ = lean_ctor_get(v_c_154_, 0);
lean_inc_ref(v_decl_388_);
v_value_389_ = lean_ctor_get(v_decl_388_, 3);
lean_inc(v_value_389_);
if (lean_obj_tag(v_value_389_) == 5)
{
lean_object* v_k_390_; lean_object* v_fvarId_391_; lean_object* v_binderName_392_; lean_object* v_type_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_456_; 
v_k_390_ = lean_ctor_get(v_c_154_, 1);
v_fvarId_391_ = lean_ctor_get(v_decl_388_, 0);
v_binderName_392_ = lean_ctor_get(v_decl_388_, 1);
v_type_393_ = lean_ctor_get(v_decl_388_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_decl_388_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_decl_388_, 3);
lean_dec(v_unused_457_);
v___x_395_ = v_decl_388_;
v_isShared_396_ = v_isSharedCheck_456_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_type_393_);
lean_inc(v_binderName_392_);
lean_inc(v_fvarId_391_);
lean_dec(v_decl_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_456_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_i_397_; lean_object* v_args_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_455_; 
v_i_397_ = lean_ctor_get(v_value_389_, 0);
v_args_398_ = lean_ctor_get(v_value_389_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_value_389_);
if (v_isSharedCheck_455_ == 0)
{
v___x_400_ = v_value_389_;
v_isShared_401_ = v_isSharedCheck_455_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_args_398_);
lean_inc(v_i_397_);
lean_dec(v_value_389_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_455_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; 
v___x_402_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_info_152_, v_i_397_, v_a_155_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; uint8_t v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = lean_unbox(v_a_403_);
if (v___x_404_ == 0)
{
lean_dec(v_a_403_);
lean_del_object(v___x_400_);
lean_dec_ref(v_args_398_);
lean_dec_ref(v_i_397_);
lean_del_object(v___x_395_);
lean_dec_ref(v_type_393_);
lean_dec(v_binderName_392_);
lean_dec(v_fvarId_391_);
lean_inc_ref(v_k_390_);
v_k_168_ = v_k_390_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_444_; 
lean_inc_ref(v_k_390_);
v_isSharedCheck_444_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_446_);
v___x_406_ = v_c_154_;
v_isShared_407_ = v_isSharedCheck_444_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_c_154_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_444_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_cidx_408_; lean_object* v_cidx_409_; uint8_t v___x_410_; lean_object* v___x_412_; 
v_cidx_408_ = lean_ctor_get(v_info_152_, 1);
v_cidx_409_ = lean_ctor_get(v_i_397_, 1);
v___x_410_ = 1;
lean_inc_ref(v_args_398_);
lean_inc_ref(v_i_397_);
if (v_isShared_401_ == 0)
{
v___x_412_ = v___x_400_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_i_397_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_args_398_);
v___x_412_ = v_reuseFailAlloc_443_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
lean_inc_ref(v_type_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 3, v___x_412_);
v___x_414_ = v___x_395_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_fvarId_391_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_binderName_392_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_type_393_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v___x_412_);
v___x_414_ = v_reuseFailAlloc_442_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
uint8_t v___y_416_; uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_eq(v_cidx_408_, v_cidx_409_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = lean_unbox(v_a_403_);
v___y_416_ = v___x_440_;
goto v___jp_415_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = 0;
v___y_416_ = v___x_441_;
goto v___jp_415_;
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(v___x_417_, 0, v_w_153_);
lean_ctor_set(v___x_417_, 1, v_i_397_);
lean_ctor_set(v___x_417_, 2, v_args_398_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*3, v___y_416_);
v___x_418_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_410_, v___x_414_, v_type_393_, v___x_417_, v_a_157_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_430_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_a_419_);
v___x_424_ = v___x_406_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_k_390_);
v___x_424_ = v_reuseFailAlloc_429_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_a_403_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
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
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_del_object(v___x_406_);
lean_dec(v_a_403_);
lean_dec_ref(v_k_390_);
v_a_431_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_418_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_418_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
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
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_del_object(v___x_400_);
lean_dec_ref(v_args_398_);
lean_dec_ref(v_i_397_);
lean_del_object(v___x_395_);
lean_dec_ref(v_type_393_);
lean_dec(v_binderName_392_);
lean_dec(v_fvarId_391_);
lean_dec_ref_known(v_c_154_, 2);
lean_dec(v_w_153_);
v_a_447_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_402_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_402_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
else
{
lean_object* v_k_458_; 
lean_dec(v_value_389_);
lean_dec_ref(v_decl_388_);
v_k_458_ = lean_ctor_get(v_c_154_, 1);
lean_inc_ref(v_k_458_);
v_k_168_ = v_k_458_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
}
case 2:
{
lean_object* v_decl_459_; lean_object* v_k_460_; lean_object* v_params_461_; lean_object* v_type_462_; lean_object* v_value_463_; lean_object* v___x_464_; 
v_decl_459_ = lean_ctor_get(v_c_154_, 0);
v_k_460_ = lean_ctor_get(v_c_154_, 1);
v_params_461_ = lean_ctor_get(v_decl_459_, 2);
v_type_462_ = lean_ctor_get(v_decl_459_, 3);
v_value_463_ = lean_ctor_get(v_decl_459_, 4);
lean_inc_ref(v_value_463_);
lean_inc(v_w_153_);
v___x_464_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_152_, v_w_153_, v_value_463_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v_snd_466_; uint8_t v___x_467_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v_snd_466_ = lean_ctor_get(v_a_465_, 1);
lean_inc(v_snd_466_);
v___x_467_ = lean_unbox(v_snd_466_);
if (v___x_467_ == 0)
{
lean_dec(v_snd_466_);
lean_dec(v_a_465_);
lean_inc_ref(v_k_460_);
v_k_168_ = v_k_460_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
else
{
lean_object* v_fst_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_511_; 
lean_dec(v_w_153_);
v_fst_468_ = lean_ctor_get(v_a_465_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_465_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_a_465_, 1);
lean_dec(v_unused_512_);
v___x_470_ = v_a_465_;
v_isShared_471_ = v_isSharedCheck_511_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_fst_468_);
lean_dec(v_a_465_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_511_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; lean_object* v___x_473_; 
v___x_472_ = 1;
lean_inc_ref(v_params_461_);
lean_inc_ref(v_type_462_);
lean_inc_ref(v_decl_459_);
v___x_473_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_472_, v_decl_459_, v_type_462_, v_params_461_, v_fst_468_, v_a_157_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_502_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_502_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_502_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_502_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___y_479_; uint8_t v___y_487_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_ptr_addr(v_k_460_);
v___x_498_ = lean_usize_dec_eq(v___x_497_, v___x_497_);
if (v___x_498_ == 0)
{
v___y_487_ = v___x_498_;
goto v___jp_486_;
}
else
{
size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_ptr_addr(v_decl_459_);
v___x_500_ = lean_ptr_addr(v_a_474_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
v___y_487_ = v___x_501_;
goto v___jp_486_;
}
v___jp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___y_479_);
v___x_481_ = v___x_470_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___y_479_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_snd_466_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_481_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_inc_ref(v_k_460_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_495_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_496_);
v___x_489_ = v_c_154_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_c_154_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v_a_474_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_460_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v___y_479_ = v___x_492_;
goto v___jp_478_;
}
}
}
else
{
lean_dec(v_a_474_);
v___y_479_ = v_c_154_;
goto v___jp_478_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_del_object(v___x_470_);
lean_dec(v_snd_466_);
lean_dec_ref_known(v_c_154_, 2);
v_a_503_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_473_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_473_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_c_154_, 2);
lean_dec(v_w_153_);
return v___x_464_;
}
}
case 3:
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_w_153_);
v___x_513_ = 0;
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_c_154_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
case 4:
{
lean_object* v_cases_517_; lean_object* v_typeName_518_; lean_object* v_resultType_519_; lean_object* v_discr_520_; lean_object* v_alts_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_573_; 
v_cases_517_ = lean_ctor_get(v_c_154_, 0);
lean_inc_ref(v_cases_517_);
v_typeName_518_ = lean_ctor_get(v_cases_517_, 0);
v_resultType_519_ = lean_ctor_get(v_cases_517_, 1);
v_discr_520_ = lean_ctor_get(v_cases_517_, 2);
v_alts_521_ = lean_ctor_get(v_cases_517_, 3);
v_isSharedCheck_573_ = !lean_is_exclusive(v_cases_517_);
if (v_isSharedCheck_573_ == 0)
{
v___x_523_ = v_cases_517_;
v_isShared_524_ = v_isSharedCheck_573_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_alts_521_);
lean_inc(v_discr_520_);
lean_inc(v_resultType_519_);
lean_inc(v_typeName_518_);
lean_dec(v_cases_517_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_573_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
size_t v_sz_525_; size_t v___x_526_; lean_object* v___x_527_; 
v_sz_525_ = lean_array_size(v_alts_521_);
v___x_526_ = ((size_t)0ULL);
lean_inc_ref(v_alts_521_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_152_, v_w_153_, v_sz_525_, v___x_526_, v_alts_521_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_564_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_564_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_564_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_564_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___y_533_; uint8_t v___y_534_; lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___y_544_; size_t v___x_550_; size_t v___x_551_; uint8_t v___x_552_; 
v___x_540_ = l_Array_unzip___redArg(v_a_528_);
lean_dec(v_a_528_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_fst_541_);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
lean_inc(v_snd_542_);
lean_dec_ref(v___x_540_);
v___x_550_ = lean_ptr_addr(v_alts_521_);
lean_dec_ref(v_alts_521_);
v___x_551_ = lean_ptr_addr(v_fst_541_);
v___x_552_ = lean_usize_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_562_; 
v_isSharedCheck_562_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_563_);
v___x_554_ = v_c_154_;
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
else
{
lean_dec(v_c_154_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 3, v_fst_541_);
v___x_557_ = v___x_523_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_typeName_518_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_resultType_519_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_discr_520_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_fst_541_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
v___y_544_ = v___x_559_;
goto v___jp_543_;
}
}
}
}
else
{
lean_dec(v_fst_541_);
lean_del_object(v___x_523_);
lean_dec(v_discr_520_);
lean_dec_ref(v_resultType_519_);
lean_dec(v_typeName_518_);
v___y_544_ = v_c_154_;
goto v___jp_543_;
}
v___jp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_box(v___y_534_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_536_);
v___x_538_ = v___x_530_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_array_get_size(v_snd_542_);
v___x_547_ = lean_nat_dec_lt(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec(v_snd_542_);
v___y_533_ = v___y_544_;
v___y_534_ = v___x_547_;
goto v___jp_532_;
}
else
{
if (v___x_547_ == 0)
{
lean_dec(v_snd_542_);
v___y_533_ = v___y_544_;
v___y_534_ = v___x_547_;
goto v___jp_532_;
}
else
{
size_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_usize_of_nat(v___x_546_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_542_, v___x_526_, v___x_548_);
lean_dec(v_snd_542_);
v___y_533_ = v___y_544_;
v___y_534_ = v___x_549_;
goto v___jp_532_;
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_523_);
lean_dec_ref(v_alts_521_);
lean_dec(v_discr_520_);
lean_dec_ref(v_resultType_519_);
lean_dec(v_typeName_518_);
lean_dec_ref_known(v_c_154_, 1);
v_a_565_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_527_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_527_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
case 5:
{
uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_w_153_);
v___x_574_ = 0;
v___x_575_ = lean_box(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_c_154_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
case 6:
{
uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_w_153_);
v___x_578_ = 0;
v___x_579_ = lean_box(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_c_154_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
case 8:
{
lean_object* v_k_582_; 
v_k_582_ = lean_ctor_get(v_c_154_, 3);
lean_inc_ref(v_k_582_);
v_k_168_ = v_k_582_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
case 9:
{
lean_object* v_k_583_; 
v_k_583_ = lean_ctor_get(v_c_154_, 5);
lean_inc_ref(v_k_583_);
v_k_168_ = v_k_583_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
default: 
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v_c_154_);
lean_dec(v_w_153_);
v___x_584_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
v___x_585_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_584_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
return v___x_585_;
}
}
v___jp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_box(v___y_162_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
v___jp_167_:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_152_, v_w_153_, v_k_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
switch(lean_obj_tag(v_c_154_))
{
case 0:
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v_decl_178_; lean_object* v_k_179_; size_t v___x_180_; size_t v___x_181_; uint8_t v___x_182_; 
v_fst_176_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_177_);
lean_dec(v_a_175_);
v_decl_178_ = lean_ctor_get(v_c_154_, 0);
v_k_179_ = lean_ctor_get(v_c_154_, 1);
v___x_180_ = lean_ptr_addr(v_k_179_);
v___x_181_ = lean_ptr_addr(v_fst_176_);
v___x_182_ = lean_usize_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
lean_inc_ref(v_decl_178_);
v_isSharedCheck_190_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_191_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_192_);
v___x_184_ = v_c_154_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_c_154_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_fst_176_);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_decl_178_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_fst_176_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
uint8_t v___x_188_; 
v___x_188_ = lean_unbox(v_snd_177_);
lean_dec(v_snd_177_);
v___y_162_ = v___x_188_;
v___y_163_ = v___x_187_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_193_; 
lean_dec(v_fst_176_);
v___x_193_ = lean_unbox(v_snd_177_);
lean_dec(v_snd_177_);
v___y_162_ = v___x_193_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 1:
{
lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v_decl_196_; lean_object* v_k_197_; size_t v___x_198_; size_t v___x_199_; uint8_t v___x_200_; 
v_fst_194_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_194_);
v_snd_195_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_195_);
lean_dec(v_a_175_);
v_decl_196_ = lean_ctor_get(v_c_154_, 0);
v_k_197_ = lean_ctor_get(v_c_154_, 1);
v___x_198_ = lean_ptr_addr(v_k_197_);
v___x_199_ = lean_ptr_addr(v_fst_194_);
v___x_200_ = lean_usize_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
lean_inc_ref(v_decl_196_);
v_isSharedCheck_208_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_209_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_210_);
v___x_202_ = v_c_154_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_c_154_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_fst_194_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_decl_196_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_fst_194_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
uint8_t v___x_206_; 
v___x_206_ = lean_unbox(v_snd_195_);
lean_dec(v_snd_195_);
v___y_162_ = v___x_206_;
v___y_163_ = v___x_205_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_211_; 
lean_dec(v_fst_194_);
v___x_211_ = lean_unbox(v_snd_195_);
lean_dec(v_snd_195_);
v___y_162_ = v___x_211_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 2:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v_decl_214_; lean_object* v_k_215_; size_t v___x_216_; size_t v___x_217_; uint8_t v___x_218_; 
v_fst_212_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_213_);
lean_dec(v_a_175_);
v_decl_214_ = lean_ctor_get(v_c_154_, 0);
v_k_215_ = lean_ctor_get(v_c_154_, 1);
v___x_216_ = lean_ptr_addr(v_k_215_);
v___x_217_ = lean_ptr_addr(v_fst_212_);
v___x_218_ = lean_usize_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
lean_inc_ref(v_decl_214_);
v_isSharedCheck_226_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; 
v_unused_227_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_228_);
v___x_220_ = v_c_154_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_c_154_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_fst_212_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_decl_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_fst_212_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_snd_213_);
lean_dec(v_snd_213_);
v___y_162_ = v___x_224_;
v___y_163_ = v___x_223_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_229_; 
lean_dec(v_fst_212_);
v___x_229_ = lean_unbox(v_snd_213_);
lean_dec(v_snd_213_);
v___y_162_ = v___x_229_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 7:
{
lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v_fvarId_232_; lean_object* v_i_233_; lean_object* v_y_234_; lean_object* v_k_235_; size_t v___x_236_; size_t v___x_237_; uint8_t v___x_238_; 
v_fst_230_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_230_);
v_snd_231_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_231_);
lean_dec(v_a_175_);
v_fvarId_232_ = lean_ctor_get(v_c_154_, 0);
v_i_233_ = lean_ctor_get(v_c_154_, 1);
v_y_234_ = lean_ctor_get(v_c_154_, 2);
v_k_235_ = lean_ctor_get(v_c_154_, 3);
v___x_236_ = lean_ptr_addr(v_k_235_);
v___x_237_ = lean_ptr_addr(v_fst_230_);
v___x_238_ = lean_usize_dec_eq(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
lean_inc(v_y_234_);
lean_inc(v_i_233_);
lean_inc(v_fvarId_232_);
v_isSharedCheck_246_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; 
v_unused_247_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_250_);
v___x_240_ = v_c_154_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_c_154_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v_fst_230_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_fvarId_232_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_i_233_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_y_234_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_fst_230_);
v___x_243_ = v_reuseFailAlloc_245_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_snd_231_);
lean_dec(v_snd_231_);
v___y_162_ = v___x_244_;
v___y_163_ = v___x_243_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_251_; 
lean_dec(v_fst_230_);
v___x_251_ = lean_unbox(v_snd_231_);
lean_dec(v_snd_231_);
v___y_162_ = v___x_251_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 9:
{
lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v_fvarId_254_; lean_object* v_i_255_; lean_object* v_offset_256_; lean_object* v_y_257_; lean_object* v_ty_258_; lean_object* v_k_259_; size_t v___x_260_; size_t v___x_261_; uint8_t v___x_262_; 
v_fst_252_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_252_);
v_snd_253_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_253_);
lean_dec(v_a_175_);
v_fvarId_254_ = lean_ctor_get(v_c_154_, 0);
v_i_255_ = lean_ctor_get(v_c_154_, 1);
v_offset_256_ = lean_ctor_get(v_c_154_, 2);
v_y_257_ = lean_ctor_get(v_c_154_, 3);
v_ty_258_ = lean_ctor_get(v_c_154_, 4);
v_k_259_ = lean_ctor_get(v_c_154_, 5);
v___x_260_ = lean_ptr_addr(v_k_259_);
v___x_261_ = lean_ptr_addr(v_fst_252_);
v___x_262_ = lean_usize_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
lean_inc_ref(v_ty_258_);
lean_inc(v_y_257_);
lean_inc(v_offset_256_);
lean_inc(v_i_255_);
lean_inc(v_fvarId_254_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_271_ = lean_ctor_get(v_c_154_, 5);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_c_154_, 4);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_276_);
v___x_264_ = v_c_154_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_c_154_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 5, v_fst_252_);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_fvarId_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_i_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_offset_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_y_257_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_ty_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_fst_252_);
v___x_267_ = v_reuseFailAlloc_269_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_snd_253_);
lean_dec(v_snd_253_);
v___y_162_ = v___x_268_;
v___y_163_ = v___x_267_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_277_; 
lean_dec(v_fst_252_);
v___x_277_ = lean_unbox(v_snd_253_);
lean_dec(v_snd_253_);
v___y_162_ = v___x_277_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 8:
{
lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v_fvarId_280_; lean_object* v_i_281_; lean_object* v_y_282_; lean_object* v_k_283_; size_t v___x_284_; size_t v___x_285_; uint8_t v___x_286_; 
v_fst_278_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_278_);
v_snd_279_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_279_);
lean_dec(v_a_175_);
v_fvarId_280_ = lean_ctor_get(v_c_154_, 0);
v_i_281_ = lean_ctor_get(v_c_154_, 1);
v_y_282_ = lean_ctor_get(v_c_154_, 2);
v_k_283_ = lean_ctor_get(v_c_154_, 3);
v___x_284_ = lean_ptr_addr(v_k_283_);
v___x_285_ = lean_ptr_addr(v_fst_278_);
v___x_286_ = lean_usize_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
lean_inc(v_y_282_);
lean_inc(v_i_281_);
lean_inc(v_fvarId_280_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_295_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_298_);
v___x_288_ = v_c_154_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_c_154_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 3, v_fst_278_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_fvarId_280_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_i_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_y_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_fst_278_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
uint8_t v___x_292_; 
v___x_292_ = lean_unbox(v_snd_279_);
lean_dec(v_snd_279_);
v___y_162_ = v___x_292_;
v___y_163_ = v___x_291_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_299_; 
lean_dec(v_fst_278_);
v___x_299_ = lean_unbox(v_snd_279_);
lean_dec(v_snd_279_);
v___y_162_ = v___x_299_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 10:
{
lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v_fvarId_302_; lean_object* v_cidx_303_; lean_object* v_k_304_; size_t v___x_305_; size_t v___x_306_; uint8_t v___x_307_; 
v_fst_300_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_300_);
v_snd_301_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_301_);
lean_dec(v_a_175_);
v_fvarId_302_ = lean_ctor_get(v_c_154_, 0);
v_cidx_303_ = lean_ctor_get(v_c_154_, 1);
v_k_304_ = lean_ctor_get(v_c_154_, 2);
v___x_305_ = lean_ptr_addr(v_k_304_);
v___x_306_ = lean_ptr_addr(v_fst_300_);
v___x_307_ = lean_usize_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
lean_inc(v_cidx_303_);
lean_inc(v_fvarId_302_);
v_isSharedCheck_315_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_316_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_318_);
v___x_309_ = v_c_154_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_dec(v_c_154_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 2, v_fst_300_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_fvarId_302_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_cidx_303_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_fst_300_);
v___x_312_ = v_reuseFailAlloc_314_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
uint8_t v___x_313_; 
v___x_313_ = lean_unbox(v_snd_301_);
lean_dec(v_snd_301_);
v___y_162_ = v___x_313_;
v___y_163_ = v___x_312_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_319_; 
lean_dec(v_fst_300_);
v___x_319_ = lean_unbox(v_snd_301_);
lean_dec(v_snd_301_);
v___y_162_ = v___x_319_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 11:
{
lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v_fvarId_322_; lean_object* v_n_323_; uint8_t v_check_324_; uint8_t v_persistent_325_; lean_object* v_k_326_; size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v_fst_320_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_321_);
lean_dec(v_a_175_);
v_fvarId_322_ = lean_ctor_get(v_c_154_, 0);
v_n_323_ = lean_ctor_get(v_c_154_, 1);
v_check_324_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*3);
v_persistent_325_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*3 + 1);
v_k_326_ = lean_ctor_get(v_c_154_, 2);
v___x_327_ = lean_ptr_addr(v_k_326_);
v___x_328_ = lean_ptr_addr(v_fst_320_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
lean_inc(v_n_323_);
lean_inc(v_fvarId_322_);
v_isSharedCheck_337_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_338_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_340_);
v___x_331_ = v_c_154_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_c_154_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 2, v_fst_320_);
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_fvarId_322_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_n_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_fst_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*3, v_check_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*3 + 1, v_persistent_325_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
uint8_t v___x_335_; 
v___x_335_ = lean_unbox(v_snd_321_);
lean_dec(v_snd_321_);
v___y_162_ = v___x_335_;
v___y_163_ = v___x_334_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_341_; 
lean_dec(v_fst_320_);
v___x_341_ = lean_unbox(v_snd_321_);
lean_dec(v_snd_321_);
v___y_162_ = v___x_341_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 12:
{
lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v_fvarId_344_; lean_object* v_n_345_; uint8_t v_check_346_; uint8_t v_persistent_347_; lean_object* v_objs_x3f_348_; lean_object* v_k_349_; size_t v___x_350_; size_t v___x_351_; uint8_t v___x_352_; 
v_fst_342_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_342_);
v_snd_343_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_343_);
lean_dec(v_a_175_);
v_fvarId_344_ = lean_ctor_get(v_c_154_, 0);
v_n_345_ = lean_ctor_get(v_c_154_, 1);
v_check_346_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*4);
v_persistent_347_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*4 + 1);
v_objs_x3f_348_ = lean_ctor_get(v_c_154_, 2);
v_k_349_ = lean_ctor_get(v_c_154_, 3);
v___x_350_ = lean_ptr_addr(v_k_349_);
v___x_351_ = lean_ptr_addr(v_fst_342_);
v___x_352_ = lean_usize_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
lean_inc(v_objs_x3f_348_);
lean_inc(v_n_345_);
lean_inc(v_fvarId_344_);
v_isSharedCheck_360_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_361_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_364_);
v___x_354_ = v_c_154_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_c_154_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 3, v_fst_342_);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_fvarId_344_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_n_345_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_objs_x3f_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_fst_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*4, v_check_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*4 + 1, v_persistent_347_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
uint8_t v___x_358_; 
v___x_358_ = lean_unbox(v_snd_343_);
lean_dec(v_snd_343_);
v___y_162_ = v___x_358_;
v___y_163_ = v___x_357_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_365_; 
lean_dec(v_fst_342_);
v___x_365_ = lean_unbox(v_snd_343_);
lean_dec(v_snd_343_);
v___y_162_ = v___x_365_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 13:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v_fvarId_368_; lean_object* v_k_369_; size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v_fst_366_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_367_);
lean_dec(v_a_175_);
v_fvarId_368_ = lean_ctor_get(v_c_154_, 0);
v_k_369_ = lean_ctor_get(v_c_154_, 1);
v___x_370_ = lean_ptr_addr(v_k_369_);
v___x_371_ = lean_ptr_addr(v_fst_366_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
lean_inc(v_fvarId_368_);
v_isSharedCheck_380_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_381_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_382_);
v___x_374_ = v_c_154_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_c_154_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v_fst_366_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_fvarId_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_fst_366_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
uint8_t v___x_378_; 
v___x_378_ = lean_unbox(v_snd_367_);
lean_dec(v_snd_367_);
v___y_162_ = v___x_378_;
v___y_163_ = v___x_377_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_383_; 
lean_dec(v_fst_366_);
v___x_383_ = lean_unbox(v_snd_367_);
lean_dec(v_snd_367_);
v___y_162_ = v___x_383_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
default: 
{
lean_object* v_snd_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
lean_dec_ref(v_c_154_);
v_snd_384_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_384_);
lean_dec(v_a_175_);
v___x_385_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
v___x_386_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(v___x_385_);
v___x_387_ = lean_unbox(v_snd_384_);
lean_dec(v_snd_384_);
v___y_162_ = v___x_387_;
v___y_163_ = v___x_386_;
goto v___jp_161_;
}
}
}
else
{
lean_dec_ref(v_c_154_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* v_info_586_, lean_object* v_w_587_, size_t v_sz_588_, size_t v_i_589_, lean_object* v_bs_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_lt(v_i_589_, v_sz_588_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v_w_587_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v_bs_590_);
return v___x_598_;
}
else
{
lean_object* v_v_599_; lean_object* v___x_600_; lean_object* v_bs_x27_601_; lean_object* v___y_603_; 
v_v_599_ = lean_array_uget(v_bs_590_, v_i_589_);
v___x_600_ = lean_unsigned_to_nat(0u);
v_bs_x27_601_ = lean_array_uset(v_bs_590_, v_i_589_, v___x_600_);
switch(lean_obj_tag(v_v_599_))
{
case 0:
{
lean_object* v_code_628_; 
v_code_628_ = lean_ctor_get(v_v_599_, 2);
lean_inc_ref(v_code_628_);
v___y_603_ = v_code_628_;
goto v___jp_602_;
}
case 1:
{
lean_object* v_code_629_; 
v_code_629_ = lean_ctor_get(v_v_599_, 1);
lean_inc_ref(v_code_629_);
v___y_603_ = v_code_629_;
goto v___jp_602_;
}
default: 
{
lean_object* v_code_630_; 
v_code_630_ = lean_ctor_get(v_v_599_, 0);
lean_inc_ref(v_code_630_);
v___y_603_ = v_code_630_;
goto v___jp_602_;
}
}
v___jp_602_:
{
lean_object* v___x_604_; 
lean_inc(v_w_587_);
v___x_604_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_586_, v_w_587_, v___y_603_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_619_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_fst_606_ = lean_ctor_get(v_a_605_, 0);
v_snd_607_ = lean_ctor_get(v_a_605_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_619_ == 0)
{
v___x_609_ = v_a_605_;
v_isShared_610_ = v_isSharedCheck_619_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
lean_dec(v_a_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_619_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_599_, v_fst_606_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_607_);
v___x_613_ = v_reuseFailAlloc_618_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_589_, v___x_614_);
v___x_616_ = lean_array_uset(v_bs_x27_601_, v_i_589_, v___x_613_);
v_i_589_ = v___x_615_;
v_bs_590_ = v___x_616_;
goto _start;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_bs_x27_601_);
lean_dec(v_v_599_);
lean_dec(v_w_587_);
v_a_620_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_604_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_604_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* v_info_631_, lean_object* v_w_632_, lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_bs_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_643_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_631_, v_w_632_, v_sz_boxed_642_, v_i_boxed_643_, v_bs_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v_info_631_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* v_info_645_, lean_object* v_w_646_, lean_object* v_c_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_645_, v_w_646_, v_c_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_info_645_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v_ngen_658_; lean_object* v_namePrefix_659_; lean_object* v_idx_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_689_; 
v___x_657_ = lean_st_ref_get(v___y_655_);
v_ngen_658_ = lean_ctor_get(v___x_657_, 2);
lean_inc_ref(v_ngen_658_);
lean_dec(v___x_657_);
v_namePrefix_659_ = lean_ctor_get(v_ngen_658_, 0);
v_idx_660_ = lean_ctor_get(v_ngen_658_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_ngen_658_);
if (v_isSharedCheck_689_ == 0)
{
v___x_662_ = v_ngen_658_;
v_isShared_663_ = v_isSharedCheck_689_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_idx_660_);
lean_inc(v_namePrefix_659_);
lean_dec(v_ngen_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_689_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v_env_665_; lean_object* v_nextMacroScope_666_; lean_object* v_auxDeclNGen_667_; lean_object* v_traceState_668_; lean_object* v_cache_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_687_; 
v___x_664_ = lean_st_ref_take(v___y_655_);
v_env_665_ = lean_ctor_get(v___x_664_, 0);
v_nextMacroScope_666_ = lean_ctor_get(v___x_664_, 1);
v_auxDeclNGen_667_ = lean_ctor_get(v___x_664_, 3);
v_traceState_668_ = lean_ctor_get(v___x_664_, 4);
v_cache_669_ = lean_ctor_get(v___x_664_, 5);
v_messages_670_ = lean_ctor_get(v___x_664_, 6);
v_infoState_671_ = lean_ctor_get(v___x_664_, 7);
v_snapshotTasks_672_ = lean_ctor_get(v___x_664_, 8);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_664_, 2);
lean_dec(v_unused_688_);
v___x_674_ = v___x_664_;
v_isShared_675_ = v_isSharedCheck_687_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snapshotTasks_672_);
lean_inc(v_infoState_671_);
lean_inc(v_messages_670_);
lean_inc(v_cache_669_);
lean_inc(v_traceState_668_);
lean_inc(v_auxDeclNGen_667_);
lean_inc(v_nextMacroScope_666_);
lean_inc(v_env_665_);
lean_dec(v___x_664_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_687_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_r_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_inc(v_idx_660_);
lean_inc(v_namePrefix_659_);
v_r_676_ = l_Lean_Name_num___override(v_namePrefix_659_, v_idx_660_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_idx_660_, v___x_677_);
lean_dec(v_idx_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_678_);
v___x_680_ = v___x_662_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_namePrefix_659_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_686_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 2, v___x_680_);
v___x_682_ = v___x_674_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_env_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_nextMacroScope_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_auxDeclNGen_667_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_traceState_668_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v_messages_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_infoState_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_snapshotTasks_672_);
v___x_682_ = v_reuseFailAlloc_685_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_st_ref_put(v___y_655_, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_r_676_);
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_690_);
lean_dec(v___y_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v___x_699_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_697_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_714_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(0);
v___x_722_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
v___x_723_ = l_Lean_Expr_const___override(v___x_722_, v___x_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* v_x_724_, lean_object* v_info_725_, lean_object* v_c_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_a_734_, 2);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_725_, v_a_734_, v_c_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_790_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_790_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_790_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_790_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_snd_740_; uint8_t v___x_741_; 
v_snd_740_ = lean_ctor_get(v_a_736_, 1);
v___x_741_ = lean_unbox(v_snd_740_);
if (v___x_741_ == 0)
{
lean_object* v_fst_742_; lean_object* v___x_744_; 
lean_dec(v_a_734_);
lean_dec(v_x_724_);
v_fst_742_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_742_);
lean_dec(v_a_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_fst_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v_fst_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_788_; 
lean_del_object(v___x_738_);
v_fst_746_ = lean_ctor_get(v_a_736_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_736_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_a_736_, 1);
lean_dec(v_unused_789_);
v___x_748_ = v_a_736_;
v_isShared_749_ = v_isSharedCheck_788_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_fst_746_);
lean_dec(v_a_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_788_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
v___x_751_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_750_, v_a_729_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_779_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_779_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_779_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_779_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_size_756_; lean_object* v___x_757_; lean_object* v_lctx_758_; lean_object* v_nextIdx_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_778_; 
v_size_756_ = lean_ctor_get(v_info_725_, 2);
v___x_757_ = lean_st_ref_take(v_a_729_);
v_lctx_758_ = lean_ctor_get(v___x_757_, 0);
v_nextIdx_759_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_778_ == 0)
{
v___x_761_ = v___x_757_;
v_isShared_762_ = v_isSharedCheck_778_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_nextIdx_759_);
lean_inc(v_lctx_758_);
lean_dec(v___x_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_778_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; lean_object* v___x_765_; 
v___x_763_ = 1;
lean_inc(v_size_756_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 11);
lean_ctor_set(v___x_748_, 1, v_x_724_);
lean_ctor_set(v___x_748_, 0, v_size_756_);
v___x_765_ = v___x_748_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_size_756_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_x_724_);
v___x_765_ = v_reuseFailAlloc_777_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_766_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
v___x_767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_767_, 0, v_a_734_);
lean_ctor_set(v___x_767_, 1, v_a_752_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
lean_ctor_set(v___x_767_, 3, v___x_765_);
lean_inc_ref(v___x_767_);
v___x_768_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_763_, v_lctx_758_, v___x_767_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_768_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_nextIdx_759_);
v___x_770_ = v_reuseFailAlloc_776_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_st_ref_put(v_a_729_, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_767_);
lean_ctor_set(v___x_772_, 1, v_fst_746_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_772_);
v___x_774_ = v___x_754_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_del_object(v___x_748_);
lean_dec(v_fst_746_);
lean_dec(v_a_734_);
lean_dec(v_x_724_);
v_a_780_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_751_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_751_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_734_);
lean_dec(v_x_724_);
v_a_791_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_735_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_735_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_c_726_);
lean_dec(v_x_724_);
v_a_799_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_733_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_733_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* v_x_807_, lean_object* v_info_808_, lean_object* v_c_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_807_, v_info_808_, v_c_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_info_808_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* v_x_831_, lean_object* v_as_832_, size_t v_i_833_, size_t v_stop_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_eq(v_i_833_, v_stop_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_836_ = lean_array_uget_borrowed(v_as_832_, v_i_833_);
v___x_837_ = 1;
lean_inc(v_x_831_);
v___x_838_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_831_);
v___x_839_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_837_, v___x_836_, v___x_838_);
lean_dec(v___x_838_);
if (v___x_839_ == 0)
{
size_t v___x_840_; size_t v___x_841_; 
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_833_, v___x_840_);
v_i_833_ = v___x_841_;
goto _start;
}
else
{
lean_dec(v_x_831_);
return v___x_839_;
}
}
else
{
uint8_t v___x_843_; 
lean_dec(v_x_831_);
v___x_843_ = 0;
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* v_x_844_, lean_object* v_as_845_, lean_object* v_i_846_, lean_object* v_stop_847_){
_start:
{
size_t v_i_boxed_848_; size_t v_stop_boxed_849_; uint8_t v_res_850_; lean_object* v_r_851_; 
v_i_boxed_848_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_stop_boxed_849_ = lean_unbox_usize(v_stop_847_);
lean_dec(v_stop_847_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_844_, v_as_845_, v_i_boxed_848_, v_stop_boxed_849_);
lean_dec_ref(v_as_845_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* v_instr_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_instr_852_) == 0)
{
lean_object* v_decl_854_; lean_object* v_value_855_; 
v_decl_854_ = lean_ctor_get(v_instr_852_, 0);
v_value_855_ = lean_ctor_get(v_decl_854_, 3);
if (lean_obj_tag(v_value_855_) == 5)
{
lean_object* v_args_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_args_856_ = lean_ctor_get(v_value_855_, 1);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_array_get_size(v_args_856_);
v___x_859_ = lean_nat_dec_lt(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_dec(v_x_853_);
return v___x_859_;
}
else
{
if (v___x_859_ == 0)
{
lean_dec(v_x_853_);
return v___x_859_;
}
else
{
size_t v___x_860_; size_t v___x_861_; uint8_t v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_858_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_853_, v_args_856_, v___x_860_, v___x_861_);
return v___x_862_;
}
}
}
else
{
uint8_t v___x_863_; 
lean_dec(v_x_853_);
v___x_863_ = 0;
return v___x_863_;
}
}
else
{
uint8_t v___x_864_; 
lean_dec(v_x_853_);
v___x_864_ = 0;
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* v_instr_865_, lean_object* v_x_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_865_, v_x_866_);
lean_dec_ref(v_instr_865_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t v_x_869_){
_start:
{
switch(v_x_869_)
{
case 0:
{
lean_object* v___x_870_; 
v___x_870_ = lean_unsigned_to_nat(0u);
return v___x_870_;
}
case 1:
{
lean_object* v___x_871_; 
v___x_871_ = lean_unsigned_to_nat(1u);
return v___x_871_;
}
default: 
{
lean_object* v___x_872_; 
v___x_872_ = lean_unsigned_to_nat(2u);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object* v_x_873_){
_start:
{
uint8_t v_x_boxed_874_; lean_object* v_res_875_; 
v_x_boxed_874_ = lean_unbox(v_x_873_);
v_res_875_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_boxed_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* v_k_876_){
_start:
{
lean_inc(v_k_876_);
return v_k_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* v_k_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_877_);
lean_dec(v_k_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* v_motive_879_, lean_object* v_ctorIdx_880_, uint8_t v_t_881_, lean_object* v_h_882_, lean_object* v_k_883_){
_start:
{
lean_inc(v_k_883_);
return v_k_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* v_motive_884_, lean_object* v_ctorIdx_885_, lean_object* v_t_886_, lean_object* v_h_887_, lean_object* v_k_888_){
_start:
{
uint8_t v_t_boxed_889_; lean_object* v_res_890_; 
v_t_boxed_889_ = lean_unbox(v_t_886_);
v_res_890_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(v_motive_884_, v_ctorIdx_885_, v_t_boxed_889_, v_h_887_, v_k_888_);
lean_dec(v_k_888_);
lean_dec(v_ctorIdx_885_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* v_ownedArg_891_){
_start:
{
lean_inc(v_ownedArg_891_);
return v_ownedArg_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* v_ownedArg_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_892_);
lean_dec(v_ownedArg_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* v_motive_894_, uint8_t v_t_895_, lean_object* v_h_896_, lean_object* v_ownedArg_897_){
_start:
{
lean_inc(v_ownedArg_897_);
return v_ownedArg_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* v_motive_898_, lean_object* v_t_899_, lean_object* v_h_900_, lean_object* v_ownedArg_901_){
_start:
{
uint8_t v_t_boxed_902_; lean_object* v_res_903_; 
v_t_boxed_902_ = lean_unbox(v_t_899_);
v_res_903_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_898_, v_t_boxed_902_, v_h_900_, v_ownedArg_901_);
lean_dec(v_ownedArg_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* v_other_904_){
_start:
{
lean_inc(v_other_904_);
return v_other_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* v_other_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_905_);
lean_dec(v_other_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* v_motive_907_, uint8_t v_t_908_, lean_object* v_h_909_, lean_object* v_other_910_){
_start:
{
lean_inc(v_other_910_);
return v_other_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* v_motive_911_, lean_object* v_t_912_, lean_object* v_h_913_, lean_object* v_other_914_){
_start:
{
uint8_t v_t_boxed_915_; lean_object* v_res_916_; 
v_t_boxed_915_ = lean_unbox(v_t_912_);
v_res_916_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_911_, v_t_boxed_915_, v_h_913_, v_other_914_);
lean_dec(v_other_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* v_none_917_){
_start:
{
lean_inc(v_none_917_);
return v_none_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* v_none_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_918_);
lean_dec(v_none_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* v_motive_920_, uint8_t v_t_921_, lean_object* v_h_922_, lean_object* v_none_923_){
_start:
{
lean_inc(v_none_923_);
return v_none_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* v_motive_924_, lean_object* v_t_925_, lean_object* v_h_926_, lean_object* v_none_927_){
_start:
{
uint8_t v_t_boxed_928_; lean_object* v_res_929_; 
v_t_boxed_928_ = lean_unbox(v_t_925_);
v_res_929_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(v_motive_924_, v_t_boxed_928_, v_h_926_, v_none_927_);
lean_dec(v_none_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* v_x_930_, lean_object* v_as_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_b_934_){
_start:
{
lean_object* v_a_937_; uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_934_);
return v___x_942_;
}
else
{
lean_object* v_snd_943_; lean_object* v_fst_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_988_; 
v_snd_943_ = lean_ctor_get(v_b_934_, 1);
v_fst_944_ = lean_ctor_get(v_b_934_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_b_934_);
if (v_isSharedCheck_988_ == 0)
{
v___x_946_ = v_b_934_;
v_isShared_947_ = v_isSharedCheck_988_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_943_);
lean_inc(v_fst_944_);
lean_dec(v_b_934_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_988_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_array_948_; lean_object* v_start_949_; lean_object* v_stop_950_; uint8_t v___x_951_; 
v_array_948_ = lean_ctor_get(v_snd_943_, 0);
v_start_949_ = lean_ctor_get(v_snd_943_, 1);
v_stop_950_ = lean_ctor_get(v_snd_943_, 2);
v___x_951_ = lean_nat_dec_lt(v_start_949_, v_stop_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_953_; 
if (v_isShared_947_ == 0)
{
v___x_953_ = v___x_946_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_fst_944_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_snd_943_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
else
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_984_; 
lean_inc(v_stop_950_);
lean_inc(v_start_949_);
lean_inc_ref(v_array_948_);
v_isSharedCheck_984_ = !lean_is_exclusive(v_snd_943_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_985_ = lean_ctor_get(v_snd_943_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_snd_943_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_snd_943_, 0);
lean_dec(v_unused_987_);
v___x_957_ = v_snd_943_;
v_isShared_958_ = v_isSharedCheck_984_;
goto v_resetjp_956_;
}
else
{
lean_dec(v_snd_943_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_984_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v_a_959_ = lean_array_uget_borrowed(v_as_931_, v_i_933_);
v___x_960_ = lean_array_fget(v_array_948_, v_start_949_);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_start_949_, v___x_961_);
lean_dec(v_start_949_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_962_);
v___x_964_ = v___x_957_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_array_948_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_stop_950_);
v___x_964_ = v_reuseFailAlloc_983_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
uint8_t v___y_966_; 
if (lean_obj_tag(v_a_959_) == 1)
{
lean_object* v_fvarId_971_; uint8_t v___x_972_; 
v_fvarId_971_ = lean_ctor_get(v_a_959_, 0);
v___x_972_ = l_Lean_instBEqFVarId_beq(v_fvarId_971_, v_x_930_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_dec(v___x_960_);
lean_del_object(v___x_946_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_fst_944_);
lean_ctor_set(v___x_973_, 1, v___x_964_);
v_a_937_ = v___x_973_;
goto v___jp_936_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_unbox(v_fst_944_);
switch(v___x_974_)
{
case 0:
{
uint8_t v_borrow_975_; 
v_borrow_975_ = lean_ctor_get_uint8(v___x_960_, sizeof(void*)*3);
lean_dec(v___x_960_);
if (v_borrow_975_ == 0)
{
uint8_t v___x_976_; 
v___x_976_ = lean_unbox(v_fst_944_);
lean_dec(v_fst_944_);
v___y_966_ = v___x_976_;
goto v___jp_965_;
}
else
{
uint8_t v___x_977_; 
lean_dec(v_fst_944_);
v___x_977_ = 1;
v___y_966_ = v___x_977_;
goto v___jp_965_;
}
}
case 1:
{
uint8_t v___x_978_; 
lean_dec(v___x_960_);
v___x_978_ = lean_unbox(v_fst_944_);
lean_dec(v_fst_944_);
v___y_966_ = v___x_978_;
goto v___jp_965_;
}
default: 
{
uint8_t v_borrow_979_; 
lean_dec(v_fst_944_);
v_borrow_979_ = lean_ctor_get_uint8(v___x_960_, sizeof(void*)*3);
lean_dec(v___x_960_);
if (v_borrow_979_ == 0)
{
uint8_t v___x_980_; 
v___x_980_ = 0;
v___y_966_ = v___x_980_;
goto v___jp_965_;
}
else
{
uint8_t v___x_981_; 
v___x_981_ = 1;
v___y_966_ = v___x_981_;
goto v___jp_965_;
}
}
}
}
}
else
{
lean_object* v___x_982_; 
lean_dec(v___x_960_);
lean_del_object(v___x_946_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_fst_944_);
lean_ctor_set(v___x_982_, 1, v___x_964_);
v_a_937_ = v___x_982_;
goto v___jp_936_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_box(v___y_966_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_964_);
lean_ctor_set(v___x_946_, 0, v___x_967_);
v___x_969_ = v___x_946_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
v_a_937_ = v___x_969_;
goto v___jp_936_;
}
}
}
}
}
}
}
v___jp_936_:
{
size_t v___x_938_; size_t v___x_939_; 
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_933_, v___x_938_);
v_i_933_ = v___x_939_;
v_b_934_ = v_a_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* v_x_989_, lean_object* v_as_990_, lean_object* v_sz_991_, lean_object* v_i_992_, lean_object* v_b_993_, lean_object* v___y_994_){
_start:
{
size_t v_sz_boxed_995_; size_t v_i_boxed_996_; lean_object* v_res_997_; 
v_sz_boxed_995_ = lean_unbox_usize(v_sz_991_);
lean_dec(v_sz_991_);
v_i_boxed_996_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_989_, v_as_990_, v_sz_boxed_995_, v_i_boxed_996_, v_b_993_);
lean_dec_ref(v_as_990_);
lean_dec(v_x_989_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* v_instr_998_, lean_object* v_x_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
if (lean_obj_tag(v_instr_998_) == 0)
{
lean_object* v_decl_1016_; lean_object* v_value_1017_; 
v_decl_1016_ = lean_ctor_get(v_instr_998_, 0);
v_value_1017_ = lean_ctor_get(v_decl_1016_, 3);
lean_inc(v_value_1017_);
switch(lean_obj_tag(v_value_1017_))
{
case 9:
{
lean_object* v_fn_1018_; lean_object* v_args_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref_known(v_instr_998_, 1);
v_fn_1018_ = lean_ctor_get(v_value_1017_, 0);
v_args_1019_ = lean_ctor_get(v_value_1017_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_value_1017_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1021_ = v_value_1017_;
v_isShared_1022_ = v_isSharedCheck_1081_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_args_1019_);
lean_inc(v_fn_1018_);
lean_dec(v_value_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1081_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
lean_inc_ref(v_args_1019_);
lean_inc(v_fn_1018_);
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_fn_1018_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_args_1019_);
v___x_1024_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1018_, v_a_1004_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1071_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1071_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1071_;
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
v_sz_1038_ = lean_array_size(v_args_1019_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_999_, v_args_1019_, v_sz_1038_, v___x_1039_, v___x_1037_);
lean_dec_ref(v_args_1019_);
lean_dec(v_x_999_);
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
uint8_t v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
lean_dec(v_a_1026_);
lean_dec_ref(v_args_1019_);
v___x_1058_ = 1;
v___x_1059_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_999_);
v___x_1060_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1058_, v___x_1024_, v___x_1059_);
lean_dec(v___x_1059_);
lean_dec_ref(v___x_1024_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1061_ = 2;
v___x_1062_ = lean_box(v___x_1061_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1062_);
v___x_1064_ = v___x_1028_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1066_ = 0;
v___x_1067_ = lean_box(v___x_1066_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1067_);
v___x_1069_ = v___x_1028_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_args_1019_);
lean_dec(v_x_999_);
v_a_1072_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1025_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1025_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
case 10:
{
lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1107_; 
v_isSharedCheck_1107_ = !lean_is_exclusive(v_instr_998_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_instr_998_, 0);
lean_dec(v_unused_1108_);
v___x_1083_ = v_instr_998_;
v_isShared_1084_ = v_isSharedCheck_1107_;
goto v_resetjp_1082_;
}
else
{
lean_dec(v_instr_998_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1107_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_fn_1085_; lean_object* v_args_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1106_; 
v_fn_1085_ = lean_ctor_get(v_value_1017_, 0);
v_args_1086_ = lean_ctor_get(v_value_1017_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_value_1017_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1088_ = v_value_1017_;
v_isShared_1089_ = v_isSharedCheck_1106_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_args_1086_);
lean_inc(v_fn_1085_);
lean_dec(v_value_1017_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1106_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint8_t v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = 1;
if (v_isShared_1089_ == 0)
{
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_fn_1085_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_args_1086_);
v___x_1092_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_999_);
v___x_1094_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1090_, v___x_1092_, v___x_1093_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1092_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1095_ = 2;
v___x_1096_ = lean_box(v___x_1095_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1096_);
v___x_1098_ = v___x_1083_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = 0;
v___x_1101_ = lean_box(v___x_1100_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1101_);
v___x_1103_ = v___x_1083_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1134_; 
v_isSharedCheck_1134_ = !lean_is_exclusive(v_instr_998_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v_instr_998_, 0);
lean_dec(v_unused_1135_);
v___x_1110_ = v_instr_998_;
v_isShared_1111_ = v_isSharedCheck_1134_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v_instr_998_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1134_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_fvarId_1112_; lean_object* v_args_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1133_; 
v_fvarId_1112_ = lean_ctor_get(v_value_1017_, 0);
v_args_1113_ = lean_ctor_get(v_value_1017_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_value_1017_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1115_ = v_value_1017_;
v_isShared_1116_ = v_isSharedCheck_1133_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_args_1113_);
lean_inc(v_fvarId_1112_);
lean_dec(v_value_1017_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1133_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = 1;
if (v_isShared_1116_ == 0)
{
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_fvarId_1112_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_args_1113_);
v___x_1119_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_999_);
v___x_1121_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1117_, v___x_1119_, v___x_1120_);
lean_dec(v___x_1120_);
lean_dec_ref(v___x_1119_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1122_ = 2;
v___x_1123_ = lean_box(v___x_1122_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1123_);
v___x_1125_ = v___x_1110_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
else
{
uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = 0;
v___x_1128_ = lean_box(v___x_1127_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1128_);
v___x_1130_ = v___x_1110_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
default: 
{
lean_dec(v_value_1017_);
goto v___jp_1006_;
}
}
}
else
{
goto v___jp_1006_;
}
v___jp_1006_:
{
uint8_t v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = 1;
v___x_1008_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_999_);
v___x_1009_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_1007_, v_instr_998_, v___x_1008_);
lean_dec(v___x_1008_);
lean_dec_ref(v_instr_998_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = 2;
v___x_1011_ = lean_box(v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
else
{
uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = 1;
v___x_1014_ = lean_box(v___x_1013_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* v_instr_1136_, lean_object* v_x_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1136_, v_x_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* v_x_1145_, lean_object* v_as_1146_, size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1145_, v_as_1146_, v_sz_1147_, v_i_1148_, v_b_1149_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* v_x_1157_, lean_object* v_as_1158_, lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_b_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
size_t v_sz_boxed_1168_; size_t v_i_boxed_1169_; lean_object* v_res_1170_; 
v_sz_boxed_1168_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1169_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1157_, v_as_1158_, v_sz_boxed_1168_, v_i_boxed_1169_, v_b_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec_ref(v_as_1158_);
lean_dec(v_x_1157_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* v_alt_1171_, lean_object* v_f_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___y_1180_; 
switch(lean_obj_tag(v_alt_1171_))
{
case 0:
{
lean_object* v_code_1199_; 
v_code_1199_ = lean_ctor_get(v_alt_1171_, 2);
lean_inc_ref(v_code_1199_);
v___y_1180_ = v_code_1199_;
goto v___jp_1179_;
}
case 1:
{
lean_object* v_code_1200_; 
v_code_1200_ = lean_ctor_get(v_alt_1171_, 1);
lean_inc_ref(v_code_1200_);
v___y_1180_ = v_code_1200_;
goto v___jp_1179_;
}
default: 
{
lean_object* v_code_1201_; 
v_code_1201_ = lean_ctor_get(v_alt_1171_, 0);
lean_inc_ref(v_code_1201_);
v___y_1180_ = v_code_1201_;
goto v___jp_1179_;
}
}
v___jp_1179_:
{
lean_object* v___x_1181_; 
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc_ref(v___y_1173_);
v___x_1181_ = lean_apply_7(v_f_1172_, v___y_1180_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, lean_box(0));
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1190_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1171_, v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_alt_1171_);
v_a_1191_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1181_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1181_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* v_alt_1202_, lean_object* v_f_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1202_, v_f_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* v_x_1211_, lean_object* v_info_1212_, lean_object* v_c_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1211_, v_info_1212_, v_c_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec_ref(v_a_1214_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* v_x_1221_, lean_object* v_info_1222_, lean_object* v_i_1223_, lean_object* v_as_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = lean_array_get_size(v_as_1224_);
v___x_1232_ = lean_nat_dec_lt(v_i_1223_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec(v_i_1223_);
lean_dec_ref(v_info_1222_);
lean_dec(v_x_1221_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_as_1224_);
return v___x_1233_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_a_1234_ = lean_array_fget_borrowed(v_as_1224_, v_i_1223_);
lean_inc_ref(v_info_1222_);
lean_inc(v_x_1221_);
v___x_1235_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(v___x_1235_, 0, v_x_1221_);
lean_closure_set(v___x_1235_, 1, v_info_1222_);
lean_inc(v_a_1234_);
v___x_1236_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_1234_, v___x_1235_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; size_t v___x_1238_; size_t v___x_1239_; uint8_t v___x_1240_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = lean_ptr_addr(v_a_1234_);
v___x_1239_ = lean_ptr_addr(v_a_1237_);
v___x_1240_ = lean_usize_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_add(v_i_1223_, v___x_1241_);
v___x_1243_ = lean_array_fset(v_as_1224_, v_i_1223_, v_a_1237_);
lean_dec(v_i_1223_);
v_i_1223_ = v___x_1242_;
v_as_1224_ = v___x_1243_;
goto _start;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_a_1237_);
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_add(v_i_1223_, v___x_1245_);
lean_dec(v_i_1223_);
v_i_1223_ = v___x_1246_;
goto _start;
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_as_1224_);
lean_dec(v_i_1223_);
lean_dec_ref(v_info_1222_);
lean_dec(v_x_1221_);
v_a_1248_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1236_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1236_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_1258_ = lean_unsigned_to_nat(61u);
v___x_1259_ = lean_unsigned_to_nat(247u);
v___x_1260_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
v___x_1261_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_1262_ = l_mkPanicMessageWithDecl(v___x_1261_, v___x_1260_, v___x_1259_, v___x_1258_, v___x_1257_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* v_x_1263_, lean_object* v_info_1264_, lean_object* v_c_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
switch(lean_obj_tag(v_c_1265_))
{
case 0:
{
lean_object* v_decl_1272_; lean_object* v_k_1273_; uint8_t v___x_1274_; lean_object* v_instr_1275_; uint8_t v___x_1276_; uint8_t v___x_1277_; 
v_decl_1272_ = lean_ctor_get(v_c_1265_, 0);
v_k_1273_ = lean_ctor_get(v_c_1265_, 1);
v___x_1274_ = 1;
v_instr_1275_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1274_, v_c_1265_);
lean_inc(v_x_1263_);
v___x_1276_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1275_, v_x_1263_);
v___x_1277_ = 1;
if (v___x_1276_ == 0)
{
lean_object* v___x_1278_; 
lean_inc_ref(v_k_1273_);
lean_inc_ref(v_info_1264_);
lean_inc(v_x_1263_);
v___x_1278_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1263_, v_info_1264_, v_k_1273_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1396_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1396_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1396_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___y_1284_; lean_object* v_snd_1290_; uint8_t v___x_1291_; 
v_snd_1290_ = lean_ctor_get(v_a_1279_, 1);
v___x_1291_ = lean_unbox(v_snd_1290_);
if (v___x_1291_ == 0)
{
lean_object* v_fst_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1381_; 
lean_inc(v_snd_1290_);
lean_del_object(v___x_1281_);
v_fst_1292_ = lean_ctor_get(v_a_1279_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_a_1279_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_a_1279_, 1);
lean_dec(v_unused_1382_);
v___x_1294_ = v_a_1279_;
v_isShared_1295_ = v_isSharedCheck_1381_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_fst_1292_);
lean_dec(v_a_1279_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1381_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; 
lean_inc(v_x_1263_);
v___x_1296_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1275_, v_x_1263_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1372_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1372_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1372_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___y_1302_; lean_object* v___y_1310_; uint8_t v___x_1314_; 
v___x_1314_ = lean_unbox(v_a_1297_);
lean_dec(v_a_1297_);
switch(v___x_1314_)
{
case 0:
{
size_t v___x_1315_; size_t v___x_1316_; uint8_t v___x_1317_; 
lean_del_object(v___x_1299_);
lean_del_object(v___x_1294_);
lean_dec(v_snd_1290_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1315_ = lean_ptr_addr(v_k_1273_);
v___x_1316_ = lean_ptr_addr(v_fst_1292_);
v___x_1317_ = lean_usize_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_inc_ref(v_decl_1272_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1325_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1326_);
v___x_1319_ = v_c_1265_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v_c_1265_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_fst_1292_);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_decl_1272_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_fst_1292_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v___y_1310_ = v___x_1322_;
goto v___jp_1309_;
}
}
}
else
{
lean_dec(v_fst_1292_);
v___y_1310_ = v_c_1265_;
goto v___jp_1309_;
}
}
case 1:
{
lean_object* v___x_1327_; 
lean_del_object(v___x_1299_);
lean_del_object(v___x_1294_);
lean_dec(v_snd_1290_);
v___x_1327_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1263_, v_info_1264_, v_fst_1292_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_info_1264_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1351_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1351_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1351_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___y_1333_; size_t v___x_1339_; size_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_ptr_addr(v_k_1273_);
v___x_1340_ = lean_ptr_addr(v_a_1328_);
v___x_1341_ = lean_usize_dec_eq(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_inc_ref(v_decl_1272_);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1349_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1350_);
v___x_1343_ = v_c_1265_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v_c_1265_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v_a_1328_);
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_decl_1272_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_a_1328_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v___y_1333_ = v___x_1346_;
goto v___jp_1332_;
}
}
}
else
{
lean_dec(v_a_1328_);
v___y_1333_ = v_c_1265_;
goto v___jp_1332_;
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1334_ = lean_box(v___x_1277_);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___y_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1335_);
v___x_1337_ = v___x_1330_;
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
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref_known(v_c_1265_, 2);
v_a_1352_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1327_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1327_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
default: 
{
size_t v___x_1360_; size_t v___x_1361_; uint8_t v___x_1362_; 
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1360_ = lean_ptr_addr(v_k_1273_);
v___x_1361_ = lean_ptr_addr(v_fst_1292_);
v___x_1362_ = lean_usize_dec_eq(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_inc_ref(v_decl_1272_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1370_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1371_);
v___x_1364_ = v_c_1265_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v_c_1265_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_fst_1292_);
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_decl_1272_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_fst_1292_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
v___y_1302_ = v___x_1367_;
goto v___jp_1301_;
}
}
}
else
{
lean_dec(v_fst_1292_);
v___y_1302_ = v_c_1265_;
goto v___jp_1301_;
}
}
}
v___jp_1301_:
{
lean_object* v___x_1304_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___y_1302_);
v___x_1304_ = v___x_1294_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___y_1302_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_snd_1290_);
v___x_1304_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1304_);
v___x_1306_ = v___x_1299_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
v___jp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(v___x_1277_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___y_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_del_object(v___x_1294_);
lean_dec(v_fst_1292_);
lean_dec(v_snd_1290_);
lean_dec_ref_known(v_c_1265_, 2);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_a_1373_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1296_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1296_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v_fst_1383_; size_t v___x_1384_; size_t v___x_1385_; uint8_t v___x_1386_; 
lean_dec_ref(v_instr_1275_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_fst_1383_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_fst_1383_);
lean_dec(v_a_1279_);
v___x_1384_ = lean_ptr_addr(v_k_1273_);
v___x_1385_ = lean_ptr_addr(v_fst_1383_);
v___x_1386_ = lean_usize_dec_eq(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_inc_ref(v_decl_1272_);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; lean_object* v_unused_1395_; 
v_unused_1394_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1395_);
v___x_1388_ = v_c_1265_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v_c_1265_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_fst_1383_);
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_decl_1272_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_fst_1383_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v___y_1284_ = v___x_1391_;
goto v___jp_1283_;
}
}
}
else
{
lean_dec(v_fst_1383_);
v___y_1284_ = v_c_1265_;
goto v___jp_1283_;
}
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = lean_box(v___x_1277_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___y_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1286_);
v___x_1288_ = v___x_1281_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1275_);
lean_dec_ref_known(v_c_1265_, 2);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
return v___x_1278_;
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v_instr_1275_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1397_ = lean_box(v___x_1277_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_c_1265_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
case 2:
{
lean_object* v_decl_1400_; lean_object* v_k_1401_; lean_object* v___x_1402_; 
v_decl_1400_ = lean_ctor_get(v_c_1265_, 0);
v_k_1401_ = lean_ctor_get(v_c_1265_, 1);
lean_inc_ref(v_k_1401_);
lean_inc_ref(v_info_1264_);
lean_inc(v_x_1263_);
v___x_1402_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1263_, v_info_1264_, v_k_1401_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v_params_1406_; lean_object* v_type_1407_; lean_object* v_value_1408_; lean_object* v___x_1409_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v_fst_1404_ = lean_ctor_get(v_a_1403_, 0);
lean_inc(v_fst_1404_);
v_snd_1405_ = lean_ctor_get(v_a_1403_, 1);
lean_inc(v_snd_1405_);
lean_dec(v_a_1403_);
v_params_1406_ = lean_ctor_get(v_decl_1400_, 2);
v_type_1407_ = lean_ctor_get(v_decl_1400_, 3);
v_value_1408_ = lean_ctor_get(v_decl_1400_, 4);
lean_inc_ref(v_value_1408_);
v___x_1409_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1263_, v_info_1264_, v_value_1408_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1455_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v_fst_1411_ = lean_ctor_get(v_a_1410_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_a_1410_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v_a_1410_, 1);
lean_dec(v_unused_1456_);
v___x_1413_ = v_a_1410_;
v_isShared_1414_ = v_isSharedCheck_1455_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fst_1411_);
lean_dec(v_a_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1455_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
uint8_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = 1;
lean_inc_ref(v_params_1406_);
lean_inc_ref(v_type_1407_);
lean_inc_ref(v_decl_1400_);
v___x_1416_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1415_, v_decl_1400_, v_type_1407_, v_params_1406_, v_fst_1411_, v_a_1268_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1446_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1446_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1446_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___y_1422_; uint8_t v___y_1430_; size_t v___x_1440_; size_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_ptr_addr(v_k_1401_);
v___x_1441_ = lean_ptr_addr(v_fst_1404_);
v___x_1442_ = lean_usize_dec_eq(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
v___y_1430_ = v___x_1442_;
goto v___jp_1429_;
}
else
{
size_t v___x_1443_; size_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_ptr_addr(v_decl_1400_);
v___x_1444_ = lean_ptr_addr(v_a_1417_);
v___x_1445_ = lean_usize_dec_eq(v___x_1443_, v___x_1444_);
v___y_1430_ = v___x_1445_;
goto v___jp_1429_;
}
v___jp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v_snd_1405_);
lean_ctor_set(v___x_1413_, 0, v___y_1422_);
v___x_1424_ = v___x_1413_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___y_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_snd_1405_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1424_);
v___x_1426_ = v___x_1419_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
v___jp_1429_:
{
if (v___y_1430_ == 0)
{
lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; lean_object* v_unused_1439_; 
v_unused_1438_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1439_);
v___x_1432_ = v_c_1265_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_dec(v_c_1265_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v_fst_1404_);
lean_ctor_set(v___x_1432_, 0, v_a_1417_);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1417_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_fst_1404_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v___y_1422_ = v___x_1435_;
goto v___jp_1421_;
}
}
}
else
{
lean_dec(v_a_1417_);
lean_dec(v_fst_1404_);
v___y_1422_ = v_c_1265_;
goto v___jp_1421_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_del_object(v___x_1413_);
lean_dec(v_snd_1405_);
lean_dec(v_fst_1404_);
lean_dec_ref_known(v_c_1265_, 2);
v_a_1447_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1416_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1416_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_dec(v_snd_1405_);
lean_dec(v_fst_1404_);
lean_dec_ref_known(v_c_1265_, 2);
return v___x_1409_;
}
}
else
{
lean_dec_ref_known(v_c_1265_, 2);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
return v___x_1402_;
}
}
case 3:
{
lean_object* v___x_1457_; 
lean_dec_ref(v_info_1264_);
lean_inc_ref(v_c_1265_);
v___x_1457_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1265_, v_x_1263_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_c_1265_);
lean_ctor_set(v___x_1462_, 1, v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref_known(v_c_1265_, 2);
v_a_1467_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1457_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1457_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
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
case 4:
{
lean_object* v_cases_1475_; lean_object* v___x_1476_; 
v_cases_1475_ = lean_ctor_get(v_c_1265_, 0);
lean_inc_ref(v_cases_1475_);
lean_inc(v_x_1263_);
lean_inc_ref(v_c_1265_);
v___x_1476_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1265_, v_x_1263_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1529_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1529_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1529_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_unbox(v_a_1477_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_dec_ref(v_cases_1475_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_c_1265_);
lean_ctor_set(v___x_1482_, 1, v_a_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1482_);
v___x_1484_ = v___x_1479_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
else
{
lean_object* v_typeName_1486_; lean_object* v_resultType_1487_; lean_object* v_discr_1488_; lean_object* v_alts_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1528_; 
lean_del_object(v___x_1479_);
v_typeName_1486_ = lean_ctor_get(v_cases_1475_, 0);
v_resultType_1487_ = lean_ctor_get(v_cases_1475_, 1);
v_discr_1488_ = lean_ctor_get(v_cases_1475_, 2);
v_alts_1489_ = lean_ctor_get(v_cases_1475_, 3);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_cases_1475_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1491_ = v_cases_1475_;
v_isShared_1492_ = v_isSharedCheck_1528_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_alts_1489_);
lean_inc(v_discr_1488_);
lean_inc(v_resultType_1487_);
lean_inc(v_typeName_1486_);
lean_dec(v_cases_1475_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1528_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1489_);
v___x_1494_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1263_, v_info_1264_, v___x_1493_, v_alts_1489_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1519_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1519_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1519_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___y_1500_; size_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_ptr_addr(v_alts_1489_);
lean_dec_ref(v_alts_1489_);
v___x_1506_ = lean_ptr_addr(v_a_1495_);
v___x_1507_ = lean_usize_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1517_; 
v_isSharedCheck_1517_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1518_);
v___x_1509_ = v_c_1265_;
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_c_1265_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 3, v_a_1495_);
v___x_1512_ = v___x_1491_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_typeName_1486_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_resultType_1487_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_discr_1488_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_a_1495_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1512_);
v___x_1514_ = v___x_1509_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
v___y_1500_ = v___x_1514_;
goto v___jp_1499_;
}
}
}
}
else
{
lean_dec(v_a_1495_);
lean_del_object(v___x_1491_);
lean_dec(v_discr_1488_);
lean_dec_ref(v_resultType_1487_);
lean_dec(v_typeName_1486_);
v___y_1500_ = v_c_1265_;
goto v___jp_1499_;
}
v___jp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___y_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1477_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1501_);
v___x_1503_ = v___x_1497_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_del_object(v___x_1491_);
lean_dec_ref(v_alts_1489_);
lean_dec(v_discr_1488_);
lean_dec_ref(v_resultType_1487_);
lean_dec(v_typeName_1486_);
lean_dec(v_a_1477_);
lean_dec_ref_known(v_c_1265_, 1);
v_a_1520_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1494_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1494_);
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
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_cases_1475_);
lean_dec_ref_known(v_c_1265_, 1);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_a_1530_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1476_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1476_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
case 5:
{
lean_object* v___x_1538_; 
lean_dec_ref(v_info_1264_);
lean_inc_ref(v_c_1265_);
v___x_1538_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1265_, v_x_1263_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_c_1265_);
lean_ctor_set(v___x_1543_, 1, v_a_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref_known(v_c_1265_, 1);
v_a_1548_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1538_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1538_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
case 6:
{
lean_object* v___x_1556_; 
lean_dec_ref(v_info_1264_);
lean_inc_ref(v_c_1265_);
v___x_1556_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1265_, v_x_1263_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1565_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_c_1265_);
lean_ctor_set(v___x_1561_, 1, v_a_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1561_);
v___x_1563_ = v___x_1559_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref_known(v_c_1265_, 1);
v_a_1566_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1556_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1556_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_1574_; lean_object* v_i_1575_; lean_object* v_y_1576_; lean_object* v_k_1577_; uint8_t v___x_1578_; lean_object* v_instr_1579_; uint8_t v___x_1580_; uint8_t v___x_1581_; 
v_fvarId_1574_ = lean_ctor_get(v_c_1265_, 0);
v_i_1575_ = lean_ctor_get(v_c_1265_, 1);
v_y_1576_ = lean_ctor_get(v_c_1265_, 2);
v_k_1577_ = lean_ctor_get(v_c_1265_, 3);
v___x_1578_ = 1;
v_instr_1579_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1578_, v_c_1265_);
lean_inc(v_x_1263_);
v___x_1580_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1579_, v_x_1263_);
v___x_1581_ = 1;
if (v___x_1580_ == 0)
{
lean_object* v___x_1582_; 
lean_inc_ref(v_k_1577_);
lean_inc_ref(v_info_1264_);
lean_inc(v_x_1263_);
v___x_1582_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1263_, v_info_1264_, v_k_1577_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1708_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1708_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1708_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___y_1588_; lean_object* v_snd_1594_; uint8_t v___x_1595_; 
v_snd_1594_ = lean_ctor_get(v_a_1583_, 1);
v___x_1595_ = lean_unbox(v_snd_1594_);
if (v___x_1595_ == 0)
{
lean_object* v_fst_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1691_; 
lean_inc(v_snd_1594_);
lean_del_object(v___x_1585_);
v_fst_1596_ = lean_ctor_get(v_a_1583_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v_a_1583_, 1);
lean_dec(v_unused_1692_);
v___x_1598_ = v_a_1583_;
v_isShared_1599_ = v_isSharedCheck_1691_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_fst_1596_);
lean_dec(v_a_1583_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1691_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; 
lean_inc(v_x_1263_);
v___x_1600_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1579_, v_x_1263_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1682_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1682_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1682_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___y_1606_; lean_object* v___y_1614_; uint8_t v___x_1618_; 
v___x_1618_ = lean_unbox(v_a_1601_);
lean_dec(v_a_1601_);
switch(v___x_1618_)
{
case 0:
{
size_t v___x_1619_; size_t v___x_1620_; uint8_t v___x_1621_; 
lean_del_object(v___x_1603_);
lean_del_object(v___x_1598_);
lean_dec(v_snd_1594_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1619_ = lean_ptr_addr(v_k_1577_);
v___x_1620_ = lean_ptr_addr(v_fst_1596_);
v___x_1621_ = lean_usize_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_inc(v_y_1576_);
lean_inc(v_i_1575_);
lean_inc(v_fvarId_1574_);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; lean_object* v_unused_1632_; 
v_unused_1629_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1632_);
v___x_1623_ = v_c_1265_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v_c_1265_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 3, v_fst_1596_);
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_fvarId_1574_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_i_1575_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_y_1576_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_fst_1596_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
v___y_1614_ = v___x_1626_;
goto v___jp_1613_;
}
}
}
else
{
lean_dec(v_fst_1596_);
v___y_1614_ = v_c_1265_;
goto v___jp_1613_;
}
}
case 1:
{
lean_object* v___x_1633_; 
lean_del_object(v___x_1603_);
lean_del_object(v___x_1598_);
lean_dec(v_snd_1594_);
v___x_1633_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1263_, v_info_1264_, v_fst_1596_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_info_1264_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1659_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1659_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1659_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___y_1639_; size_t v___x_1645_; size_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_ptr_addr(v_k_1577_);
v___x_1646_ = lean_ptr_addr(v_a_1634_);
v___x_1647_ = lean_usize_dec_eq(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_inc(v_y_1576_);
lean_inc(v_i_1575_);
lean_inc(v_fvarId_1574_);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1655_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1658_);
v___x_1649_ = v_c_1265_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_c_1265_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 3, v_a_1634_);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_fvarId_1574_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_i_1575_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_y_1576_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_a_1634_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v___y_1639_ = v___x_1652_;
goto v___jp_1638_;
}
}
}
else
{
lean_dec(v_a_1634_);
v___y_1639_ = v_c_1265_;
goto v___jp_1638_;
}
v___jp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = lean_box(v___x_1581_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___y_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1641_);
v___x_1643_ = v___x_1636_;
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
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref_known(v_c_1265_, 4);
v_a_1660_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1633_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1633_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
default: 
{
size_t v___x_1668_; size_t v___x_1669_; uint8_t v___x_1670_; 
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1668_ = lean_ptr_addr(v_k_1577_);
v___x_1669_ = lean_ptr_addr(v_fst_1596_);
v___x_1670_ = lean_usize_dec_eq(v___x_1668_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_inc(v_y_1576_);
lean_inc(v_i_1575_);
lean_inc(v_fvarId_1574_);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; 
v_unused_1678_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1681_);
v___x_1672_ = v_c_1265_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v_c_1265_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 3, v_fst_1596_);
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_fvarId_1574_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_i_1575_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_y_1576_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_fst_1596_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
v___y_1606_ = v___x_1675_;
goto v___jp_1605_;
}
}
}
else
{
lean_dec(v_fst_1596_);
v___y_1606_ = v_c_1265_;
goto v___jp_1605_;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___y_1606_);
v___x_1608_ = v___x_1598_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___y_1606_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_snd_1594_);
v___x_1608_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1608_);
v___x_1610_ = v___x_1603_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
v___jp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_box(v___x_1581_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___y_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1598_);
lean_dec(v_fst_1596_);
lean_dec(v_snd_1594_);
lean_dec_ref_known(v_c_1265_, 4);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_a_1683_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1600_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1600_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v_fst_1693_; size_t v___x_1694_; size_t v___x_1695_; uint8_t v___x_1696_; 
lean_dec_ref(v_instr_1579_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_fst_1693_ = lean_ctor_get(v_a_1583_, 0);
lean_inc(v_fst_1693_);
lean_dec(v_a_1583_);
v___x_1694_ = lean_ptr_addr(v_k_1577_);
v___x_1695_ = lean_ptr_addr(v_fst_1693_);
v___x_1696_ = lean_usize_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_inc(v_y_1576_);
lean_inc(v_i_1575_);
lean_inc(v_fvarId_1574_);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; 
v_unused_1704_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1707_);
v___x_1698_ = v_c_1265_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v_c_1265_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 3, v_fst_1693_);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_fvarId_1574_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_i_1575_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_y_1576_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_fst_1693_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
v___y_1588_ = v___x_1701_;
goto v___jp_1587_;
}
}
}
else
{
lean_dec(v_fst_1693_);
v___y_1588_ = v_c_1265_;
goto v___jp_1587_;
}
}
v___jp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1589_ = lean_box(v___x_1581_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1590_);
v___x_1592_ = v___x_1585_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1579_);
lean_dec_ref_known(v_c_1265_, 4);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
return v___x_1582_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref(v_instr_1579_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1709_ = lean_box(v___x_1581_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_c_1265_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
case 9:
{
lean_object* v_fvarId_1712_; lean_object* v_i_1713_; lean_object* v_offset_1714_; lean_object* v_y_1715_; lean_object* v_ty_1716_; lean_object* v_k_1717_; uint8_t v___x_1718_; lean_object* v_instr_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; 
v_fvarId_1712_ = lean_ctor_get(v_c_1265_, 0);
v_i_1713_ = lean_ctor_get(v_c_1265_, 1);
v_offset_1714_ = lean_ctor_get(v_c_1265_, 2);
v_y_1715_ = lean_ctor_get(v_c_1265_, 3);
v_ty_1716_ = lean_ctor_get(v_c_1265_, 4);
v_k_1717_ = lean_ctor_get(v_c_1265_, 5);
v___x_1718_ = 1;
v_instr_1719_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1718_, v_c_1265_);
lean_inc(v_x_1263_);
v___x_1720_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1719_, v_x_1263_);
v___x_1721_ = 1;
if (v___x_1720_ == 0)
{
lean_object* v___x_1722_; 
lean_inc_ref(v_k_1717_);
lean_inc_ref(v_info_1264_);
lean_inc(v_x_1263_);
v___x_1722_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1263_, v_info_1264_, v_k_1717_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1856_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1856_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1856_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___y_1728_; lean_object* v_snd_1734_; uint8_t v___x_1735_; 
v_snd_1734_ = lean_ctor_get(v_a_1723_, 1);
v___x_1735_ = lean_unbox(v_snd_1734_);
if (v___x_1735_ == 0)
{
lean_object* v_fst_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1837_; 
lean_inc(v_snd_1734_);
lean_del_object(v___x_1725_);
v_fst_1736_ = lean_ctor_get(v_a_1723_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_a_1723_, 1);
lean_dec(v_unused_1838_);
v___x_1738_ = v_a_1723_;
v_isShared_1739_ = v_isSharedCheck_1837_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_fst_1736_);
lean_dec(v_a_1723_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1837_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; 
lean_inc(v_x_1263_);
v___x_1740_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1719_, v_x_1263_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1828_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1828_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1828_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___y_1746_; lean_object* v___y_1754_; uint8_t v___x_1758_; 
v___x_1758_ = lean_unbox(v_a_1741_);
lean_dec(v_a_1741_);
switch(v___x_1758_)
{
case 0:
{
size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
lean_del_object(v___x_1743_);
lean_del_object(v___x_1738_);
lean_dec(v_snd_1734_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1759_ = lean_ptr_addr(v_k_1717_);
v___x_1760_ = lean_ptr_addr(v_fst_1736_);
v___x_1761_ = lean_usize_dec_eq(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_inc_ref(v_ty_1716_);
lean_inc(v_y_1715_);
lean_inc(v_offset_1714_);
lean_inc(v_i_1713_);
lean_inc(v_fvarId_1712_);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; 
v_unused_1769_ = lean_ctor_get(v_c_1265_, 5);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_c_1265_, 4);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1774_);
v___x_1763_ = v_c_1265_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_dec(v_c_1265_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 5, v_fst_1736_);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_fvarId_1712_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_i_1713_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_offset_1714_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_y_1715_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_ty_1716_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v_fst_1736_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v___y_1754_ = v___x_1766_;
goto v___jp_1753_;
}
}
}
else
{
lean_dec(v_fst_1736_);
v___y_1754_ = v_c_1265_;
goto v___jp_1753_;
}
}
case 1:
{
lean_object* v___x_1775_; 
lean_del_object(v___x_1743_);
lean_del_object(v___x_1738_);
lean_dec(v_snd_1734_);
v___x_1775_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1263_, v_info_1264_, v_fst_1736_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_info_1264_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1803_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1803_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1803_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___y_1781_; size_t v___x_1787_; size_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1787_ = lean_ptr_addr(v_k_1717_);
v___x_1788_ = lean_ptr_addr(v_a_1776_);
v___x_1789_ = lean_usize_dec_eq(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_inc_ref(v_ty_1716_);
lean_inc(v_y_1715_);
lean_inc(v_offset_1714_);
lean_inc(v_i_1713_);
lean_inc(v_fvarId_1712_);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; lean_object* v_unused_1802_; 
v_unused_1797_ = lean_ctor_get(v_c_1265_, 5);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_c_1265_, 4);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1802_);
v___x_1791_ = v_c_1265_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_dec(v_c_1265_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 5, v_a_1776_);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_fvarId_1712_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_i_1713_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_offset_1714_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_y_1715_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_ty_1716_);
lean_ctor_set(v_reuseFailAlloc_1795_, 5, v_a_1776_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v___y_1781_ = v___x_1794_;
goto v___jp_1780_;
}
}
}
else
{
lean_dec(v_a_1776_);
v___y_1781_ = v_c_1265_;
goto v___jp_1780_;
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_box(v___x_1721_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___y_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1783_);
v___x_1785_ = v___x_1778_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec_ref_known(v_c_1265_, 6);
v_a_1804_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1775_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1775_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
default: 
{
size_t v___x_1812_; size_t v___x_1813_; uint8_t v___x_1814_; 
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1812_ = lean_ptr_addr(v_k_1717_);
v___x_1813_ = lean_ptr_addr(v_fst_1736_);
v___x_1814_ = lean_usize_dec_eq(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_inc_ref(v_ty_1716_);
lean_inc(v_y_1715_);
lean_inc(v_offset_1714_);
lean_inc(v_i_1713_);
lean_inc(v_fvarId_1712_);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; lean_object* v_unused_1823_; lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; 
v_unused_1822_ = lean_ctor_get(v_c_1265_, 5);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v_c_1265_, 4);
lean_dec(v_unused_1823_);
v_unused_1824_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1827_);
v___x_1816_ = v_c_1265_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v_c_1265_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 5, v_fst_1736_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_fvarId_1712_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_i_1713_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_offset_1714_);
lean_ctor_set(v_reuseFailAlloc_1820_, 3, v_y_1715_);
lean_ctor_set(v_reuseFailAlloc_1820_, 4, v_ty_1716_);
lean_ctor_set(v_reuseFailAlloc_1820_, 5, v_fst_1736_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
v___y_1746_ = v___x_1819_;
goto v___jp_1745_;
}
}
}
else
{
lean_dec(v_fst_1736_);
v___y_1746_ = v_c_1265_;
goto v___jp_1745_;
}
}
}
v___jp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___y_1746_);
v___x_1748_ = v___x_1738_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___y_1746_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_snd_1734_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1748_);
v___x_1750_ = v___x_1743_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
v___jp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_box(v___x_1721_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1738_);
lean_dec(v_fst_1736_);
lean_dec(v_snd_1734_);
lean_dec_ref_known(v_c_1265_, 6);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_a_1829_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1740_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1740_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
else
{
lean_object* v_fst_1839_; size_t v___x_1840_; size_t v___x_1841_; uint8_t v___x_1842_; 
lean_dec_ref(v_instr_1719_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v_fst_1839_ = lean_ctor_get(v_a_1723_, 0);
lean_inc(v_fst_1839_);
lean_dec(v_a_1723_);
v___x_1840_ = lean_ptr_addr(v_k_1717_);
v___x_1841_ = lean_ptr_addr(v_fst_1839_);
v___x_1842_ = lean_usize_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_inc_ref(v_ty_1716_);
lean_inc(v_y_1715_);
lean_inc(v_offset_1714_);
lean_inc(v_i_1713_);
lean_inc(v_fvarId_1712_);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_c_1265_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; 
v_unused_1850_ = lean_ctor_get(v_c_1265_, 5);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_c_1265_, 4);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_c_1265_, 3);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_c_1265_, 2);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_c_1265_, 1);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_c_1265_, 0);
lean_dec(v_unused_1855_);
v___x_1844_ = v_c_1265_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v_c_1265_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 5, v_fst_1839_);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_fvarId_1712_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_i_1713_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_offset_1714_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_y_1715_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_ty_1716_);
lean_ctor_set(v_reuseFailAlloc_1848_, 5, v_fst_1839_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v___y_1728_ = v___x_1847_;
goto v___jp_1727_;
}
}
}
else
{
lean_dec(v_fst_1839_);
v___y_1728_ = v_c_1265_;
goto v___jp_1727_;
}
}
v___jp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1729_ = lean_box(v___x_1721_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___y_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1730_);
v___x_1732_ = v___x_1725_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1719_);
lean_dec_ref_known(v_c_1265_, 6);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
return v___x_1722_;
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_instr_1719_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1857_ = lean_box(v___x_1721_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_c_1265_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
default: 
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref(v_c_1265_);
lean_dec_ref(v_info_1264_);
lean_dec(v_x_1263_);
v___x_1860_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
v___x_1861_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_1860_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object* v_x_1862_, lean_object* v_info_1863_, lean_object* v_c_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___x_1871_; 
lean_inc_ref(v_info_1863_);
lean_inc(v_x_1862_);
v___x_1871_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1862_, v_info_1863_, v_c_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1884_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1884_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1884_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_snd_1876_; uint8_t v___x_1877_; 
v_snd_1876_ = lean_ctor_get(v_a_1872_, 1);
v___x_1877_ = lean_unbox(v_snd_1876_);
if (v___x_1877_ == 0)
{
lean_object* v_fst_1878_; lean_object* v___x_1879_; 
lean_del_object(v___x_1874_);
v_fst_1878_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_fst_1878_);
lean_dec(v_a_1872_);
v___x_1879_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1862_, v_info_1863_, v_fst_1878_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec_ref(v_info_1863_);
return v___x_1879_;
}
else
{
lean_object* v_fst_1880_; lean_object* v___x_1882_; 
lean_dec_ref(v_info_1863_);
lean_dec(v_x_1862_);
v_fst_1880_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_fst_1880_);
lean_dec(v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v_fst_1880_);
v___x_1882_ = v___x_1874_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_fst_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v_info_1863_);
lean_dec(v_x_1862_);
v_a_1885_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1871_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1871_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object* v_x_1893_, lean_object* v_info_1894_, lean_object* v_i_1895_, lean_object* v_as_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1893_, v_info_1894_, v_i_1895_, v_as_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object* v_x_1904_, lean_object* v_info_1905_, lean_object* v_c_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1904_, v_info_1905_, v_c_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_a_1907_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t v_pu_1914_, lean_object* v_alt_1915_, lean_object* v_f_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1915_, v_f_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object* v_pu_1924_, lean_object* v_alt_1925_, lean_object* v_f_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v_pu_boxed_1933_; lean_object* v_res_1934_; 
v_pu_boxed_1933_ = lean_unbox(v_pu_1924_);
v_res_1934_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_boxed_1933_, v_alt_1925_, v_f_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object* v_msg_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_toApplicative_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1978_; 
v___x_1942_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_1943_ = l_StateRefT_x27_instMonad___redArg(v___x_1942_);
v_toApplicative_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1943_, 1);
lean_dec(v_unused_1979_);
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1978_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_toApplicative_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1978_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_toFunctor_1948_; lean_object* v_toSeq_1949_; lean_object* v_toSeqLeft_1950_; lean_object* v_toSeqRight_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1976_; 
v_toFunctor_1948_ = lean_ctor_get(v_toApplicative_1944_, 0);
v_toSeq_1949_ = lean_ctor_get(v_toApplicative_1944_, 2);
v_toSeqLeft_1950_ = lean_ctor_get(v_toApplicative_1944_, 3);
v_toSeqRight_1951_ = lean_ctor_get(v_toApplicative_1944_, 4);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_toApplicative_1944_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_toApplicative_1944_, 1);
lean_dec(v_unused_1977_);
v___x_1953_ = v_toApplicative_1944_;
v_isShared_1954_ = v_isSharedCheck_1976_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_toSeqRight_1951_);
lean_inc(v_toSeqLeft_1950_);
lean_inc(v_toSeq_1949_);
lean_inc(v_toFunctor_1948_);
lean_dec(v_toApplicative_1944_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1976_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___f_1961_; lean_object* v___f_1962_; lean_object* v___x_1964_; 
v___f_1955_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_1956_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1948_);
v___f_1957_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1957_, 0, v_toFunctor_1948_);
v___f_1958_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1958_, 0, v_toFunctor_1948_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___f_1957_);
lean_ctor_set(v___x_1959_, 1, v___f_1958_);
v___f_1960_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1960_, 0, v_toSeqRight_1951_);
v___f_1961_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1961_, 0, v_toSeqLeft_1950_);
v___f_1962_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1962_, 0, v_toSeq_1949_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 4, v___f_1960_);
lean_ctor_set(v___x_1953_, 3, v___f_1961_);
lean_ctor_set(v___x_1953_, 2, v___f_1962_);
lean_ctor_set(v___x_1953_, 1, v___f_1955_);
lean_ctor_set(v___x_1953_, 0, v___x_1959_);
v___x_1964_ = v___x_1953_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___f_1955_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v___f_1962_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v___f_1961_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v___f_1960_);
v___x_1964_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v___f_1956_);
lean_ctor_set(v___x_1946_, 0, v___x_1964_);
v___x_1966_ = v___x_1946_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___f_1956_);
v___x_1966_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___f_1970_; lean_object* v___f_1971_; lean_object* v___x_5584__overap_1972_; lean_object* v___x_1973_; 
v___x_1967_ = l_StateRefT_x27_instMonad___redArg(v___x_1966_);
v___x_1968_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_1969_ = l_instInhabitedOfMonad___redArg(v___x_1967_, v___x_1968_);
v___f_1970_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1970_, 0, v___x_1969_);
v___f_1971_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1971_, 0, v___f_1970_);
v___x_5584__overap_1972_ = lean_panic_fn_borrowed(v___f_1971_, v_msg_1935_);
lean_dec_ref(v___f_1971_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc_ref(v___y_1936_);
v___x_1973_ = lean_apply_6(v___x_5584__overap_1972_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, lean_box(0));
return v___x_1973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg(lean_object* v_m_1988_, lean_object* v_query_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v_zero_1993_; uint8_t v_isZero_1994_; 
v_zero_1993_ = lean_unsigned_to_nat(0u);
v_isZero_1994_ = lean_nat_dec_eq(v_x_1991_, v_zero_1993_);
if (v_isZero_1994_ == 1)
{
lean_dec(v_x_1992_);
lean_dec(v_x_1991_);
if (lean_obj_tag(v_x_1990_) == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_box(2);
return v___x_1995_;
}
else
{
lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_val_1996_ = lean_ctor_get(v_x_1990_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1990_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v_x_1990_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v_x_1990_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_val_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_keyArray_2004_; lean_object* v_valueArray_2005_; lean_object* v___x_2006_; uint8_t v_isSome_2007_; 
v_keyArray_2004_ = lean_ctor_get(v_m_1988_, 1);
v_valueArray_2005_ = lean_ctor_get(v_m_1988_, 2);
v___x_2006_ = lean_array_fget_borrowed(v_keyArray_2004_, v_x_1992_);
v_isSome_2007_ = lean_noption_is_some(v___x_2006_);
if (v_isSome_2007_ == 0)
{
lean_dec(v_x_1991_);
if (lean_obj_tag(v_x_1990_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_x_1992_);
return v___x_2008_;
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_x_1992_);
v_val_2009_ = lean_ctor_get(v_x_1990_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_x_1990_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v_x_1990_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v_x_1990_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_val_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
lean_object* v_one_2017_; lean_object* v_n_2018_; lean_object* v___y_2020_; 
v_one_2017_ = lean_unsigned_to_nat(1u);
v_n_2018_ = lean_nat_sub(v_x_1991_, v_one_2017_);
lean_dec(v_x_1991_);
if (v_isSome_2007_ == 0)
{
goto v___jp_2026_;
}
else
{
lean_object* v___x_2028_; uint8_t v_isSome_2029_; 
v___x_2028_ = lean_array_fget_borrowed(v_valueArray_2005_, v_x_1992_);
v_isSome_2029_ = lean_noption_is_some(v___x_2028_);
if (v_isSome_2029_ == 0)
{
goto v___jp_2026_;
}
else
{
lean_object* v_val_2030_; uint8_t v___x_2031_; 
lean_inc(v___x_2006_);
v_val_2030_ = lean_noption_get(v___x_2006_);
v___x_2031_ = l_Lean_instBEqFVarId_beq(v_val_2030_, v_query_1989_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
lean_dec(v_val_2030_);
v___x_2032_ = lean_array_get_size(v_keyArray_2004_);
v___x_2033_ = lean_nat_add(v_x_1992_, v_one_2017_);
lean_dec(v_x_1992_);
v___x_2034_ = lean_nat_dec_lt(v___x_2033_, v___x_2032_);
if (v___x_2034_ == 0)
{
lean_dec(v___x_2033_);
v_x_1991_ = v_n_2018_;
v_x_1992_ = v_zero_1993_;
goto _start;
}
else
{
v_x_1991_ = v_n_2018_;
v_x_1992_ = v___x_2033_;
goto _start;
}
}
else
{
lean_object* v_val_2037_; lean_object* v___x_2038_; 
lean_dec(v_n_2018_);
lean_dec(v_x_1990_);
lean_inc(v___x_2028_);
v_val_2037_ = lean_noption_get(v___x_2028_);
v___x_2038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2038_, 0, v_x_1992_);
lean_ctor_set(v___x_2038_, 1, v_val_2030_);
lean_ctor_set(v___x_2038_, 2, v_val_2037_);
return v___x_2038_;
}
}
}
v___jp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2021_ = lean_array_get_size(v_keyArray_2004_);
v___x_2022_ = lean_nat_add(v_x_1992_, v_one_2017_);
lean_dec(v_x_1992_);
v___x_2023_ = lean_nat_dec_lt(v___x_2022_, v___x_2021_);
if (v___x_2023_ == 0)
{
lean_dec(v___x_2022_);
v_x_1990_ = v___y_2020_;
v_x_1991_ = v_n_2018_;
v_x_1992_ = v_zero_1993_;
goto _start;
}
else
{
v_x_1990_ = v___y_2020_;
v_x_1991_ = v_n_2018_;
v_x_1992_ = v___x_2022_;
goto _start;
}
}
v___jp_2026_:
{
if (lean_obj_tag(v_x_1990_) == 0)
{
lean_object* v___x_2027_; 
lean_inc(v_x_1992_);
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_x_1992_);
v___y_2020_ = v___x_2027_;
goto v___jp_2019_;
}
else
{
v___y_2020_ = v_x_1990_;
goto v___jp_2019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_m_2039_, lean_object* v_query_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_m_2039_, v_query_2040_, v_x_2041_, v_x_2042_, v_x_2043_);
lean_dec(v_query_2040_);
lean_dec_ref(v_m_2039_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_2045_, lean_object* v_query_2046_){
_start:
{
lean_object* v_keyArray_2047_; lean_object* v___x_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v___x_2051_; uint64_t v_fold_2052_; uint64_t v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; size_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_keyArray_2047_ = lean_ctor_get(v_m_2045_, 1);
v___x_2048_ = lean_array_get_size(v_keyArray_2047_);
v___x_2049_ = l_Lean_instHashableFVarId_hash(v_query_2046_);
v___x_2050_ = 32ULL;
v___x_2051_ = lean_uint64_shift_right(v___x_2049_, v___x_2050_);
v_fold_2052_ = lean_uint64_xor(v___x_2049_, v___x_2051_);
v___x_2053_ = 16ULL;
v___x_2054_ = lean_uint64_shift_right(v_fold_2052_, v___x_2053_);
v___x_2055_ = lean_uint64_xor(v_fold_2052_, v___x_2054_);
v___x_2056_ = lean_uint64_to_usize(v___x_2055_);
v___x_2057_ = lean_usize_of_nat(v___x_2048_);
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_sub(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_usize_land(v___x_2056_, v___x_2059_);
v___x_2061_ = lean_usize_to_nat(v___x_2060_);
v___x_2062_ = lean_box(0);
v___x_2063_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_m_2045_, v_query_2046_, v___x_2062_, v___x_2048_, v___x_2061_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_2064_, lean_object* v_query_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg(v_m_2064_, v_query_2065_);
lean_dec(v_query_2065_);
lean_dec_ref(v_m_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(lean_object* v_m_2067_, lean_object* v_query_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg(v_m_2067_, v_query_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_index_2070_; lean_object* v_key_2071_; lean_object* v_value_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_index_2070_ = lean_ctor_get(v___x_2069_, 0);
v_key_2071_ = lean_ctor_get(v___x_2069_, 1);
v_value_2072_ = lean_ctor_get(v___x_2069_, 2);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2069_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_value_2072_);
lean_inc(v_key_2071_);
lean_inc(v_index_2070_);
lean_dec(v___x_2069_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_index_2070_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_key_2071_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_value_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v___x_2080_; 
lean_dec(v___x_2069_);
v___x_2080_ = lean_box(1);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_m_2081_, lean_object* v_query_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(v_m_2081_, v_query_2082_);
lean_dec(v_query_2082_);
lean_dec_ref(v_m_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object* v_m_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(v_m_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_value_2087_; lean_object* v___x_2088_; 
v_value_2087_ = lean_ctor_get(v___x_2086_, 2);
lean_inc(v_value_2087_);
lean_dec_ref_known(v___x_2086_, 3);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_value_2087_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_box(0);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object* v_m_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_m_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_m_2090_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object* v_m_2093_, lean_object* v_a_2094_, lean_object* v_fallback_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_m_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_inc(v_fallback_2095_);
return v_fallback_2095_;
}
else
{
lean_object* v_val_2097_; 
v_val_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_val_2097_);
lean_dec_ref_known(v___x_2096_, 1);
return v_val_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object* v_m_2098_, lean_object* v_a_2099_, lean_object* v_fallback_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2098_, v_a_2099_, v_fallback_2100_);
lean_dec(v_fallback_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_m_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_spec__11___redArg(lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v_ks_2106_; lean_object* v_vs_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2131_; 
v_ks_2106_ = lean_ctor_get(v_x_2102_, 0);
v_vs_2107_ = lean_ctor_get(v_x_2102_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_x_2102_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2109_ = v_x_2102_;
v_isShared_2110_ = v_isSharedCheck_2131_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_vs_2107_);
lean_inc(v_ks_2106_);
lean_dec(v_x_2102_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2131_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_array_get_size(v_ks_2106_);
v___x_2112_ = lean_nat_dec_lt(v_x_2103_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
lean_dec(v_x_2103_);
v___x_2113_ = lean_array_push(v_ks_2106_, v_x_2104_);
v___x_2114_ = lean_array_push(v_vs_2107_, v_x_2105_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2114_);
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2116_ = v___x_2109_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
else
{
lean_object* v_k_x27_2118_; uint8_t v___x_2119_; 
v_k_x27_2118_ = lean_array_fget_borrowed(v_ks_2106_, v_x_2103_);
v___x_2119_ = l_Lean_instBEqFVarId_beq(v_x_2104_, v_k_x27_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2121_; 
if (v_isShared_2110_ == 0)
{
v___x_2121_ = v___x_2109_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_ks_2106_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_vs_2107_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_add(v_x_2103_, v___x_2122_);
lean_dec(v_x_2103_);
v_x_2102_ = v___x_2121_;
v_x_2103_ = v___x_2123_;
goto _start;
}
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2126_ = lean_array_fset(v_ks_2106_, v_x_2103_, v_x_2104_);
v___x_2127_ = lean_array_fset(v_vs_2107_, v_x_2103_, v_x_2105_);
lean_dec(v_x_2103_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2127_);
lean_ctor_set(v___x_2109_, 0, v___x_2126_);
v___x_2129_ = v___x_2109_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(lean_object* v_n_2132_, lean_object* v_k_2133_, lean_object* v_v_2134_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_spec__11___redArg(v_n_2132_, v___x_2135_, v_k_2133_, v_v_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object* v_x_2138_, size_t v_x_2139_, size_t v_x_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
lean_object* v_es_2143_; size_t v___x_2144_; size_t v___x_2145_; lean_object* v_j_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_es_2143_ = lean_ctor_get(v_x_2138_, 0);
v___x_2144_ = ((size_t)31ULL);
v___x_2145_ = lean_usize_land(v_x_2139_, v___x_2144_);
v_j_2146_ = lean_usize_to_nat(v___x_2145_);
v___x_2147_ = lean_array_get_size(v_es_2143_);
v___x_2148_ = lean_nat_dec_lt(v_j_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_dec(v_j_2146_);
lean_dec(v_x_2142_);
lean_dec(v_x_2141_);
return v_x_2138_;
}
else
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2187_; 
lean_inc_ref(v_es_2143_);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_x_2138_, 0);
lean_dec(v_unused_2188_);
v___x_2150_ = v_x_2138_;
v_isShared_2151_ = v_isSharedCheck_2187_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v_x_2138_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2187_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_v_2152_; lean_object* v___x_2153_; lean_object* v_xs_x27_2154_; lean_object* v___y_2156_; 
v_v_2152_ = lean_array_fget(v_es_2143_, v_j_2146_);
v___x_2153_ = lean_box(0);
v_xs_x27_2154_ = lean_array_fset(v_es_2143_, v_j_2146_, v___x_2153_);
switch(lean_obj_tag(v_v_2152_))
{
case 0:
{
lean_object* v_key_2161_; lean_object* v_val_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2172_; 
v_key_2161_ = lean_ctor_get(v_v_2152_, 0);
v_val_2162_ = lean_ctor_get(v_v_2152_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_v_2152_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2164_ = v_v_2152_;
v_isShared_2165_ = v_isSharedCheck_2172_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_val_2162_);
lean_inc(v_key_2161_);
lean_dec(v_v_2152_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2172_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint8_t v___x_2166_; 
v___x_2166_ = l_Lean_instBEqFVarId_beq(v_x_2141_, v_key_2161_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_del_object(v___x_2164_);
v___x_2167_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2161_, v_val_2162_, v_x_2141_, v_x_2142_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
v___y_2156_ = v___x_2168_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2170_; 
lean_dec(v_val_2162_);
lean_dec(v_key_2161_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v_x_2142_);
lean_ctor_set(v___x_2164_, 0, v_x_2141_);
v___x_2170_ = v___x_2164_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_x_2141_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_x_2142_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
v___y_2156_ = v___x_2170_;
goto v___jp_2155_;
}
}
}
}
case 1:
{
lean_object* v_node_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
v_node_2173_ = lean_ctor_get(v_v_2152_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_v_2152_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2175_ = v_v_2152_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_node_2173_);
lean_dec(v_v_2152_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2177_ = ((size_t)5ULL);
v___x_2178_ = lean_usize_shift_right(v_x_2139_, v___x_2177_);
v___x_2179_ = ((size_t)1ULL);
v___x_2180_ = lean_usize_add(v_x_2140_, v___x_2179_);
v___x_2181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_2173_, v___x_2178_, v___x_2180_, v_x_2141_, v_x_2142_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2181_);
v___x_2183_ = v___x_2175_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
v___y_2156_ = v___x_2183_;
goto v___jp_2155_;
}
}
}
default: 
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_x_2141_);
lean_ctor_set(v___x_2186_, 1, v_x_2142_);
v___y_2156_ = v___x_2186_;
goto v___jp_2155_;
}
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_array_fset(v_xs_x27_2154_, v_j_2146_, v___y_2156_);
lean_dec(v_j_2146_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2157_);
v___x_2159_ = v___x_2150_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
else
{
lean_object* v_ks_2189_; lean_object* v_vs_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2210_; 
v_ks_2189_ = lean_ctor_get(v_x_2138_, 0);
v_vs_2190_ = lean_ctor_get(v_x_2138_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2192_ = v_x_2138_;
v_isShared_2193_ = v_isSharedCheck_2210_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_vs_2190_);
lean_inc(v_ks_2189_);
lean_dec(v_x_2138_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2210_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_ks_2189_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_vs_2190_);
v___x_2195_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v_newNode_2196_; uint8_t v___y_2198_; size_t v___x_2204_; uint8_t v___x_2205_; 
v_newNode_2196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v___x_2195_, v_x_2141_, v_x_2142_);
v___x_2204_ = ((size_t)7ULL);
v___x_2205_ = lean_usize_dec_le(v___x_2204_, v_x_2140_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2196_);
v___x_2207_ = lean_unsigned_to_nat(4u);
v___x_2208_ = lean_nat_dec_lt(v___x_2206_, v___x_2207_);
lean_dec(v___x_2206_);
v___y_2198_ = v___x_2208_;
goto v___jp_2197_;
}
else
{
v___y_2198_ = v___x_2205_;
goto v___jp_2197_;
}
v___jp_2197_:
{
if (v___y_2198_ == 0)
{
lean_object* v_ks_2199_; lean_object* v_vs_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_ks_2199_ = lean_ctor_get(v_newNode_2196_, 0);
lean_inc_ref(v_ks_2199_);
v_vs_2200_ = lean_ctor_get(v_newNode_2196_, 1);
lean_inc_ref(v_vs_2200_);
lean_dec_ref(v_newNode_2196_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg(v_x_2140_, v_ks_2199_, v_vs_2200_, v___x_2201_, v___x_2202_);
lean_dec_ref(v_vs_2200_);
lean_dec_ref(v_ks_2199_);
return v___x_2203_;
}
else
{
return v_newNode_2196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg(size_t v_depth_2211_, lean_object* v_keys_2212_, lean_object* v_vals_2213_, lean_object* v_i_2214_, lean_object* v_entries_2215_){
_start:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_array_get_size(v_keys_2212_);
v___x_2217_ = lean_nat_dec_lt(v_i_2214_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_dec(v_i_2214_);
return v_entries_2215_;
}
else
{
lean_object* v_k_2218_; lean_object* v_v_2219_; uint64_t v___x_2220_; size_t v_h_2221_; size_t v___x_2222_; lean_object* v___x_2223_; size_t v___x_2224_; size_t v___x_2225_; size_t v___x_2226_; size_t v_h_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_k_2218_ = lean_array_fget_borrowed(v_keys_2212_, v_i_2214_);
v_v_2219_ = lean_array_fget_borrowed(v_vals_2213_, v_i_2214_);
v___x_2220_ = l_Lean_instHashableFVarId_hash(v_k_2218_);
v_h_2221_ = lean_uint64_to_usize(v___x_2220_);
v___x_2222_ = ((size_t)5ULL);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = ((size_t)1ULL);
v___x_2225_ = lean_usize_sub(v_depth_2211_, v___x_2224_);
v___x_2226_ = lean_usize_mul(v___x_2222_, v___x_2225_);
v_h_2227_ = lean_usize_shift_right(v_h_2221_, v___x_2226_);
v___x_2228_ = lean_nat_add(v_i_2214_, v___x_2223_);
lean_dec(v_i_2214_);
lean_inc(v_v_2219_);
lean_inc(v_k_2218_);
v___x_2229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2215_, v_h_2227_, v_depth_2211_, v_k_2218_, v_v_2219_);
v_i_2214_ = v___x_2228_;
v_entries_2215_ = v___x_2229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_depth_2231_, lean_object* v_keys_2232_, lean_object* v_vals_2233_, lean_object* v_i_2234_, lean_object* v_entries_2235_){
_start:
{
size_t v_depth_boxed_2236_; lean_object* v_res_2237_; 
v_depth_boxed_2236_ = lean_unbox_usize(v_depth_2231_);
lean_dec(v_depth_2231_);
v_res_2237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg(v_depth_boxed_2236_, v_keys_2232_, v_vals_2233_, v_i_2234_, v_entries_2235_);
lean_dec_ref(v_vals_2233_);
lean_dec_ref(v_keys_2232_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_){
_start:
{
size_t v_x_6531__boxed_2243_; size_t v_x_6532__boxed_2244_; lean_object* v_res_2245_; 
v_x_6531__boxed_2243_ = lean_unbox_usize(v_x_2239_);
lean_dec(v_x_2239_);
v_x_6532__boxed_2244_ = lean_unbox_usize(v_x_2240_);
lean_dec(v_x_2240_);
v_res_2245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2238_, v_x_6531__boxed_2243_, v_x_6532__boxed_2244_, v_x_2241_, v_x_2242_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
uint64_t v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; lean_object* v___x_2252_; 
v___x_2249_ = l_Lean_instHashableFVarId_hash(v_x_2247_);
v___x_2250_ = lean_uint64_to_usize(v___x_2249_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2246_, v___x_2250_, v___x_2251_, v_x_2247_, v_x_2248_);
return v___x_2252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2253_, lean_object* v_i_2254_, lean_object* v_k_2255_){
_start:
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_array_get_size(v_keys_2253_);
v___x_2257_ = lean_nat_dec_lt(v_i_2254_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_dec(v_i_2254_);
return v___x_2257_;
}
else
{
lean_object* v_k_x27_2258_; uint8_t v___x_2259_; 
v_k_x27_2258_ = lean_array_fget_borrowed(v_keys_2253_, v_i_2254_);
v___x_2259_ = l_Lean_instBEqFVarId_beq(v_k_2255_, v_k_x27_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_add(v_i_2254_, v___x_2260_);
lean_dec(v_i_2254_);
v_i_2254_ = v___x_2261_;
goto _start;
}
else
{
lean_dec(v_i_2254_);
return v___x_2259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2263_, lean_object* v_i_2264_, lean_object* v_k_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2263_, v_i_2264_, v_k_2265_);
lean_dec(v_k_2265_);
lean_dec_ref(v_keys_2263_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2268_, size_t v_x_2269_, lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2268_) == 0)
{
lean_object* v_es_2271_; lean_object* v___x_2272_; size_t v___x_2273_; size_t v___x_2274_; lean_object* v_j_2275_; lean_object* v___x_2276_; 
v_es_2271_ = lean_ctor_get(v_x_2268_, 0);
v___x_2272_ = lean_box(2);
v___x_2273_ = ((size_t)31ULL);
v___x_2274_ = lean_usize_land(v_x_2269_, v___x_2273_);
v_j_2275_ = lean_usize_to_nat(v___x_2274_);
v___x_2276_ = lean_array_get_borrowed(v___x_2272_, v_es_2271_, v_j_2275_);
lean_dec(v_j_2275_);
switch(lean_obj_tag(v___x_2276_))
{
case 0:
{
lean_object* v_key_2277_; uint8_t v___x_2278_; 
v_key_2277_ = lean_ctor_get(v___x_2276_, 0);
v___x_2278_ = l_Lean_instBEqFVarId_beq(v_x_2270_, v_key_2277_);
return v___x_2278_;
}
case 1:
{
lean_object* v_node_2279_; size_t v___x_2280_; size_t v___x_2281_; 
v_node_2279_ = lean_ctor_get(v___x_2276_, 0);
v___x_2280_ = ((size_t)5ULL);
v___x_2281_ = lean_usize_shift_right(v_x_2269_, v___x_2280_);
v_x_2268_ = v_node_2279_;
v_x_2269_ = v___x_2281_;
goto _start;
}
default: 
{
uint8_t v___x_2283_; 
v___x_2283_ = 0;
return v___x_2283_;
}
}
}
else
{
lean_object* v_ks_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_ks_2284_ = lean_ctor_get(v_x_2268_, 0);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2284_, v___x_2285_, v_x_2270_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_){
_start:
{
size_t v_x_6713__boxed_2290_; uint8_t v_res_2291_; lean_object* v_r_2292_; 
v_x_6713__boxed_2290_ = lean_unbox_usize(v_x_2288_);
lean_dec(v_x_2288_);
v_res_2291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2287_, v_x_6713__boxed_2290_, v_x_2289_);
lean_dec(v_x_2289_);
lean_dec_ref(v_x_2287_);
v_r_2292_ = lean_box(v_res_2291_);
return v_r_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2293_, lean_object* v_x_2294_){
_start:
{
uint64_t v___x_2295_; size_t v___x_2296_; uint8_t v___x_2297_; 
v___x_2295_ = l_Lean_instHashableFVarId_hash(v_x_2294_);
v___x_2296_ = lean_uint64_to_usize(v___x_2295_);
v___x_2297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2293_, v___x_2296_, v_x_2294_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2298_, v_x_2299_);
lean_dec(v_x_2299_);
lean_dec_ref(v_x_2298_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2303_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2304_ = lean_unsigned_to_nat(59u);
v___x_2305_ = lean_unsigned_to_nat(281u);
v___x_2306_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2308_ = l_mkPanicMessageWithDecl(v___x_2307_, v___x_2306_, v___x_2305_, v___x_2304_, v___x_2303_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
switch(lean_obj_tag(v_c_2309_))
{
case 0:
{
lean_object* v_decl_2316_; lean_object* v_k_2317_; lean_object* v___x_2318_; 
v_decl_2316_ = lean_ctor_get(v_c_2309_, 0);
v_k_2317_ = lean_ctor_get(v_c_2309_, 1);
lean_inc_ref(v_k_2317_);
v___x_2318_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2317_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2341_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2341_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2341_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
size_t v___x_2323_; size_t v___x_2324_; uint8_t v___x_2325_; 
v___x_2323_ = lean_ptr_addr(v_k_2317_);
v___x_2324_ = lean_ptr_addr(v_a_2319_);
v___x_2325_ = lean_usize_dec_eq(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2335_; 
lean_inc_ref(v_decl_2316_);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_c_2309_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; lean_object* v_unused_2337_; 
v_unused_2336_ = lean_ctor_get(v_c_2309_, 1);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_c_2309_, 0);
lean_dec(v_unused_2337_);
v___x_2327_ = v_c_2309_;
v_isShared_2328_ = v_isSharedCheck_2335_;
goto v_resetjp_2326_;
}
else
{
lean_dec(v_c_2309_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2335_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v_a_2319_);
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_decl_2316_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_a_2319_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2330_);
v___x_2332_ = v___x_2321_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_object* v___x_2339_; 
lean_dec(v_a_2319_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v_c_2309_);
v___x_2339_ = v___x_2321_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_c_2309_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2309_, 2);
return v___x_2318_;
}
}
case 2:
{
lean_object* v_decl_2342_; lean_object* v_k_2343_; lean_object* v_params_2344_; lean_object* v_type_2345_; lean_object* v_value_2346_; lean_object* v___x_2347_; 
v_decl_2342_ = lean_ctor_get(v_c_2309_, 0);
v_k_2343_ = lean_ctor_get(v_c_2309_, 1);
v_params_2344_ = lean_ctor_get(v_decl_2342_, 2);
v_type_2345_ = lean_ctor_get(v_decl_2342_, 3);
v_value_2346_ = lean_ctor_get(v_decl_2342_, 4);
lean_inc_ref(v_value_2346_);
v___x_2347_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2346_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = 1;
lean_inc_ref(v_params_2344_);
lean_inc_ref(v_type_2345_);
lean_inc_ref(v_decl_2342_);
v___x_2350_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2349_, v_decl_2342_, v_type_2345_, v_params_2344_, v_a_2348_, v_a_2312_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
lean_inc_ref(v_k_2343_);
v___x_2352_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2343_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2380_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2380_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2380_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
uint8_t v___y_2358_; size_t v___x_2374_; size_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2374_ = lean_ptr_addr(v_k_2343_);
v___x_2375_ = lean_ptr_addr(v_a_2353_);
v___x_2376_ = lean_usize_dec_eq(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
v___y_2358_ = v___x_2376_;
goto v___jp_2357_;
}
else
{
size_t v___x_2377_; size_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2377_ = lean_ptr_addr(v_decl_2342_);
v___x_2378_ = lean_ptr_addr(v_a_2351_);
v___x_2379_ = lean_usize_dec_eq(v___x_2377_, v___x_2378_);
v___y_2358_ = v___x_2379_;
goto v___jp_2357_;
}
v___jp_2357_:
{
if (v___y_2358_ == 0)
{
lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2368_; 
v_isSharedCheck_2368_ = !lean_is_exclusive(v_c_2309_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; lean_object* v_unused_2370_; 
v_unused_2369_ = lean_ctor_get(v_c_2309_, 1);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_c_2309_, 0);
lean_dec(v_unused_2370_);
v___x_2360_ = v_c_2309_;
v_isShared_2361_ = v_isSharedCheck_2368_;
goto v_resetjp_2359_;
}
else
{
lean_dec(v_c_2309_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2368_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v_a_2353_);
lean_ctor_set(v___x_2360_, 0, v_a_2351_);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2351_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_a_2353_);
v___x_2363_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2363_);
v___x_2365_ = v___x_2355_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v___x_2372_; 
lean_dec(v_a_2353_);
lean_dec(v_a_2351_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v_c_2309_);
v___x_2372_ = v___x_2355_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_c_2309_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
else
{
lean_dec(v_a_2351_);
lean_dec_ref_known(v_c_2309_, 2);
return v___x_2352_;
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref_known(v_c_2309_, 2);
v_a_2381_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2350_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2350_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2309_, 2);
return v___x_2347_;
}
}
case 3:
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_c_2309_);
return v___x_2389_;
}
case 4:
{
lean_object* v_cases_2390_; lean_object* v_typeName_2391_; lean_object* v_resultType_2392_; lean_object* v_discr_2393_; lean_object* v_alts_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2447_; 
v_cases_2390_ = lean_ctor_get(v_c_2309_, 0);
lean_inc_ref(v_cases_2390_);
v_typeName_2391_ = lean_ctor_get(v_cases_2390_, 0);
v_resultType_2392_ = lean_ctor_get(v_cases_2390_, 1);
v_discr_2393_ = lean_ctor_get(v_cases_2390_, 2);
v_alts_2394_ = lean_ctor_get(v_cases_2390_, 3);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_cases_2390_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2396_ = v_cases_2390_;
v_isShared_2397_ = v_isSharedCheck_2447_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_alts_2394_);
lean_inc(v_discr_2393_);
lean_inc(v_resultType_2392_);
lean_inc(v_typeName_2391_);
lean_dec(v_cases_2390_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2447_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_alreadyFound_2398_; uint8_t v_relaxedReuse_2399_; lean_object* v_ownedness_2400_; uint8_t v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; uint8_t v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v_alreadyFound_2398_ = lean_ctor_get(v_a_2310_, 0);
v_relaxedReuse_2399_ = lean_ctor_get_uint8(v_a_2310_, sizeof(void*)*2);
v_ownedness_2400_ = lean_ctor_get(v_a_2310_, 1);
v___x_2401_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2398_, v_discr_2393_);
v___x_2402_ = 0;
v___x_2403_ = lean_box(v___x_2402_);
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2400_, v_discr_2393_, v___x_2403_);
lean_dec(v___x_2403_);
v___x_2405_ = 1;
v___x_2406_ = lean_unbox(v___x_2404_);
lean_dec(v___x_2404_);
v___x_2407_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2406_, v___x_2405_);
v___x_2408_ = lean_box(0);
lean_inc_n(v_discr_2393_, 2);
lean_inc_ref(v_alreadyFound_2398_);
v___x_2409_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2398_, v_discr_2393_, v___x_2408_);
lean_inc_ref(v_ownedness_2400_);
v___x_2410_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v_ownedness_2400_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*2, v_relaxedReuse_2399_);
v_sz_2411_ = lean_array_size(v_alts_2394_);
v___x_2412_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2394_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2407_, v_discr_2393_, v___x_2401_, v_sz_2411_, v___x_2412_, v_alts_2394_, v___x_2410_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec_ref_known(v___x_2410_, 2);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2438_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
size_t v___x_2418_; size_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = lean_ptr_addr(v_alts_2394_);
lean_dec_ref(v_alts_2394_);
v___x_2419_ = lean_ptr_addr(v_a_2414_);
v___x_2420_ = lean_usize_dec_eq(v___x_2418_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2433_; 
v_isSharedCheck_2433_ = !lean_is_exclusive(v_c_2309_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v_c_2309_, 0);
lean_dec(v_unused_2434_);
v___x_2422_ = v_c_2309_;
v_isShared_2423_ = v_isSharedCheck_2433_;
goto v_resetjp_2421_;
}
else
{
lean_dec(v_c_2309_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2433_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 3, v_a_2414_);
v___x_2425_ = v___x_2396_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_typeName_2391_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_resultType_2392_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_discr_2393_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_a_2414_);
v___x_2425_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2429_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2427_);
v___x_2429_ = v___x_2416_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v___x_2436_; 
lean_dec(v_a_2414_);
lean_del_object(v___x_2396_);
lean_dec(v_discr_2393_);
lean_dec_ref(v_resultType_2392_);
lean_dec(v_typeName_2391_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_c_2309_);
v___x_2436_ = v___x_2416_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_c_2309_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_del_object(v___x_2396_);
lean_dec_ref(v_alts_2394_);
lean_dec(v_discr_2393_);
lean_dec_ref(v_resultType_2392_);
lean_dec(v_typeName_2391_);
lean_dec_ref_known(v_c_2309_, 1);
v_a_2439_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2413_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2413_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
case 5:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_c_2309_);
return v___x_2448_;
}
case 6:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_c_2309_);
return v___x_2449_;
}
case 8:
{
lean_object* v_fvarId_2450_; lean_object* v_i_2451_; lean_object* v_y_2452_; lean_object* v_k_2453_; lean_object* v___x_2454_; 
v_fvarId_2450_ = lean_ctor_get(v_c_2309_, 0);
v_i_2451_ = lean_ctor_get(v_c_2309_, 1);
v_y_2452_ = lean_ctor_get(v_c_2309_, 2);
v_k_2453_ = lean_ctor_get(v_c_2309_, 3);
lean_inc_ref(v_k_2453_);
v___x_2454_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2453_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2479_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2479_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2479_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
size_t v___x_2459_; size_t v___x_2460_; uint8_t v___x_2461_; 
v___x_2459_ = lean_ptr_addr(v_k_2453_);
v___x_2460_ = lean_ptr_addr(v_a_2455_);
v___x_2461_ = lean_usize_dec_eq(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2471_; 
lean_inc(v_y_2452_);
lean_inc(v_i_2451_);
lean_inc(v_fvarId_2450_);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_c_2309_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; lean_object* v_unused_2473_; lean_object* v_unused_2474_; lean_object* v_unused_2475_; 
v_unused_2472_ = lean_ctor_get(v_c_2309_, 3);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v_c_2309_, 2);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_c_2309_, 1);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_c_2309_, 0);
lean_dec(v_unused_2475_);
v___x_2463_ = v_c_2309_;
v_isShared_2464_ = v_isSharedCheck_2471_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v_c_2309_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2471_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 3, v_a_2455_);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fvarId_2450_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_i_2451_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_y_2452_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_a_2455_);
v___x_2466_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2468_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2466_);
v___x_2468_ = v___x_2457_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v___x_2477_; 
lean_dec(v_a_2455_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_c_2309_);
v___x_2477_ = v___x_2457_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_c_2309_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2309_, 4);
return v___x_2454_;
}
}
case 9:
{
lean_object* v_fvarId_2480_; lean_object* v_i_2481_; lean_object* v_offset_2482_; lean_object* v_y_2483_; lean_object* v_ty_2484_; lean_object* v_k_2485_; lean_object* v___x_2486_; 
v_fvarId_2480_ = lean_ctor_get(v_c_2309_, 0);
v_i_2481_ = lean_ctor_get(v_c_2309_, 1);
v_offset_2482_ = lean_ctor_get(v_c_2309_, 2);
v_y_2483_ = lean_ctor_get(v_c_2309_, 3);
v_ty_2484_ = lean_ctor_get(v_c_2309_, 4);
v_k_2485_ = lean_ctor_get(v_c_2309_, 5);
lean_inc_ref(v_k_2485_);
v___x_2486_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2485_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2513_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2513_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2513_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
size_t v___x_2491_; size_t v___x_2492_; uint8_t v___x_2493_; 
v___x_2491_ = lean_ptr_addr(v_k_2485_);
v___x_2492_ = lean_ptr_addr(v_a_2487_);
v___x_2493_ = lean_usize_dec_eq(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2503_; 
lean_inc_ref(v_ty_2484_);
lean_inc(v_y_2483_);
lean_inc(v_offset_2482_);
lean_inc(v_i_2481_);
lean_inc(v_fvarId_2480_);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_c_2309_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; lean_object* v_unused_2509_; 
v_unused_2504_ = lean_ctor_get(v_c_2309_, 5);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_c_2309_, 4);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_c_2309_, 3);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_c_2309_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_c_2309_, 1);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_c_2309_, 0);
lean_dec(v_unused_2509_);
v___x_2495_ = v_c_2309_;
v_isShared_2496_ = v_isSharedCheck_2503_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v_c_2309_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2503_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 5, v_a_2487_);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_fvarId_2480_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_i_2481_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_offset_2482_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_y_2483_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_ty_2484_);
lean_ctor_set(v_reuseFailAlloc_2502_, 5, v_a_2487_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2500_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2498_);
v___x_2500_ = v___x_2489_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v___x_2511_; 
lean_dec(v_a_2487_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v_c_2309_);
v___x_2511_ = v___x_2489_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_c_2309_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2309_, 6);
return v___x_2486_;
}
}
default: 
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec_ref(v_c_2309_);
v___x_2514_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2515_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2514_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2524_, lean_object* v_discr_2525_, uint8_t v___x_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_bs_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec(v_discr_2525_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_bs_2529_);
return v___x_2537_;
}
else
{
lean_object* v___f_2538_; lean_object* v_v_2539_; lean_object* v___x_2540_; lean_object* v_bs_x27_2541_; lean_object* v_a_2543_; lean_object* v___y_2549_; lean_object* v___x_2559_; 
v___f_2538_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2539_ = lean_array_uget(v_bs_2529_, v_i_2528_);
v___x_2540_ = lean_unsigned_to_nat(0u);
v_bs_x27_2541_ = lean_array_uset(v_bs_2529_, v_i_2528_, v___x_2540_);
v___x_2559_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2539_, v___f_2538_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
if (lean_obj_tag(v_a_2560_) == 1)
{
lean_object* v_info_2561_; lean_object* v_code_2562_; uint8_t v___y_2564_; uint8_t v___x_2576_; 
v_info_2561_ = lean_ctor_get(v_a_2560_, 0);
v_code_2562_ = lean_ctor_get(v_a_2560_, 1);
v___x_2576_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2561_);
if (v___x_2576_ == 0)
{
v___y_2564_ = v___x_2526_;
goto v___jp_2563_;
}
else
{
v___y_2564_ = v___x_2576_;
goto v___jp_2563_;
}
v___jp_2563_:
{
if (v___y_2564_ == 0)
{
if (v___x_2524_ == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref_known(v___x_2559_, 1);
lean_inc_ref(v_code_2562_);
lean_inc_ref(v_info_2561_);
lean_inc(v_discr_2525_);
v___x_2565_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2525_, v_info_2561_, v_code_2562_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2560_, v_a_2566_);
v_a_2543_ = v___x_2567_;
goto v___jp_2542_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref_known(v_a_2560_, 2);
lean_dec_ref(v_bs_x27_2541_);
lean_dec(v_discr_2525_);
v_a_2568_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2565_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2565_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2560_, 2);
v___y_2549_ = v___x_2559_;
goto v___jp_2548_;
}
}
else
{
lean_dec_ref_known(v_a_2560_, 2);
v___y_2549_ = v___x_2559_;
goto v___jp_2548_;
}
}
}
else
{
lean_dec_ref_known(v_a_2560_, 1);
v___y_2549_ = v___x_2559_;
goto v___jp_2548_;
}
}
else
{
v___y_2549_ = v___x_2559_;
goto v___jp_2548_;
}
v___jp_2542_:
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_add(v_i_2528_, v___x_2544_);
v___x_2546_ = lean_array_uset(v_bs_x27_2541_, v_i_2528_, v_a_2543_);
v_i_2528_ = v___x_2545_;
v_bs_2529_ = v___x_2546_;
goto _start;
}
v___jp_2548_:
{
if (lean_obj_tag(v___y_2549_) == 0)
{
lean_object* v_a_2550_; 
v_a_2550_ = lean_ctor_get(v___y_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___y_2549_, 1);
v_a_2543_ = v_a_2550_;
goto v___jp_2542_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_bs_x27_2541_);
lean_dec(v_discr_2525_);
v_a_2551_ = lean_ctor_get(v___y_2549_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___y_2549_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___y_2549_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___y_2549_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2577_, lean_object* v_discr_2578_, lean_object* v___x_2579_, lean_object* v_sz_2580_, lean_object* v_i_2581_, lean_object* v_bs_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
uint8_t v___x_6774__boxed_2589_; uint8_t v___x_6776__boxed_2590_; size_t v_sz_boxed_2591_; size_t v_i_boxed_2592_; lean_object* v_res_2593_; 
v___x_6774__boxed_2589_ = lean_unbox(v___x_2577_);
v___x_6776__boxed_2590_ = lean_unbox(v___x_2579_);
v_sz_boxed_2591_ = lean_unbox_usize(v_sz_2580_);
lean_dec(v_sz_2580_);
v_i_boxed_2592_ = lean_unbox_usize(v_i_2581_);
lean_dec(v_i_2581_);
v_res_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6774__boxed_2589_, v_discr_2578_, v___x_6776__boxed_2590_, v_sz_boxed_2591_, v_i_boxed_2592_, v_bs_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2595_, v_x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_){
_start:
{
uint8_t v_res_2601_; lean_object* v_r_2602_; 
v_res_2601_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2598_, v_x_2599_, v_x_2600_);
lean_dec(v_x_2600_);
lean_dec_ref(v_x_2599_);
v_r_2602_ = lean_box(v_res_2601_);
return v_r_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2603_, lean_object* v_m_2604_, lean_object* v_a_2605_, lean_object* v_fallback_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2604_, v_a_2605_, v_fallback_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2608_, lean_object* v_m_2609_, lean_object* v_a_2610_, lean_object* v_fallback_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2608_, v_m_2609_, v_a_2610_, v_fallback_2611_);
lean_dec(v_fallback_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_m_2609_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2614_, v_x_2615_, v_x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2618_, lean_object* v_x_2619_, size_t v_x_2620_, lean_object* v_x_2621_){
_start:
{
uint8_t v___x_2622_; 
v___x_2622_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2619_, v_x_2620_, v_x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
size_t v_x_7325__boxed_2627_; uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_x_7325__boxed_2627_ = lean_unbox_usize(v_x_2625_);
lean_dec(v_x_2625_);
v_res_2628_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2623_, v_x_2624_, v_x_7325__boxed_2627_, v_x_2626_);
lean_dec(v_x_2626_);
lean_dec_ref(v_x_2624_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2630_, lean_object* v_m_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_m_2631_, v_a_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2634_, lean_object* v_m_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2634_, v_m_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_m_2635_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2638_, lean_object* v_x_2639_, size_t v_x_2640_, size_t v_x_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2639_, v_x_2640_, v_x_2641_, v_x_2642_, v_x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2645_, lean_object* v_x_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
size_t v_x_7338__boxed_2651_; size_t v_x_7339__boxed_2652_; lean_object* v_res_2653_; 
v_x_7338__boxed_2651_ = lean_unbox_usize(v_x_2647_);
lean_dec(v_x_2647_);
v_x_7339__boxed_2652_ = lean_unbox_usize(v_x_2648_);
lean_dec(v_x_2648_);
v_res_2653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2645_, v_x_2646_, v_x_7338__boxed_2651_, v_x_7339__boxed_2652_, v_x_2649_, v_x_2650_);
return v_res_2653_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2654_, lean_object* v_keys_2655_, lean_object* v_vals_2656_, lean_object* v_heq_2657_, lean_object* v_i_2658_, lean_object* v_k_2659_){
_start:
{
uint8_t v___x_2660_; 
v___x_2660_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2655_, v_i_2658_, v_k_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2661_, lean_object* v_keys_2662_, lean_object* v_vals_2663_, lean_object* v_heq_2664_, lean_object* v_i_2665_, lean_object* v_k_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2661_, v_keys_2662_, v_vals_2663_, v_heq_2664_, v_i_2665_, v_k_2666_);
lean_dec(v_k_2666_);
lean_dec_ref(v_vals_2663_);
lean_dec_ref(v_keys_2662_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2669_, lean_object* v_m_2670_, lean_object* v_query_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___redArg(v_m_2670_, v_query_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2673_, lean_object* v_m_2674_, lean_object* v_query_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5(v_00_u03b2_2673_, v_m_2674_, v_query_2675_);
lean_dec(v_query_2675_);
lean_dec_ref(v_m_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2677_, lean_object* v_n_2678_, lean_object* v_k_2679_, lean_object* v_v_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_n_2678_, v_k_2679_, v_v_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_2682_, size_t v_depth_2683_, lean_object* v_keys_2684_, lean_object* v_vals_2685_, lean_object* v_heq_2686_, lean_object* v_i_2687_, lean_object* v_entries_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___redArg(v_depth_2683_, v_keys_2684_, v_vals_2685_, v_i_2687_, v_entries_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2690_, lean_object* v_depth_2691_, lean_object* v_keys_2692_, lean_object* v_vals_2693_, lean_object* v_heq_2694_, lean_object* v_i_2695_, lean_object* v_entries_2696_){
_start:
{
size_t v_depth_boxed_2697_; lean_object* v_res_2698_; 
v_depth_boxed_2697_ = lean_unbox_usize(v_depth_2691_);
lean_dec(v_depth_2691_);
v_res_2698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__9(v_00_u03b2_2690_, v_depth_boxed_2697_, v_keys_2692_, v_vals_2693_, v_heq_2694_, v_i_2695_, v_entries_2696_);
lean_dec_ref(v_vals_2693_);
lean_dec_ref(v_keys_2692_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2699_, lean_object* v_m_2700_, lean_object* v_query_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___redArg(v_m_2700_, v_query_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2703_, lean_object* v_m_2704_, lean_object* v_query_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_2703_, v_m_2704_, v_query_2705_);
lean_dec(v_query_2705_);
lean_dec_ref(v_m_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_2707_, lean_object* v_x_2708_, lean_object* v_x_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_spec__11___redArg(v_x_2708_, v_x_2709_, v_x_2710_, v_x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_2713_, lean_object* v_m_2714_, lean_object* v_query_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_m_2714_, v_query_2715_, v_x_2716_, v_x_2717_, v_x_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_m_2722_, lean_object* v_query_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v_x_2726_, lean_object* v_x_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2_spec__5_spec__8_spec__10(v_00_u03b2_2721_, v_m_2722_, v_query_2723_, v_x_2724_, v_x_2725_, v_x_2726_, v_x_2727_);
lean_dec(v_query_2723_);
lean_dec_ref(v_m_2722_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v_toApplicative_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2802_; 
v___x_2738_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2739_ = l_StateRefT_x27_instMonad___redArg(v___x_2738_);
v_toApplicative_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2739_, 1);
lean_dec(v_unused_2803_);
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2802_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_toApplicative_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2802_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v_toFunctor_2744_; lean_object* v_toSeq_2745_; lean_object* v_toSeqLeft_2746_; lean_object* v_toSeqRight_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2800_; 
v_toFunctor_2744_ = lean_ctor_get(v_toApplicative_2740_, 0);
v_toSeq_2745_ = lean_ctor_get(v_toApplicative_2740_, 2);
v_toSeqLeft_2746_ = lean_ctor_get(v_toApplicative_2740_, 3);
v_toSeqRight_2747_ = lean_ctor_get(v_toApplicative_2740_, 4);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_toApplicative_2740_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v_toApplicative_2740_, 1);
lean_dec(v_unused_2801_);
v___x_2749_ = v_toApplicative_2740_;
v_isShared_2750_ = v_isSharedCheck_2800_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_toSeqRight_2747_);
lean_inc(v_toSeqLeft_2746_);
lean_inc(v_toSeq_2745_);
lean_inc(v_toFunctor_2744_);
lean_dec(v_toApplicative_2740_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2800_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___f_2758_; lean_object* v___x_2760_; 
v___f_2751_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2752_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2744_);
v___f_2753_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2753_, 0, v_toFunctor_2744_);
v___f_2754_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2754_, 0, v_toFunctor_2744_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___f_2753_);
lean_ctor_set(v___x_2755_, 1, v___f_2754_);
v___f_2756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2756_, 0, v_toSeqRight_2747_);
v___f_2757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2757_, 0, v_toSeqLeft_2746_);
v___f_2758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2758_, 0, v_toSeq_2745_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v___f_2756_);
lean_ctor_set(v___x_2749_, 3, v___f_2757_);
lean_ctor_set(v___x_2749_, 2, v___f_2758_);
lean_ctor_set(v___x_2749_, 1, v___f_2751_);
lean_ctor_set(v___x_2749_, 0, v___x_2755_);
v___x_2760_ = v___x_2749_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___f_2751_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v___f_2758_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v___f_2757_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v___f_2756_);
v___x_2760_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___f_2752_);
lean_ctor_set(v___x_2742_, 0, v___x_2760_);
v___x_2762_ = v___x_2742_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___f_2752_);
v___x_2762_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v_toApplicative_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2796_; 
v___x_2763_ = l_StateRefT_x27_instMonad___redArg(v___x_2762_);
v_toApplicative_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; 
v_unused_2797_ = lean_ctor_get(v___x_2763_, 1);
lean_dec(v_unused_2797_);
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2796_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_toApplicative_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2796_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_toFunctor_2768_; lean_object* v_toSeq_2769_; lean_object* v_toSeqLeft_2770_; lean_object* v_toSeqRight_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2794_; 
v_toFunctor_2768_ = lean_ctor_get(v_toApplicative_2764_, 0);
v_toSeq_2769_ = lean_ctor_get(v_toApplicative_2764_, 2);
v_toSeqLeft_2770_ = lean_ctor_get(v_toApplicative_2764_, 3);
v_toSeqRight_2771_ = lean_ctor_get(v_toApplicative_2764_, 4);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_toApplicative_2764_);
if (v_isSharedCheck_2794_ == 0)
{
lean_object* v_unused_2795_; 
v_unused_2795_ = lean_ctor_get(v_toApplicative_2764_, 1);
lean_dec(v_unused_2795_);
v___x_2773_ = v_toApplicative_2764_;
v_isShared_2774_ = v_isSharedCheck_2794_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_toSeqRight_2771_);
lean_inc(v_toSeqLeft_2770_);
lean_inc(v_toSeq_2769_);
lean_inc(v_toFunctor_2768_);
lean_dec(v_toApplicative_2764_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2794_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___f_2775_; lean_object* v___f_2776_; lean_object* v___f_2777_; lean_object* v___f_2778_; lean_object* v___x_2779_; lean_object* v___f_2780_; lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___x_2784_; 
v___f_2775_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2776_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2768_);
v___f_2777_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2777_, 0, v_toFunctor_2768_);
v___f_2778_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2778_, 0, v_toFunctor_2768_);
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___f_2777_);
lean_ctor_set(v___x_2779_, 1, v___f_2778_);
v___f_2780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2780_, 0, v_toSeqRight_2771_);
v___f_2781_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2781_, 0, v_toSeqLeft_2770_);
v___f_2782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2782_, 0, v_toSeq_2769_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v___f_2780_);
lean_ctor_set(v___x_2773_, 3, v___f_2781_);
lean_ctor_set(v___x_2773_, 2, v___f_2782_);
lean_ctor_set(v___x_2773_, 1, v___f_2775_);
lean_ctor_set(v___x_2773_, 0, v___x_2779_);
v___x_2784_ = v___x_2773_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___f_2775_);
lean_ctor_set(v_reuseFailAlloc_2793_, 2, v___f_2782_);
lean_ctor_set(v_reuseFailAlloc_2793_, 3, v___f_2781_);
lean_ctor_set(v_reuseFailAlloc_2793_, 4, v___f_2780_);
v___x_2784_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v___f_2776_);
lean_ctor_set(v___x_2766_, 0, v___x_2784_);
v___x_2786_ = v___x_2766_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___f_2776_);
v___x_2786_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2508__overap_2790_; lean_object* v___x_2791_; 
v___x_2787_ = l_StateRefT_x27_instMonad___redArg(v___x_2786_);
v___x_2788_ = lean_box(0);
v___x_2789_ = l_instInhabitedOfMonad___redArg(v___x_2787_, v___x_2788_);
v___x_2508__overap_2790_ = lean_panic_fn_borrowed(v___x_2789_, v_msg_2731_);
lean_dec(v___x_2789_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
v___x_2791_ = lean_apply_6(v___x_2508__overap_2790_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2791_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
return v_res_2811_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2813_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2814_ = lean_unsigned_to_nat(61u);
v___x_2815_ = lean_unsigned_to_nat(304u);
v___x_2816_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2817_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2818_ = l_mkPanicMessageWithDecl(v___x_2817_, v___x_2816_, v___x_2815_, v___x_2814_, v___x_2813_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
switch(lean_obj_tag(v_c_2819_))
{
case 0:
{
lean_object* v_decl_2826_; lean_object* v_value_2827_; 
v_decl_2826_ = lean_ctor_get(v_c_2819_, 0);
v_value_2827_ = lean_ctor_get(v_decl_2826_, 3);
if (lean_obj_tag(v_value_2827_) == 11)
{
lean_object* v_k_2828_; lean_object* v_var_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_inc_ref(v_value_2827_);
v_k_2828_ = lean_ctor_get(v_c_2819_, 1);
lean_inc_ref(v_k_2828_);
lean_dec_ref_known(v_c_2819_, 2);
v_var_2829_ = lean_ctor_get(v_value_2827_, 1);
lean_inc(v_var_2829_);
lean_dec_ref_known(v_value_2827_, 2);
v___x_2830_ = lean_st_ref_take(v_a_2820_);
v___x_2831_ = lean_box(0);
v___x_2832_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2830_, v_var_2829_, v___x_2831_);
v___x_2833_ = lean_st_ref_put(v_a_2820_, v___x_2832_);
v_c_2819_ = v_k_2828_;
goto _start;
}
else
{
lean_object* v_k_2835_; 
v_k_2835_ = lean_ctor_get(v_c_2819_, 1);
lean_inc_ref(v_k_2835_);
lean_dec_ref_known(v_c_2819_, 2);
v_c_2819_ = v_k_2835_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2837_; lean_object* v_k_2838_; lean_object* v_value_2839_; lean_object* v___x_2840_; 
v_decl_2837_ = lean_ctor_get(v_c_2819_, 0);
lean_inc_ref(v_decl_2837_);
v_k_2838_ = lean_ctor_get(v_c_2819_, 1);
lean_inc_ref(v_k_2838_);
lean_dec_ref_known(v_c_2819_, 2);
v_value_2839_ = lean_ctor_get(v_decl_2837_, 4);
lean_inc_ref(v_value_2839_);
lean_dec_ref(v_decl_2837_);
v___x_2840_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2839_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_dec_ref_known(v___x_2840_, 1);
v_c_2819_ = v_k_2838_;
goto _start;
}
else
{
lean_dec_ref(v_k_2838_);
return v___x_2840_;
}
}
case 3:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec_ref_known(v_c_2819_, 2);
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
case 4:
{
lean_object* v_cases_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2866_; 
v_cases_2844_ = lean_ctor_get(v_c_2819_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_c_2819_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2846_ = v_c_2819_;
v_isShared_2847_ = v_isSharedCheck_2866_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_cases_2844_);
lean_dec(v_c_2819_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2866_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v_alts_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v_alts_2848_ = lean_ctor_get(v_cases_2844_, 3);
lean_inc_ref(v_alts_2848_);
lean_dec_ref(v_cases_2844_);
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_array_get_size(v_alts_2848_);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_nat_dec_lt(v___x_2849_, v___x_2850_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref(v_alts_2848_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set_tag(v___x_2846_, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2851_);
v___x_2854_ = v___x_2846_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2851_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
else
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_nat_dec_le(v___x_2850_, v___x_2850_);
if (v___x_2856_ == 0)
{
if (v___x_2852_ == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref(v_alts_2848_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set_tag(v___x_2846_, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2851_);
v___x_2858_ = v___x_2846_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2851_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
else
{
size_t v___x_2860_; size_t v___x_2861_; lean_object* v___x_2862_; 
lean_del_object(v___x_2846_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = lean_usize_of_nat(v___x_2850_);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2848_, v___x_2860_, v___x_2861_, v___x_2851_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
lean_dec_ref(v_alts_2848_);
return v___x_2862_;
}
}
else
{
size_t v___x_2863_; size_t v___x_2864_; lean_object* v___x_2865_; 
lean_del_object(v___x_2846_);
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = lean_usize_of_nat(v___x_2850_);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2848_, v___x_2863_, v___x_2864_, v___x_2851_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
lean_dec_ref(v_alts_2848_);
return v___x_2865_;
}
}
}
}
case 5:
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2874_; 
v_isSharedCheck_2874_ = !lean_is_exclusive(v_c_2819_);
if (v_isSharedCheck_2874_ == 0)
{
lean_object* v_unused_2875_; 
v_unused_2875_ = lean_ctor_get(v_c_2819_, 0);
lean_dec(v_unused_2875_);
v___x_2868_ = v_c_2819_;
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v_c_2819_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = lean_box(0);
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
case 6:
{
lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
v_isSharedCheck_2883_ = !lean_is_exclusive(v_c_2819_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v_c_2819_, 0);
lean_dec(v_unused_2884_);
v___x_2877_ = v_c_2819_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v_c_2819_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = lean_box(0);
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
case 8:
{
lean_object* v_k_2885_; 
v_k_2885_ = lean_ctor_get(v_c_2819_, 3);
lean_inc_ref(v_k_2885_);
lean_dec_ref_known(v_c_2819_, 4);
v_c_2819_ = v_k_2885_;
goto _start;
}
case 9:
{
lean_object* v_k_2887_; 
v_k_2887_ = lean_ctor_get(v_c_2819_, 5);
lean_inc_ref(v_k_2887_);
lean_dec_ref_known(v_c_2819_, 6);
v_c_2819_ = v_k_2887_;
goto _start;
}
default: 
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec_ref(v_c_2819_);
v___x_2889_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2890_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2889_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
return v___x_2890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2891_, size_t v_i_2892_, size_t v_stop_2893_, lean_object* v_b_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___y_2902_; uint8_t v___x_2908_; 
v___x_2908_ = lean_usize_dec_eq(v_i_2892_, v_stop_2893_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_array_uget_borrowed(v_as_2891_, v_i_2892_);
switch(lean_obj_tag(v___x_2909_))
{
case 0:
{
lean_object* v_code_2910_; 
v_code_2910_ = lean_ctor_get(v___x_2909_, 2);
lean_inc_ref(v_code_2910_);
v___y_2902_ = v_code_2910_;
goto v___jp_2901_;
}
case 1:
{
lean_object* v_code_2911_; 
v_code_2911_ = lean_ctor_get(v___x_2909_, 1);
lean_inc_ref(v_code_2911_);
v___y_2902_ = v_code_2911_;
goto v___jp_2901_;
}
default: 
{
lean_object* v_code_2912_; 
v_code_2912_ = lean_ctor_get(v___x_2909_, 0);
lean_inc_ref(v_code_2912_);
v___y_2902_ = v_code_2912_;
goto v___jp_2901_;
}
}
}
else
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_b_2894_);
return v___x_2913_;
}
v___jp_2901_:
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2902_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; size_t v___x_2905_; size_t v___x_2906_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_add(v_i_2892_, v___x_2905_);
v_i_2892_ = v___x_2906_;
v_b_2894_ = v_a_2904_;
goto _start;
}
else
{
return v___x_2903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2914_, lean_object* v_i_2915_, lean_object* v_stop_2916_, lean_object* v_b_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
size_t v_i_boxed_2924_; size_t v_stop_boxed_2925_; lean_object* v_res_2926_; 
v_i_boxed_2924_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_stop_boxed_2925_ = lean_unbox_usize(v_stop_2916_);
lean_dec(v_stop_2916_);
v_res_2926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2914_, v_i_boxed_2924_, v_stop_boxed_2925_, v_b_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v_as_2914_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
return v_res_2934_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2940_, lean_object* v_v_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
if (lean_obj_tag(v_v_2941_) == 0)
{
lean_object* v_code_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2972_; 
v_code_2948_ = lean_ctor_get(v_v_2941_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_v_2941_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2950_ = v_v_2941_;
v_isShared_2951_ = v_isSharedCheck_2972_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_code_2948_);
lean_dec(v_v_2941_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2972_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; 
lean_inc(v___y_2946_);
lean_inc_ref(v___y_2945_);
lean_inc(v___y_2944_);
lean_inc_ref(v___y_2943_);
lean_inc_ref(v___y_2942_);
v___x_2952_ = lean_apply_7(v_f_2940_, v_code_2948_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, lean_box(0));
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2963_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2963_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2963_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v_a_2953_);
v___x_2958_ = v___x_2950_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2958_);
v___x_2960_ = v___x_2955_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2950_);
v_a_2964_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2952_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2952_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
else
{
lean_object* v___x_2973_; 
lean_dec_ref(v_f_2940_);
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_v_2941_);
return v___x_2973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2974_, lean_object* v_v_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2974_, v_v_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v___y_2976_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2983_, lean_object* v_f_2984_, lean_object* v_v_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2984_, v_v_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2993_, lean_object* v_f_2994_, lean_object* v_v_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
uint8_t v_pu_boxed_3002_; lean_object* v_res_3003_; 
v_pu_boxed_3002_ = lean_unbox(v_pu_2993_);
v_res_3003_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_3002_, v_f_2994_, v_v_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v___y_2996_);
return v_res_3003_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_box(0));
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_alreadyFound_3013_; uint8_t v_relaxedReuse_3014_; lean_object* v_ownedness_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; uint8_t v_relaxedReuse_3022_; 
v_relaxedReuse_3022_ = lean_ctor_get_uint8(v___y_3006_, sizeof(void*)*2);
if (v_relaxedReuse_3022_ == 0)
{
lean_object* v_ownedness_3023_; lean_object* v___x_3024_; 
v_ownedness_3023_ = lean_ctor_get(v___y_3006_, 1);
v___x_3024_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v_alreadyFound_3013_ = v___x_3024_;
v_relaxedReuse_3014_ = v_relaxedReuse_3022_;
v_ownedness_3015_ = v_ownedness_3023_;
v___y_3016_ = v___y_3007_;
v___y_3017_ = v___y_3008_;
v___y_3018_ = v___y_3009_;
v___y_3019_ = v___y_3010_;
goto v___jp_3012_;
}
else
{
lean_object* v_ownedness_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_ownedness_3025_ = lean_ctor_get(v___y_3006_, 1);
v___x_3026_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_3027_ = lean_st_mk_ref(v___x_3026_);
lean_inc_ref(v_code_3005_);
v___x_3028_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_3005_, v___x_3027_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3029_; 
lean_dec_ref_known(v___x_3028_, 1);
v___x_3029_ = lean_st_ref_get(v___x_3027_);
lean_dec(v___x_3027_);
v_alreadyFound_3013_ = v___x_3029_;
v_relaxedReuse_3014_ = v_relaxedReuse_3022_;
v_ownedness_3015_ = v_ownedness_3025_;
v___y_3016_ = v___y_3007_;
v___y_3017_ = v___y_3008_;
v___y_3018_ = v___y_3009_;
v___y_3019_ = v___y_3010_;
goto v___jp_3012_;
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v___x_3027_);
lean_dec_ref(v_code_3005_);
v_a_3030_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3028_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3028_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
v___jp_3012_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_inc_ref(v_ownedness_3015_);
v___x_3020_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3020_, 0, v_alreadyFound_3013_);
lean_ctor_set(v___x_3020_, 1, v_ownedness_3015_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*2, v_relaxedReuse_3014_);
v___x_3021_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_3005_, v___x_3020_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec_ref_known(v___x_3020_, 2);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_toSignature_3054_; lean_object* v_value_3055_; uint8_t v_recursive_3056_; lean_object* v_inlineAttr_x3f_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3082_; 
v_toSignature_3054_ = lean_ctor_get(v_decl_3047_, 0);
v_value_3055_ = lean_ctor_get(v_decl_3047_, 1);
v_recursive_3056_ = lean_ctor_get_uint8(v_decl_3047_, sizeof(void*)*3);
v_inlineAttr_x3f_3057_ = lean_ctor_get(v_decl_3047_, 2);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_decl_3047_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3059_ = v_decl_3047_;
v_isShared_3060_ = v_isSharedCheck_3082_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_inlineAttr_x3f_3057_);
lean_inc(v_value_3055_);
lean_inc(v_toSignature_3054_);
lean_dec(v_decl_3047_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3082_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___f_3061_; lean_object* v___x_3062_; 
v___f_3061_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_3062_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_3061_, v_value_3055_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3073_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3073_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3073_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v_a_3063_);
v___x_3068_ = v___x_3059_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_toSignature_3054_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_a_3063_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_inlineAttr_x3f_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*3, v_recursive_3056_);
v___x_3068_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3070_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3068_);
v___x_3070_ = v___x_3065_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_del_object(v___x_3059_);
lean_dec(v_inlineAttr_x3f_3057_);
lean_dec_ref(v_toSignature_3054_);
v_a_3074_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3062_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3062_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_a_3084_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3092_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3125_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3125_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3125_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
uint8_t v_resetReuse_3102_; 
v_resetReuse_3102_ = lean_ctor_get_uint8(v_a_3098_, sizeof(void*)*4 + 2);
lean_dec(v_a_3098_);
if (v_resetReuse_3102_ == 0)
{
lean_object* v___x_3104_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v_decl_3091_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_decl_3091_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
else
{
lean_object* v___x_3106_; 
lean_del_object(v___x_3100_);
lean_inc_ref(v_decl_3091_);
v___x_3106_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc_n(v_a_3107_, 2);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_3091_, v_a_3107_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_3111_ = 0;
lean_inc(v_a_3107_);
v___x_3112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v_a_3107_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*2, v___x_3111_);
v___x_3113_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3109_, v___x_3112_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec_ref_known(v___x_3112_, 2);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3115_, 0, v___x_3110_);
lean_ctor_set(v___x_3115_, 1, v_a_3107_);
lean_ctor_set_uint8(v___x_3115_, sizeof(void*)*2, v_resetReuse_3102_);
v___x_3116_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3114_, v___x_3115_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec_ref_known(v___x_3115_, 2);
return v___x_3116_;
}
else
{
lean_dec(v_a_3107_);
return v___x_3113_;
}
}
else
{
lean_dec(v_a_3107_);
return v___x_3108_;
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_decl_3091_);
v_a_3117_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3106_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3106_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_decl_3091_);
v_a_3126_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3097_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3097_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
return v_res_3140_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3147_ = 2;
v___x_3148_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3149_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3148_, v___x_3147_, v___x_3146_, v___x_3145_);
return v___x_3149_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3150_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = lean_unsigned_to_nat(2506150707u);
v___x_3207_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3208_ = l_Lean_Name_num___override(v___x_3207_, v___x_3206_);
return v___x_3208_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3211_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3212_ = l_Lean_Name_str___override(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3215_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3216_ = l_Lean_Name_str___override(v___x_3215_, v___x_3214_);
return v___x_3216_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_unsigned_to_nat(2u);
v___x_3218_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3219_ = l_Lean_Name_num___override(v___x_3218_, v___x_3217_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3221_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3222_ = 1;
v___x_3223_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3224_ = l_Lean_registerTraceClass(v___x_3221_, v___x_3222_, v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3226_;
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
