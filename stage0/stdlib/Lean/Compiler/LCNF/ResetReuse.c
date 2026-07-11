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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_3772__overap_101_; lean_object* v___x_102_; 
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
v___x_3772__overap_101_ = lean_panic_fn_borrowed(v___f_100_, v_msg_61_);
lean_dec_ref(v___f_100_);
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc_ref(v___y_62_);
v___x_102_ = lean_apply_6(v___x_3772__overap_101_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, lean_box(0));
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
lean_object* v_k_390_; lean_object* v_fvarId_391_; lean_object* v_binderName_392_; lean_object* v_type_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_453_; 
v_k_390_ = lean_ctor_get(v_c_154_, 1);
v_fvarId_391_ = lean_ctor_get(v_decl_388_, 0);
v_binderName_392_ = lean_ctor_get(v_decl_388_, 1);
v_type_393_ = lean_ctor_get(v_decl_388_, 2);
v_isSharedCheck_453_ = !lean_is_exclusive(v_decl_388_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v_decl_388_, 3);
lean_dec(v_unused_454_);
v___x_395_ = v_decl_388_;
v_isShared_396_ = v_isSharedCheck_453_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_type_393_);
lean_inc(v_binderName_392_);
lean_inc(v_fvarId_391_);
lean_dec(v_decl_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_453_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_i_397_; lean_object* v_args_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_452_; 
v_i_397_ = lean_ctor_get(v_value_389_, 0);
v_args_398_ = lean_ctor_get(v_value_389_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_value_389_);
if (v_isSharedCheck_452_ == 0)
{
v___x_400_ = v_value_389_;
v_isShared_401_ = v_isSharedCheck_452_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_args_398_);
lean_inc(v_i_397_);
lean_dec(v_value_389_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_452_;
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
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_441_; 
lean_inc_ref(v_k_390_);
v_isSharedCheck_441_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_442_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_443_);
v___x_406_ = v_c_154_;
v_isShared_407_ = v_isSharedCheck_441_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_c_154_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_441_;
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
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_i_397_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_args_398_);
v___x_412_ = v_reuseFailAlloc_440_;
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
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_fvarId_391_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_binderName_392_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_type_393_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v___x_412_);
v___x_414_ = v_reuseFailAlloc_439_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
uint8_t v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_nat_dec_eq(v_cidx_408_, v_cidx_409_);
v___x_416_ = lean_bool_not(v___x_415_);
v___x_417_ = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(v___x_417_, 0, v_w_153_);
lean_ctor_set(v___x_417_, 1, v_i_397_);
lean_ctor_set(v___x_417_, 2, v_args_398_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*3, v___x_416_);
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
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_del_object(v___x_400_);
lean_dec_ref(v_args_398_);
lean_dec_ref(v_i_397_);
lean_del_object(v___x_395_);
lean_dec_ref(v_type_393_);
lean_dec(v_binderName_392_);
lean_dec(v_fvarId_391_);
lean_dec_ref_known(v_c_154_, 2);
lean_dec(v_w_153_);
v_a_444_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_402_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_402_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
else
{
lean_object* v_k_455_; 
lean_dec(v_value_389_);
lean_dec_ref(v_decl_388_);
v_k_455_ = lean_ctor_get(v_c_154_, 1);
lean_inc_ref(v_k_455_);
v_k_168_ = v_k_455_;
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
lean_object* v_decl_456_; lean_object* v_k_457_; lean_object* v_params_458_; lean_object* v_type_459_; lean_object* v_value_460_; lean_object* v___x_461_; 
v_decl_456_ = lean_ctor_get(v_c_154_, 0);
v_k_457_ = lean_ctor_get(v_c_154_, 1);
v_params_458_ = lean_ctor_get(v_decl_456_, 2);
v_type_459_ = lean_ctor_get(v_decl_456_, 3);
v_value_460_ = lean_ctor_get(v_decl_456_, 4);
lean_inc_ref(v_value_460_);
lean_inc(v_w_153_);
v___x_461_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_152_, v_w_153_, v_value_460_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v_snd_463_; uint8_t v___x_464_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v_snd_463_ = lean_ctor_get(v_a_462_, 1);
lean_inc(v_snd_463_);
v___x_464_ = lean_unbox(v_snd_463_);
if (v___x_464_ == 0)
{
lean_dec(v_snd_463_);
lean_dec(v_a_462_);
lean_inc_ref(v_k_457_);
v_k_168_ = v_k_457_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
else
{
lean_object* v_fst_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_w_153_);
v_fst_465_ = lean_ctor_get(v_a_462_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_a_462_, 1);
lean_dec(v_unused_509_);
v___x_467_ = v_a_462_;
v_isShared_468_ = v_isSharedCheck_508_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_fst_465_);
lean_dec(v_a_462_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_508_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint8_t v___x_469_; lean_object* v___x_470_; 
v___x_469_ = 1;
lean_inc_ref(v_params_458_);
lean_inc_ref(v_type_459_);
lean_inc_ref(v_decl_456_);
v___x_470_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_469_, v_decl_456_, v_type_459_, v_params_458_, v_fst_465_, v_a_157_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_499_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_499_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_499_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_499_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___y_476_; uint8_t v___y_484_; size_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_ptr_addr(v_k_457_);
v___x_495_ = lean_usize_dec_eq(v___x_494_, v___x_494_);
if (v___x_495_ == 0)
{
v___y_484_ = v___x_495_;
goto v___jp_483_;
}
else
{
size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_ptr_addr(v_decl_456_);
v___x_497_ = lean_ptr_addr(v_a_471_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
v___y_484_ = v___x_498_;
goto v___jp_483_;
}
v___jp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___y_476_);
v___x_478_ = v___x_467_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___y_476_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_snd_463_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_478_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
v___jp_483_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_inc_ref(v_k_457_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_493_);
v___x_486_ = v_c_154_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_dec(v_c_154_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_a_471_);
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_k_457_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v___y_476_ = v___x_489_;
goto v___jp_475_;
}
}
}
else
{
lean_dec(v_a_471_);
v___y_476_ = v_c_154_;
goto v___jp_475_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_467_);
lean_dec(v_snd_463_);
lean_dec_ref_known(v_c_154_, 2);
v_a_500_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_470_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_470_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
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
return v___x_461_;
}
}
case 3:
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_w_153_);
v___x_510_ = 0;
v___x_511_ = lean_box(v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_c_154_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
case 4:
{
lean_object* v_cases_514_; lean_object* v_typeName_515_; lean_object* v_resultType_516_; lean_object* v_discr_517_; lean_object* v_alts_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_570_; 
v_cases_514_ = lean_ctor_get(v_c_154_, 0);
lean_inc_ref(v_cases_514_);
v_typeName_515_ = lean_ctor_get(v_cases_514_, 0);
v_resultType_516_ = lean_ctor_get(v_cases_514_, 1);
v_discr_517_ = lean_ctor_get(v_cases_514_, 2);
v_alts_518_ = lean_ctor_get(v_cases_514_, 3);
v_isSharedCheck_570_ = !lean_is_exclusive(v_cases_514_);
if (v_isSharedCheck_570_ == 0)
{
v___x_520_ = v_cases_514_;
v_isShared_521_ = v_isSharedCheck_570_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_alts_518_);
lean_inc(v_discr_517_);
lean_inc(v_resultType_516_);
lean_inc(v_typeName_515_);
lean_dec(v_cases_514_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_570_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; 
v_sz_522_ = lean_array_size(v_alts_518_);
v___x_523_ = ((size_t)0ULL);
lean_inc_ref(v_alts_518_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_152_, v_w_153_, v_sz_522_, v___x_523_, v_alts_518_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_561_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_561_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_561_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_561_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___x_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___y_541_; size_t v___x_547_; size_t v___x_548_; uint8_t v___x_549_; 
v___x_537_ = l_Array_unzip___redArg(v_a_525_);
lean_dec(v_a_525_);
v_fst_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_fst_538_);
v_snd_539_ = lean_ctor_get(v___x_537_, 1);
lean_inc(v_snd_539_);
lean_dec_ref(v___x_537_);
v___x_547_ = lean_ptr_addr(v_alts_518_);
lean_dec_ref(v_alts_518_);
v___x_548_ = lean_ptr_addr(v_fst_538_);
v___x_549_ = lean_usize_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_560_);
v___x_551_ = v_c_154_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_c_154_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 3, v_fst_538_);
v___x_554_ = v___x_520_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_typeName_515_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_resultType_516_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_discr_517_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_fst_538_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
v___y_541_ = v___x_556_;
goto v___jp_540_;
}
}
}
}
else
{
lean_dec(v_fst_538_);
lean_del_object(v___x_520_);
lean_dec(v_discr_517_);
lean_dec_ref(v_resultType_516_);
lean_dec(v_typeName_515_);
v___y_541_ = v_c_154_;
goto v___jp_540_;
}
v___jp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_box(v___y_531_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_533_);
v___x_535_ = v___x_527_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_array_get_size(v_snd_539_);
v___x_544_ = lean_nat_dec_lt(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec(v_snd_539_);
v___y_530_ = v___y_541_;
v___y_531_ = v___x_544_;
goto v___jp_529_;
}
else
{
if (v___x_544_ == 0)
{
lean_dec(v_snd_539_);
v___y_530_ = v___y_541_;
v___y_531_ = v___x_544_;
goto v___jp_529_;
}
else
{
size_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_usize_of_nat(v___x_543_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_539_, v___x_523_, v___x_545_);
lean_dec(v_snd_539_);
v___y_530_ = v___y_541_;
v___y_531_ = v___x_546_;
goto v___jp_529_;
}
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_del_object(v___x_520_);
lean_dec_ref(v_alts_518_);
lean_dec(v_discr_517_);
lean_dec_ref(v_resultType_516_);
lean_dec(v_typeName_515_);
lean_dec_ref_known(v_c_154_, 1);
v_a_562_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_524_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_524_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
case 5:
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_w_153_);
v___x_571_ = 0;
v___x_572_ = lean_box(v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_c_154_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
case 6:
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_w_153_);
v___x_575_ = 0;
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_c_154_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
case 8:
{
lean_object* v_k_579_; 
v_k_579_ = lean_ctor_get(v_c_154_, 3);
lean_inc_ref(v_k_579_);
v_k_168_ = v_k_579_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
case 9:
{
lean_object* v_k_580_; 
v_k_580_ = lean_ctor_get(v_c_154_, 5);
lean_inc_ref(v_k_580_);
v_k_168_ = v_k_580_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
default: 
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref(v_c_154_);
lean_dec(v_w_153_);
v___x_581_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
v___x_582_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_581_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
return v___x_582_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* v_info_583_, lean_object* v_w_584_, size_t v_sz_585_, size_t v_i_586_, lean_object* v_bs_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_usize_dec_lt(v_i_586_, v_sz_585_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v_w_584_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_bs_587_);
return v___x_595_;
}
else
{
lean_object* v_v_596_; lean_object* v___x_597_; lean_object* v_bs_x27_598_; lean_object* v___y_600_; 
v_v_596_ = lean_array_uget(v_bs_587_, v_i_586_);
v___x_597_ = lean_unsigned_to_nat(0u);
v_bs_x27_598_ = lean_array_uset(v_bs_587_, v_i_586_, v___x_597_);
switch(lean_obj_tag(v_v_596_))
{
case 0:
{
lean_object* v_code_625_; 
v_code_625_ = lean_ctor_get(v_v_596_, 2);
lean_inc_ref(v_code_625_);
v___y_600_ = v_code_625_;
goto v___jp_599_;
}
case 1:
{
lean_object* v_code_626_; 
v_code_626_ = lean_ctor_get(v_v_596_, 1);
lean_inc_ref(v_code_626_);
v___y_600_ = v_code_626_;
goto v___jp_599_;
}
default: 
{
lean_object* v_code_627_; 
v_code_627_ = lean_ctor_get(v_v_596_, 0);
lean_inc_ref(v_code_627_);
v___y_600_ = v_code_627_;
goto v___jp_599_;
}
}
v___jp_599_:
{
lean_object* v___x_601_; 
lean_inc(v_w_584_);
v___x_601_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_583_, v_w_584_, v___y_600_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v_fst_603_ = lean_ctor_get(v_a_602_, 0);
v_snd_604_ = lean_ctor_get(v_a_602_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_616_ == 0)
{
v___x_606_ = v_a_602_;
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_inc(v_fst_603_);
lean_dec(v_a_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_596_, v_fst_603_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_snd_604_);
v___x_610_ = v_reuseFailAlloc_615_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_add(v_i_586_, v___x_611_);
v___x_613_ = lean_array_uset(v_bs_x27_598_, v_i_586_, v___x_610_);
v_i_586_ = v___x_612_;
v_bs_587_ = v___x_613_;
goto _start;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_bs_x27_598_);
lean_dec(v_v_596_);
lean_dec(v_w_584_);
v_a_617_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_601_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_601_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* v_info_628_, lean_object* v_w_629_, lean_object* v_sz_630_, lean_object* v_i_631_, lean_object* v_bs_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_630_);
lean_dec(v_sz_630_);
v_i_boxed_640_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_628_, v_w_629_, v_sz_boxed_639_, v_i_boxed_640_, v_bs_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v_info_628_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* v_info_642_, lean_object* v_w_643_, lean_object* v_c_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_642_, v_w_643_, v_c_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_info_642_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v_ngen_655_; lean_object* v_namePrefix_656_; lean_object* v_idx_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_686_; 
v___x_654_ = lean_st_ref_get(v___y_652_);
v_ngen_655_ = lean_ctor_get(v___x_654_, 2);
lean_inc_ref(v_ngen_655_);
lean_dec(v___x_654_);
v_namePrefix_656_ = lean_ctor_get(v_ngen_655_, 0);
v_idx_657_ = lean_ctor_get(v_ngen_655_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_ngen_655_);
if (v_isSharedCheck_686_ == 0)
{
v___x_659_ = v_ngen_655_;
v_isShared_660_ = v_isSharedCheck_686_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_idx_657_);
lean_inc(v_namePrefix_656_);
lean_dec(v_ngen_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_686_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v_env_662_; lean_object* v_nextMacroScope_663_; lean_object* v_auxDeclNGen_664_; lean_object* v_traceState_665_; lean_object* v_cache_666_; lean_object* v_messages_667_; lean_object* v_infoState_668_; lean_object* v_snapshotTasks_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_684_; 
v___x_661_ = lean_st_ref_take(v___y_652_);
v_env_662_ = lean_ctor_get(v___x_661_, 0);
v_nextMacroScope_663_ = lean_ctor_get(v___x_661_, 1);
v_auxDeclNGen_664_ = lean_ctor_get(v___x_661_, 3);
v_traceState_665_ = lean_ctor_get(v___x_661_, 4);
v_cache_666_ = lean_ctor_get(v___x_661_, 5);
v_messages_667_ = lean_ctor_get(v___x_661_, 6);
v_infoState_668_ = lean_ctor_get(v___x_661_, 7);
v_snapshotTasks_669_ = lean_ctor_get(v___x_661_, 8);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v___x_661_, 2);
lean_dec(v_unused_685_);
v___x_671_ = v___x_661_;
v_isShared_672_ = v_isSharedCheck_684_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snapshotTasks_669_);
lean_inc(v_infoState_668_);
lean_inc(v_messages_667_);
lean_inc(v_cache_666_);
lean_inc(v_traceState_665_);
lean_inc(v_auxDeclNGen_664_);
lean_inc(v_nextMacroScope_663_);
lean_inc(v_env_662_);
lean_dec(v___x_661_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_684_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_r_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_idx_657_);
lean_inc(v_namePrefix_656_);
v_r_673_ = l_Lean_Name_num___override(v_namePrefix_656_, v_idx_657_);
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_idx_657_, v___x_674_);
lean_dec(v_idx_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_675_);
v___x_677_ = v___x_659_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_namePrefix_656_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_683_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 2, v___x_677_);
v___x_679_ = v___x_671_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_env_662_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_nextMacroScope_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_auxDeclNGen_664_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_traceState_665_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v_cache_666_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_messages_667_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_infoState_668_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_snapshotTasks_669_);
v___x_679_ = v_reuseFailAlloc_682_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_st_ref_set(v___y_652_, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_r_673_);
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_687_);
lean_dec(v___y_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v___x_696_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_694_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(0);
v___x_719_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
v___x_720_ = l_Lean_Expr_const___override(v___x_719_, v___x_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* v_x_721_, lean_object* v_info_722_, lean_object* v_c_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_n(v_a_731_, 2);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_722_, v_a_731_, v_c_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_787_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_787_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_787_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_787_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_snd_737_; uint8_t v___x_738_; 
v_snd_737_ = lean_ctor_get(v_a_733_, 1);
v___x_738_ = lean_unbox(v_snd_737_);
if (v___x_738_ == 0)
{
lean_object* v_fst_739_; lean_object* v___x_741_; 
lean_dec(v_a_731_);
lean_dec(v_x_721_);
v_fst_739_ = lean_ctor_get(v_a_733_, 0);
lean_inc(v_fst_739_);
lean_dec(v_a_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_fst_739_);
v___x_741_ = v___x_735_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_fst_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v_fst_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_735_);
v_fst_743_ = lean_ctor_get(v_a_733_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_a_733_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_a_733_, 1);
lean_dec(v_unused_786_);
v___x_745_ = v_a_733_;
v_isShared_746_ = v_isSharedCheck_785_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_fst_743_);
lean_dec(v_a_733_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_785_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
v___x_748_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_747_, v_a_726_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_776_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_776_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_776_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_776_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_size_753_; lean_object* v___x_754_; lean_object* v_lctx_755_; lean_object* v_nextIdx_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_775_; 
v_size_753_ = lean_ctor_get(v_info_722_, 2);
v___x_754_ = lean_st_ref_take(v_a_726_);
v_lctx_755_ = lean_ctor_get(v___x_754_, 0);
v_nextIdx_756_ = lean_ctor_get(v___x_754_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_775_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_775_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_nextIdx_756_);
lean_inc(v_lctx_755_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_775_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
uint8_t v___x_760_; lean_object* v___x_762_; 
v___x_760_ = 1;
lean_inc(v_size_753_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 11);
lean_ctor_set(v___x_745_, 1, v_x_721_);
lean_ctor_set(v___x_745_, 0, v_size_753_);
v___x_762_ = v___x_745_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_size_753_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_x_721_);
v___x_762_ = v_reuseFailAlloc_774_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_763_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
v___x_764_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_764_, 0, v_a_731_);
lean_ctor_set(v___x_764_, 1, v_a_749_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
lean_ctor_set(v___x_764_, 3, v___x_762_);
lean_inc_ref(v___x_764_);
v___x_765_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_760_, v_lctx_755_, v___x_764_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_765_);
v___x_767_ = v___x_758_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_nextIdx_756_);
v___x_767_ = v_reuseFailAlloc_773_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_768_ = lean_st_ref_set(v_a_726_, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_764_);
lean_ctor_set(v___x_769_, 1, v_fst_743_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_769_);
v___x_771_ = v___x_751_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_745_);
lean_dec(v_fst_743_);
lean_dec(v_a_731_);
lean_dec(v_x_721_);
v_a_777_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_748_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_748_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_731_);
lean_dec(v_x_721_);
v_a_788_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_732_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_732_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_c_723_);
lean_dec(v_x_721_);
v_a_796_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_730_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_730_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* v_x_804_, lean_object* v_info_805_, lean_object* v_c_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_804_, v_info_805_, v_c_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_info_805_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_827_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* v_x_828_, lean_object* v_as_829_, size_t v_i_830_, size_t v_stop_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_eq(v_i_830_, v_stop_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_833_ = lean_array_uget_borrowed(v_as_829_, v_i_830_);
v___x_834_ = 1;
lean_inc(v_x_828_);
v___x_835_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_828_);
v___x_836_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_834_, v___x_833_, v___x_835_);
lean_dec(v___x_835_);
if (v___x_836_ == 0)
{
size_t v___x_837_; size_t v___x_838_; 
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_830_, v___x_837_);
v_i_830_ = v___x_838_;
goto _start;
}
else
{
lean_dec(v_x_828_);
return v___x_836_;
}
}
else
{
uint8_t v___x_840_; 
lean_dec(v_x_828_);
v___x_840_ = 0;
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* v_x_841_, lean_object* v_as_842_, lean_object* v_i_843_, lean_object* v_stop_844_){
_start:
{
size_t v_i_boxed_845_; size_t v_stop_boxed_846_; uint8_t v_res_847_; lean_object* v_r_848_; 
v_i_boxed_845_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_stop_boxed_846_ = lean_unbox_usize(v_stop_844_);
lean_dec(v_stop_844_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_841_, v_as_842_, v_i_boxed_845_, v_stop_boxed_846_);
lean_dec_ref(v_as_842_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* v_instr_849_, lean_object* v_x_850_){
_start:
{
if (lean_obj_tag(v_instr_849_) == 0)
{
lean_object* v_decl_851_; lean_object* v_value_852_; 
v_decl_851_ = lean_ctor_get(v_instr_849_, 0);
v_value_852_ = lean_ctor_get(v_decl_851_, 3);
if (lean_obj_tag(v_value_852_) == 5)
{
lean_object* v_args_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_args_853_ = lean_ctor_get(v_value_852_, 1);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_array_get_size(v_args_853_);
v___x_856_ = lean_nat_dec_lt(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_dec(v_x_850_);
return v___x_856_;
}
else
{
if (v___x_856_ == 0)
{
lean_dec(v_x_850_);
return v___x_856_;
}
else
{
size_t v___x_857_; size_t v___x_858_; uint8_t v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_855_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_850_, v_args_853_, v___x_857_, v___x_858_);
return v___x_859_;
}
}
}
else
{
uint8_t v___x_860_; 
lean_dec(v_x_850_);
v___x_860_ = 0;
return v___x_860_;
}
}
else
{
uint8_t v___x_861_; 
lean_dec(v_x_850_);
v___x_861_ = 0;
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* v_instr_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_862_, v_x_863_);
lean_dec_ref(v_instr_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t v_x_866_){
_start:
{
switch(v_x_866_)
{
case 0:
{
lean_object* v___x_867_; 
v___x_867_ = lean_unsigned_to_nat(0u);
return v___x_867_;
}
case 1:
{
lean_object* v___x_868_; 
v___x_868_ = lean_unsigned_to_nat(1u);
return v___x_868_;
}
default: 
{
lean_object* v___x_869_; 
v___x_869_ = lean_unsigned_to_nat(2u);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object* v_x_870_){
_start:
{
uint8_t v_x_boxed_871_; lean_object* v_res_872_; 
v_x_boxed_871_ = lean_unbox(v_x_870_);
v_res_872_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_boxed_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(uint8_t v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx___boxed(lean_object* v_x_875_){
_start:
{
uint8_t v_x_4__boxed_876_; lean_object* v_res_877_; 
v_x_4__boxed_876_ = lean_unbox(v_x_875_);
v_res_877_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(v_x_4__boxed_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* v_k_878_){
_start:
{
lean_inc(v_k_878_);
return v_k_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* v_k_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_879_);
lean_dec(v_k_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* v_motive_881_, lean_object* v_ctorIdx_882_, uint8_t v_t_883_, lean_object* v_h_884_, lean_object* v_k_885_){
_start:
{
lean_inc(v_k_885_);
return v_k_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* v_motive_886_, lean_object* v_ctorIdx_887_, lean_object* v_t_888_, lean_object* v_h_889_, lean_object* v_k_890_){
_start:
{
uint8_t v_t_boxed_891_; lean_object* v_res_892_; 
v_t_boxed_891_ = lean_unbox(v_t_888_);
v_res_892_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(v_motive_886_, v_ctorIdx_887_, v_t_boxed_891_, v_h_889_, v_k_890_);
lean_dec(v_k_890_);
lean_dec(v_ctorIdx_887_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* v_ownedArg_893_){
_start:
{
lean_inc(v_ownedArg_893_);
return v_ownedArg_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* v_ownedArg_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_894_);
lean_dec(v_ownedArg_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* v_motive_896_, uint8_t v_t_897_, lean_object* v_h_898_, lean_object* v_ownedArg_899_){
_start:
{
lean_inc(v_ownedArg_899_);
return v_ownedArg_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* v_motive_900_, lean_object* v_t_901_, lean_object* v_h_902_, lean_object* v_ownedArg_903_){
_start:
{
uint8_t v_t_boxed_904_; lean_object* v_res_905_; 
v_t_boxed_904_ = lean_unbox(v_t_901_);
v_res_905_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_900_, v_t_boxed_904_, v_h_902_, v_ownedArg_903_);
lean_dec(v_ownedArg_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* v_other_906_){
_start:
{
lean_inc(v_other_906_);
return v_other_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* v_other_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_907_);
lean_dec(v_other_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* v_motive_909_, uint8_t v_t_910_, lean_object* v_h_911_, lean_object* v_other_912_){
_start:
{
lean_inc(v_other_912_);
return v_other_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* v_motive_913_, lean_object* v_t_914_, lean_object* v_h_915_, lean_object* v_other_916_){
_start:
{
uint8_t v_t_boxed_917_; lean_object* v_res_918_; 
v_t_boxed_917_ = lean_unbox(v_t_914_);
v_res_918_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_913_, v_t_boxed_917_, v_h_915_, v_other_916_);
lean_dec(v_other_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* v_none_919_){
_start:
{
lean_inc(v_none_919_);
return v_none_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* v_none_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_920_);
lean_dec(v_none_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* v_motive_922_, uint8_t v_t_923_, lean_object* v_h_924_, lean_object* v_none_925_){
_start:
{
lean_inc(v_none_925_);
return v_none_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* v_motive_926_, lean_object* v_t_927_, lean_object* v_h_928_, lean_object* v_none_929_){
_start:
{
uint8_t v_t_boxed_930_; lean_object* v_res_931_; 
v_t_boxed_930_ = lean_unbox(v_t_927_);
v_res_931_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(v_motive_926_, v_t_boxed_930_, v_h_928_, v_none_929_);
lean_dec(v_none_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* v_x_932_, lean_object* v_as_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_b_936_){
_start:
{
lean_object* v_a_939_; uint8_t v___x_943_; 
v___x_943_ = lean_usize_dec_lt(v_i_935_, v_sz_934_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_936_);
return v___x_944_;
}
else
{
lean_object* v_snd_945_; lean_object* v_fst_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_990_; 
v_snd_945_ = lean_ctor_get(v_b_936_, 1);
v_fst_946_ = lean_ctor_get(v_b_936_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_b_936_);
if (v_isSharedCheck_990_ == 0)
{
v___x_948_ = v_b_936_;
v_isShared_949_ = v_isSharedCheck_990_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_946_);
lean_dec(v_b_936_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_990_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_array_950_; lean_object* v_start_951_; lean_object* v_stop_952_; uint8_t v___x_953_; 
v_array_950_ = lean_ctor_get(v_snd_945_, 0);
v_start_951_ = lean_ctor_get(v_snd_945_, 1);
v_stop_952_ = lean_ctor_get(v_snd_945_, 2);
v___x_953_ = lean_nat_dec_lt(v_start_951_, v_stop_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_955_; 
if (v_isShared_949_ == 0)
{
v___x_955_ = v___x_948_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_snd_945_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
else
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_986_; 
lean_inc(v_stop_952_);
lean_inc(v_start_951_);
lean_inc_ref(v_array_950_);
v_isSharedCheck_986_ = !lean_is_exclusive(v_snd_945_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_987_ = lean_ctor_get(v_snd_945_, 2);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_snd_945_, 1);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_snd_945_, 0);
lean_dec(v_unused_989_);
v___x_959_ = v_snd_945_;
v_isShared_960_ = v_isSharedCheck_986_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_snd_945_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_986_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v_a_961_ = lean_array_uget_borrowed(v_as_933_, v_i_935_);
v___x_962_ = lean_array_fget(v_array_950_, v_start_951_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_add(v_start_951_, v___x_963_);
lean_dec(v_start_951_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___x_964_);
v___x_966_ = v___x_959_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_array_950_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_stop_952_);
v___x_966_ = v_reuseFailAlloc_985_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
uint8_t v___y_968_; 
if (lean_obj_tag(v_a_961_) == 1)
{
lean_object* v_fvarId_973_; uint8_t v___x_974_; 
v_fvarId_973_ = lean_ctor_get(v_a_961_, 0);
v___x_974_ = l_Lean_instBEqFVarId_beq(v_fvarId_973_, v_x_932_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec(v___x_962_);
lean_del_object(v___x_948_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_fst_946_);
lean_ctor_set(v___x_975_, 1, v___x_966_);
v_a_939_ = v___x_975_;
goto v___jp_938_;
}
else
{
uint8_t v___x_976_; 
v___x_976_ = lean_unbox(v_fst_946_);
switch(v___x_976_)
{
case 0:
{
uint8_t v_borrow_977_; 
v_borrow_977_ = lean_ctor_get_uint8(v___x_962_, sizeof(void*)*3);
lean_dec(v___x_962_);
if (v_borrow_977_ == 0)
{
uint8_t v___x_978_; 
v___x_978_ = lean_unbox(v_fst_946_);
lean_dec(v_fst_946_);
v___y_968_ = v___x_978_;
goto v___jp_967_;
}
else
{
uint8_t v___x_979_; 
lean_dec(v_fst_946_);
v___x_979_ = 1;
v___y_968_ = v___x_979_;
goto v___jp_967_;
}
}
case 1:
{
uint8_t v___x_980_; 
lean_dec(v___x_962_);
v___x_980_ = lean_unbox(v_fst_946_);
lean_dec(v_fst_946_);
v___y_968_ = v___x_980_;
goto v___jp_967_;
}
default: 
{
uint8_t v_borrow_981_; 
lean_dec(v_fst_946_);
v_borrow_981_ = lean_ctor_get_uint8(v___x_962_, sizeof(void*)*3);
lean_dec(v___x_962_);
if (v_borrow_981_ == 0)
{
uint8_t v___x_982_; 
v___x_982_ = 0;
v___y_968_ = v___x_982_;
goto v___jp_967_;
}
else
{
uint8_t v___x_983_; 
v___x_983_ = 1;
v___y_968_ = v___x_983_;
goto v___jp_967_;
}
}
}
}
}
else
{
lean_object* v___x_984_; 
lean_dec(v___x_962_);
lean_del_object(v___x_948_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_fst_946_);
lean_ctor_set(v___x_984_, 1, v___x_966_);
v_a_939_ = v___x_984_;
goto v___jp_938_;
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_box(v___y_968_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_966_);
lean_ctor_set(v___x_948_, 0, v___x_969_);
v___x_971_ = v___x_948_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
v_a_939_ = v___x_971_;
goto v___jp_938_;
}
}
}
}
}
}
}
v___jp_938_:
{
size_t v___x_940_; size_t v___x_941_; 
v___x_940_ = ((size_t)1ULL);
v___x_941_ = lean_usize_add(v_i_935_, v___x_940_);
v_i_935_ = v___x_941_;
v_b_936_ = v_a_939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* v_x_991_, lean_object* v_as_992_, lean_object* v_sz_993_, lean_object* v_i_994_, lean_object* v_b_995_, lean_object* v___y_996_){
_start:
{
size_t v_sz_boxed_997_; size_t v_i_boxed_998_; lean_object* v_res_999_; 
v_sz_boxed_997_ = lean_unbox_usize(v_sz_993_);
lean_dec(v_sz_993_);
v_i_boxed_998_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_991_, v_as_992_, v_sz_boxed_997_, v_i_boxed_998_, v_b_995_);
lean_dec_ref(v_as_992_);
lean_dec(v_x_991_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* v_instr_1000_, lean_object* v_x_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
if (lean_obj_tag(v_instr_1000_) == 0)
{
lean_object* v_decl_1018_; lean_object* v_value_1019_; 
v_decl_1018_ = lean_ctor_get(v_instr_1000_, 0);
v_value_1019_ = lean_ctor_get(v_decl_1018_, 3);
lean_inc(v_value_1019_);
switch(lean_obj_tag(v_value_1019_))
{
case 9:
{
lean_object* v_fn_1020_; lean_object* v_args_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref_known(v_instr_1000_, 1);
v_fn_1020_ = lean_ctor_get(v_value_1019_, 0);
v_args_1021_ = lean_ctor_get(v_value_1019_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_value_1019_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1023_ = v_value_1019_;
v_isShared_1024_ = v_isSharedCheck_1083_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_args_1021_);
lean_inc(v_fn_1020_);
lean_dec(v_value_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1083_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
lean_inc_ref(v_args_1021_);
lean_inc(v_fn_1020_);
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_fn_1020_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_args_1021_);
v___x_1026_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1020_, v_a_1006_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1073_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1073_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1073_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
if (lean_obj_tag(v_a_1028_) == 1)
{
lean_object* v_val_1032_; lean_object* v_params_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
lean_del_object(v___x_1030_);
lean_dec_ref(v___x_1026_);
v_val_1032_ = lean_ctor_get(v_a_1028_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v_a_1028_, 1);
v_params_1033_ = lean_ctor_get(v_val_1032_, 3);
lean_inc_ref(v_params_1033_);
lean_dec(v_val_1032_);
v___x_1034_ = 2;
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_array_get_size(v_params_1033_);
v___x_1037_ = l_Array_toSubarray___redArg(v_params_1033_, v___x_1035_, v___x_1036_);
v___x_1038_ = lean_box(v___x_1034_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1037_);
v_sz_1040_ = lean_array_size(v_args_1021_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1001_, v_args_1021_, v_sz_1040_, v___x_1041_, v___x_1039_);
lean_dec_ref(v_args_1021_);
lean_dec(v_x_1001_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_fst_1047_; lean_object* v___x_1049_; 
v_fst_1047_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_fst_1047_);
lean_dec(v_a_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v_fst_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_fst_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1042_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1042_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
uint8_t v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
lean_dec(v_a_1028_);
lean_dec_ref(v_args_1021_);
v___x_1060_ = 1;
v___x_1061_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1001_);
v___x_1062_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1060_, v___x_1026_, v___x_1061_);
lean_dec(v___x_1061_);
lean_dec_ref(v___x_1026_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1063_ = 2;
v___x_1064_ = lean_box(v___x_1063_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1064_);
v___x_1066_ = v___x_1030_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1068_ = 0;
v___x_1069_ = lean_box(v___x_1068_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1069_);
v___x_1071_ = v___x_1030_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_args_1021_);
lean_dec(v_x_1001_);
v_a_1074_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1027_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1027_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
case 10:
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1109_; 
v_isSharedCheck_1109_ = !lean_is_exclusive(v_instr_1000_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_instr_1000_, 0);
lean_dec(v_unused_1110_);
v___x_1085_ = v_instr_1000_;
v_isShared_1086_ = v_isSharedCheck_1109_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v_instr_1000_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1109_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_fn_1087_; lean_object* v_args_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1108_; 
v_fn_1087_ = lean_ctor_get(v_value_1019_, 0);
v_args_1088_ = lean_ctor_get(v_value_1019_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_value_1019_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1090_ = v_value_1019_;
v_isShared_1091_ = v_isSharedCheck_1108_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_args_1088_);
lean_inc(v_fn_1087_);
lean_dec(v_value_1019_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1108_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint8_t v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = 1;
if (v_isShared_1091_ == 0)
{
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fn_1087_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_args_1088_);
v___x_1094_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1001_);
v___x_1096_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1092_, v___x_1094_, v___x_1095_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1094_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1097_ = 2;
v___x_1098_ = lean_box(v___x_1097_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1098_);
v___x_1100_ = v___x_1085_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = 0;
v___x_1103_ = lean_box(v___x_1102_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1103_);
v___x_1105_ = v___x_1085_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1136_; 
v_isSharedCheck_1136_ = !lean_is_exclusive(v_instr_1000_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_instr_1000_, 0);
lean_dec(v_unused_1137_);
v___x_1112_ = v_instr_1000_;
v_isShared_1113_ = v_isSharedCheck_1136_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v_instr_1000_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1136_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_fvarId_1114_; lean_object* v_args_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1135_; 
v_fvarId_1114_ = lean_ctor_get(v_value_1019_, 0);
v_args_1115_ = lean_ctor_get(v_value_1019_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_value_1019_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1117_ = v_value_1019_;
v_isShared_1118_ = v_isSharedCheck_1135_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_args_1115_);
lean_inc(v_fvarId_1114_);
lean_dec(v_value_1019_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1135_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = 1;
if (v_isShared_1118_ == 0)
{
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_fvarId_1114_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_args_1115_);
v___x_1121_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1001_);
v___x_1123_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1119_, v___x_1121_, v___x_1122_);
lean_dec(v___x_1122_);
lean_dec_ref(v___x_1121_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = 2;
v___x_1125_ = lean_box(v___x_1124_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1125_);
v___x_1127_ = v___x_1112_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = 0;
v___x_1130_ = lean_box(v___x_1129_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1130_);
v___x_1132_ = v___x_1112_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
default: 
{
lean_dec(v_value_1019_);
goto v___jp_1008_;
}
}
}
else
{
goto v___jp_1008_;
}
v___jp_1008_:
{
uint8_t v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = 1;
v___x_1010_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1001_);
v___x_1011_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_1009_, v_instr_1000_, v___x_1010_);
lean_dec(v___x_1010_);
lean_dec_ref(v_instr_1000_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = 2;
v___x_1013_ = lean_box(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
else
{
uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = 1;
v___x_1016_ = lean_box(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* v_instr_1138_, lean_object* v_x_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1138_, v_x_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec_ref(v_a_1140_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* v_x_1147_, lean_object* v_as_1148_, size_t v_sz_1149_, size_t v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1147_, v_as_1148_, v_sz_1149_, v_i_1150_, v_b_1151_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* v_x_1159_, lean_object* v_as_1160_, lean_object* v_sz_1161_, lean_object* v_i_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_sz_boxed_1170_; size_t v_i_boxed_1171_; lean_object* v_res_1172_; 
v_sz_boxed_1170_ = lean_unbox_usize(v_sz_1161_);
lean_dec(v_sz_1161_);
v_i_boxed_1171_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1159_, v_as_1160_, v_sz_boxed_1170_, v_i_boxed_1171_, v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v_as_1160_);
lean_dec(v_x_1159_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* v_alt_1173_, lean_object* v_f_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___y_1182_; 
switch(lean_obj_tag(v_alt_1173_))
{
case 0:
{
lean_object* v_code_1201_; 
v_code_1201_ = lean_ctor_get(v_alt_1173_, 2);
lean_inc_ref(v_code_1201_);
v___y_1182_ = v_code_1201_;
goto v___jp_1181_;
}
case 1:
{
lean_object* v_code_1202_; 
v_code_1202_ = lean_ctor_get(v_alt_1173_, 1);
lean_inc_ref(v_code_1202_);
v___y_1182_ = v_code_1202_;
goto v___jp_1181_;
}
default: 
{
lean_object* v_code_1203_; 
v_code_1203_ = lean_ctor_get(v_alt_1173_, 0);
lean_inc_ref(v_code_1203_);
v___y_1182_ = v_code_1203_;
goto v___jp_1181_;
}
}
v___jp_1181_:
{
lean_object* v___x_1183_; 
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1183_ = lean_apply_7(v_f_1174_, v___y_1182_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, lean_box(0));
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1192_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1173_, v_a_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_alt_1173_);
v_a_1193_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1183_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1183_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* v_alt_1204_, lean_object* v_f_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1204_, v_f_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* v_x_1213_, lean_object* v_info_1214_, lean_object* v_c_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1213_, v_info_1214_, v_c_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v_a_1216_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* v_x_1223_, lean_object* v_info_1224_, lean_object* v_i_1225_, lean_object* v_as_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_as_1226_);
v___x_1234_ = lean_nat_dec_lt(v_i_1225_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_i_1225_);
lean_dec_ref(v_info_1224_);
lean_dec(v_x_1223_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_as_1226_);
return v___x_1235_;
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1236_ = lean_array_fget_borrowed(v_as_1226_, v_i_1225_);
lean_inc_ref(v_info_1224_);
lean_inc(v_x_1223_);
v___x_1237_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(v___x_1237_, 0, v_x_1223_);
lean_closure_set(v___x_1237_, 1, v_info_1224_);
lean_inc(v_a_1236_);
v___x_1238_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_1236_, v___x_1237_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; size_t v___x_1240_; size_t v___x_1241_; uint8_t v___x_1242_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_ptr_addr(v_a_1236_);
v___x_1241_ = lean_ptr_addr(v_a_1239_);
v___x_1242_ = lean_usize_dec_eq(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1225_, v___x_1243_);
v___x_1245_ = lean_array_fset(v_as_1226_, v_i_1225_, v_a_1239_);
lean_dec(v_i_1225_);
v_i_1225_ = v___x_1244_;
v_as_1226_ = v___x_1245_;
goto _start;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v_a_1239_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_i_1225_, v___x_1247_);
lean_dec(v_i_1225_);
v_i_1225_ = v___x_1248_;
goto _start;
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_as_1226_);
lean_dec(v_i_1225_);
lean_dec_ref(v_info_1224_);
lean_dec(v_x_1223_);
v_a_1250_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1238_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1238_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_1260_ = lean_unsigned_to_nat(61u);
v___x_1261_ = lean_unsigned_to_nat(247u);
v___x_1262_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
v___x_1263_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_1264_ = l_mkPanicMessageWithDecl(v___x_1263_, v___x_1262_, v___x_1261_, v___x_1260_, v___x_1259_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* v_x_1265_, lean_object* v_info_1266_, lean_object* v_c_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
switch(lean_obj_tag(v_c_1267_))
{
case 0:
{
lean_object* v_decl_1274_; lean_object* v_k_1275_; uint8_t v___x_1276_; lean_object* v_instr_1277_; uint8_t v___x_1278_; uint8_t v___x_1279_; 
v_decl_1274_ = lean_ctor_get(v_c_1267_, 0);
v_k_1275_ = lean_ctor_get(v_c_1267_, 1);
v___x_1276_ = 1;
v_instr_1277_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1276_, v_c_1267_);
lean_inc(v_x_1265_);
v___x_1278_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1277_, v_x_1265_);
v___x_1279_ = 1;
if (v___x_1278_ == 0)
{
lean_object* v___x_1280_; 
lean_inc_ref(v_k_1275_);
lean_inc_ref(v_info_1266_);
lean_inc(v_x_1265_);
v___x_1280_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1265_, v_info_1266_, v_k_1275_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1398_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1398_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1398_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___y_1286_; lean_object* v_snd_1292_; uint8_t v___x_1293_; 
v_snd_1292_ = lean_ctor_get(v_a_1281_, 1);
v___x_1293_ = lean_unbox(v_snd_1292_);
if (v___x_1293_ == 0)
{
lean_object* v_fst_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1383_; 
lean_inc(v_snd_1292_);
lean_del_object(v___x_1283_);
v_fst_1294_ = lean_ctor_get(v_a_1281_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v_a_1281_, 1);
lean_dec(v_unused_1384_);
v___x_1296_ = v_a_1281_;
v_isShared_1297_ = v_isSharedCheck_1383_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_fst_1294_);
lean_dec(v_a_1281_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1383_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; 
lean_inc(v_x_1265_);
v___x_1298_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1277_, v_x_1265_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1374_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1374_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1374_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___y_1304_; lean_object* v___y_1312_; uint8_t v___x_1316_; 
v___x_1316_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
switch(v___x_1316_)
{
case 0:
{
size_t v___x_1317_; size_t v___x_1318_; uint8_t v___x_1319_; 
lean_del_object(v___x_1301_);
lean_del_object(v___x_1296_);
lean_dec(v_snd_1292_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1317_ = lean_ptr_addr(v_k_1275_);
v___x_1318_ = lean_ptr_addr(v_fst_1294_);
v___x_1319_ = lean_usize_dec_eq(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_inc_ref(v_decl_1274_);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; lean_object* v_unused_1328_; 
v_unused_1327_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1328_);
v___x_1321_ = v_c_1267_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v_c_1267_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v_fst_1294_);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_decl_1274_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_fst_1294_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
v___y_1312_ = v___x_1324_;
goto v___jp_1311_;
}
}
}
else
{
lean_dec(v_fst_1294_);
v___y_1312_ = v_c_1267_;
goto v___jp_1311_;
}
}
case 1:
{
lean_object* v___x_1329_; 
lean_del_object(v___x_1301_);
lean_del_object(v___x_1296_);
lean_dec(v_snd_1292_);
v___x_1329_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1265_, v_info_1266_, v_fst_1294_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec_ref(v_info_1266_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1353_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___y_1335_; size_t v___x_1341_; size_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_ptr_addr(v_k_1275_);
v___x_1342_ = lean_ptr_addr(v_a_1330_);
v___x_1343_ = lean_usize_dec_eq(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_inc_ref(v_decl_1274_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1352_);
v___x_1345_ = v_c_1267_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v_c_1267_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v_a_1330_);
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_decl_1274_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_a_1330_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v___y_1335_ = v___x_1348_;
goto v___jp_1334_;
}
}
}
else
{
lean_dec(v_a_1330_);
v___y_1335_ = v_c_1267_;
goto v___jp_1334_;
}
v___jp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_box(v___x_1279_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___y_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1337_);
v___x_1339_ = v___x_1332_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref_known(v_c_1267_, 2);
v_a_1354_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1329_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1329_);
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
default: 
{
size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1362_ = lean_ptr_addr(v_k_1275_);
v___x_1363_ = lean_ptr_addr(v_fst_1294_);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_inc_ref(v_decl_1274_);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; lean_object* v_unused_1373_; 
v_unused_1372_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1373_);
v___x_1366_ = v_c_1267_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v_c_1267_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_fst_1294_);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_decl_1274_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_fst_1294_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
v___y_1304_ = v___x_1369_;
goto v___jp_1303_;
}
}
}
else
{
lean_dec(v_fst_1294_);
v___y_1304_ = v_c_1267_;
goto v___jp_1303_;
}
}
}
v___jp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___y_1304_);
v___x_1306_ = v___x_1296_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___y_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_snd_1292_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1306_);
v___x_1308_ = v___x_1301_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_box(v___x_1279_);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___y_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1296_);
lean_dec(v_fst_1294_);
lean_dec(v_snd_1292_);
lean_dec_ref_known(v_c_1267_, 2);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_a_1375_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1298_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1298_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
else
{
lean_object* v_fst_1385_; size_t v___x_1386_; size_t v___x_1387_; uint8_t v___x_1388_; 
lean_dec_ref(v_instr_1277_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_fst_1385_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_fst_1385_);
lean_dec(v_a_1281_);
v___x_1386_ = lean_ptr_addr(v_k_1275_);
v___x_1387_ = lean_ptr_addr(v_fst_1385_);
v___x_1388_ = lean_usize_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_inc_ref(v_decl_1274_);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; 
v_unused_1396_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1397_);
v___x_1390_ = v_c_1267_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v_c_1267_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v_fst_1385_);
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_decl_1274_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_fst_1385_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
v___y_1286_ = v___x_1393_;
goto v___jp_1285_;
}
}
}
else
{
lean_dec(v_fst_1385_);
v___y_1286_ = v_c_1267_;
goto v___jp_1285_;
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = lean_box(v___x_1279_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___y_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1288_);
v___x_1290_ = v___x_1283_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1277_);
lean_dec_ref_known(v_c_1267_, 2);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
return v___x_1280_;
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_instr_1277_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1399_ = lean_box(v___x_1279_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_c_1267_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
case 2:
{
lean_object* v_decl_1402_; lean_object* v_k_1403_; lean_object* v___x_1404_; 
v_decl_1402_ = lean_ctor_get(v_c_1267_, 0);
v_k_1403_ = lean_ctor_get(v_c_1267_, 1);
lean_inc_ref(v_k_1403_);
lean_inc_ref(v_info_1266_);
lean_inc(v_x_1265_);
v___x_1404_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1265_, v_info_1266_, v_k_1403_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v_params_1408_; lean_object* v_type_1409_; lean_object* v_value_1410_; lean_object* v___x_1411_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v_fst_1406_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_a_1405_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_a_1405_);
v_params_1408_ = lean_ctor_get(v_decl_1402_, 2);
v_type_1409_ = lean_ctor_get(v_decl_1402_, 3);
v_value_1410_ = lean_ctor_get(v_decl_1402_, 4);
lean_inc_ref(v_value_1410_);
v___x_1411_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1265_, v_info_1266_, v_value_1410_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v_fst_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1457_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v_fst_1413_ = lean_ctor_get(v_a_1412_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1412_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_a_1412_, 1);
lean_dec(v_unused_1458_);
v___x_1415_ = v_a_1412_;
v_isShared_1416_ = v_isSharedCheck_1457_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_fst_1413_);
lean_dec(v_a_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1457_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
uint8_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = 1;
lean_inc_ref(v_params_1408_);
lean_inc_ref(v_type_1409_);
lean_inc_ref(v_decl_1402_);
v___x_1418_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1417_, v_decl_1402_, v_type_1409_, v_params_1408_, v_fst_1413_, v_a_1270_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1448_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1448_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1448_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___y_1424_; uint8_t v___y_1432_; size_t v___x_1442_; size_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_ptr_addr(v_k_1403_);
v___x_1443_ = lean_ptr_addr(v_fst_1406_);
v___x_1444_ = lean_usize_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
v___y_1432_ = v___x_1444_;
goto v___jp_1431_;
}
else
{
size_t v___x_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = lean_ptr_addr(v_decl_1402_);
v___x_1446_ = lean_ptr_addr(v_a_1419_);
v___x_1447_ = lean_usize_dec_eq(v___x_1445_, v___x_1446_);
v___y_1432_ = v___x_1447_;
goto v___jp_1431_;
}
v___jp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v_snd_1407_);
lean_ctor_set(v___x_1415_, 0, v___y_1424_);
v___x_1426_ = v___x_1415_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___y_1424_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1407_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1426_);
v___x_1428_ = v___x_1421_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
v___jp_1431_:
{
if (v___y_1432_ == 0)
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; lean_object* v_unused_1441_; 
v_unused_1440_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1441_);
v___x_1434_ = v_c_1267_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v_c_1267_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_fst_1406_);
lean_ctor_set(v___x_1434_, 0, v_a_1419_);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1419_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_fst_1406_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v___y_1424_ = v___x_1437_;
goto v___jp_1423_;
}
}
}
else
{
lean_dec(v_a_1419_);
lean_dec(v_fst_1406_);
v___y_1424_ = v_c_1267_;
goto v___jp_1423_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_del_object(v___x_1415_);
lean_dec(v_snd_1407_);
lean_dec(v_fst_1406_);
lean_dec_ref_known(v_c_1267_, 2);
v_a_1449_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1418_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1418_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
else
{
lean_dec(v_snd_1407_);
lean_dec(v_fst_1406_);
lean_dec_ref_known(v_c_1267_, 2);
return v___x_1411_;
}
}
else
{
lean_dec_ref_known(v_c_1267_, 2);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
return v___x_1404_;
}
}
case 3:
{
lean_object* v___x_1459_; 
lean_dec_ref(v_info_1266_);
lean_inc_ref(v_c_1267_);
v___x_1459_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1267_, v_x_1265_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_c_1267_);
lean_ctor_set(v___x_1464_, 1, v_a_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref_known(v_c_1267_, 2);
v_a_1469_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1459_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1459_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
case 4:
{
lean_object* v_cases_1477_; lean_object* v___x_1478_; 
v_cases_1477_ = lean_ctor_get(v_c_1267_, 0);
lean_inc_ref(v_cases_1477_);
lean_inc(v_x_1265_);
lean_inc_ref(v_c_1267_);
v___x_1478_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1267_, v_x_1265_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1531_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1531_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1531_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_unbox(v_a_1479_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_dec_ref(v_cases_1477_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_c_1267_);
lean_ctor_set(v___x_1484_, 1, v_a_1479_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1484_);
v___x_1486_ = v___x_1481_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
else
{
lean_object* v_typeName_1488_; lean_object* v_resultType_1489_; lean_object* v_discr_1490_; lean_object* v_alts_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1530_; 
lean_del_object(v___x_1481_);
v_typeName_1488_ = lean_ctor_get(v_cases_1477_, 0);
v_resultType_1489_ = lean_ctor_get(v_cases_1477_, 1);
v_discr_1490_ = lean_ctor_get(v_cases_1477_, 2);
v_alts_1491_ = lean_ctor_get(v_cases_1477_, 3);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_cases_1477_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1493_ = v_cases_1477_;
v_isShared_1494_ = v_isSharedCheck_1530_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_alts_1491_);
lean_inc(v_discr_1490_);
lean_inc(v_resultType_1489_);
lean_inc(v_typeName_1488_);
lean_dec(v_cases_1477_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1530_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1491_);
v___x_1496_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1265_, v_info_1266_, v___x_1495_, v_alts_1491_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1521_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1521_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1521_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___y_1502_; size_t v___x_1507_; size_t v___x_1508_; uint8_t v___x_1509_; 
v___x_1507_ = lean_ptr_addr(v_alts_1491_);
lean_dec_ref(v_alts_1491_);
v___x_1508_ = lean_ptr_addr(v_a_1497_);
v___x_1509_ = lean_usize_dec_eq(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1520_);
v___x_1511_ = v_c_1267_;
v_isShared_1512_ = v_isSharedCheck_1519_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_c_1267_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1519_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 3, v_a_1497_);
v___x_1514_ = v___x_1493_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_typeName_1488_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_resultType_1489_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_discr_1490_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_a_1497_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1514_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v___y_1502_ = v___x_1516_;
goto v___jp_1501_;
}
}
}
}
else
{
lean_dec(v_a_1497_);
lean_del_object(v___x_1493_);
lean_dec(v_discr_1490_);
lean_dec_ref(v_resultType_1489_);
lean_dec(v_typeName_1488_);
v___y_1502_ = v_c_1267_;
goto v___jp_1501_;
}
v___jp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1502_);
lean_ctor_set(v___x_1503_, 1, v_a_1479_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1505_ = v___x_1499_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_1493_);
lean_dec_ref(v_alts_1491_);
lean_dec(v_discr_1490_);
lean_dec_ref(v_resultType_1489_);
lean_dec(v_typeName_1488_);
lean_dec(v_a_1479_);
lean_dec_ref_known(v_c_1267_, 1);
v_a_1522_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1496_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1496_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_cases_1477_);
lean_dec_ref_known(v_c_1267_, 1);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_a_1532_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1478_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1478_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
case 5:
{
lean_object* v___x_1540_; 
lean_dec_ref(v_info_1266_);
lean_inc_ref(v_c_1267_);
v___x_1540_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1267_, v_x_1265_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_c_1267_);
lean_ctor_set(v___x_1545_, 1, v_a_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1545_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref_known(v_c_1267_, 1);
v_a_1550_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1540_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1540_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
case 6:
{
lean_object* v___x_1558_; 
lean_dec_ref(v_info_1266_);
lean_inc_ref(v_c_1267_);
v___x_1558_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1267_, v_x_1265_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_c_1267_);
lean_ctor_set(v___x_1563_, 1, v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref_known(v_c_1267_, 1);
v_a_1568_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1558_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1558_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_1576_; lean_object* v_i_1577_; lean_object* v_y_1578_; lean_object* v_k_1579_; uint8_t v___x_1580_; lean_object* v_instr_1581_; uint8_t v___x_1582_; uint8_t v___x_1583_; 
v_fvarId_1576_ = lean_ctor_get(v_c_1267_, 0);
v_i_1577_ = lean_ctor_get(v_c_1267_, 1);
v_y_1578_ = lean_ctor_get(v_c_1267_, 2);
v_k_1579_ = lean_ctor_get(v_c_1267_, 3);
v___x_1580_ = 1;
v_instr_1581_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1580_, v_c_1267_);
lean_inc(v_x_1265_);
v___x_1582_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1581_, v_x_1265_);
v___x_1583_ = 1;
if (v___x_1582_ == 0)
{
lean_object* v___x_1584_; 
lean_inc_ref(v_k_1579_);
lean_inc_ref(v_info_1266_);
lean_inc(v_x_1265_);
v___x_1584_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1265_, v_info_1266_, v_k_1579_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1710_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1710_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1710_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___y_1590_; lean_object* v_snd_1596_; uint8_t v___x_1597_; 
v_snd_1596_ = lean_ctor_get(v_a_1585_, 1);
v___x_1597_ = lean_unbox(v_snd_1596_);
if (v___x_1597_ == 0)
{
lean_object* v_fst_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1693_; 
lean_inc(v_snd_1596_);
lean_del_object(v___x_1587_);
v_fst_1598_ = lean_ctor_get(v_a_1585_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1585_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v_a_1585_, 1);
lean_dec(v_unused_1694_);
v___x_1600_ = v_a_1585_;
v_isShared_1601_ = v_isSharedCheck_1693_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_fst_1598_);
lean_dec(v_a_1585_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1693_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; 
lean_inc(v_x_1265_);
v___x_1602_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1581_, v_x_1265_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1684_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1684_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1684_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___y_1608_; lean_object* v___y_1616_; uint8_t v___x_1620_; 
v___x_1620_ = lean_unbox(v_a_1603_);
lean_dec(v_a_1603_);
switch(v___x_1620_)
{
case 0:
{
size_t v___x_1621_; size_t v___x_1622_; uint8_t v___x_1623_; 
lean_del_object(v___x_1605_);
lean_del_object(v___x_1600_);
lean_dec(v_snd_1596_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1621_ = lean_ptr_addr(v_k_1579_);
v___x_1622_ = lean_ptr_addr(v_fst_1598_);
v___x_1623_ = lean_usize_dec_eq(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_inc(v_y_1578_);
lean_inc(v_i_1577_);
lean_inc(v_fvarId_1576_);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; lean_object* v_unused_1632_; lean_object* v_unused_1633_; lean_object* v_unused_1634_; 
v_unused_1631_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1634_);
v___x_1625_ = v_c_1267_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v_c_1267_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 3, v_fst_1598_);
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_fvarId_1576_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_i_1577_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_y_1578_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v_fst_1598_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v___y_1616_ = v___x_1628_;
goto v___jp_1615_;
}
}
}
else
{
lean_dec(v_fst_1598_);
v___y_1616_ = v_c_1267_;
goto v___jp_1615_;
}
}
case 1:
{
lean_object* v___x_1635_; 
lean_del_object(v___x_1605_);
lean_del_object(v___x_1600_);
lean_dec(v_snd_1596_);
v___x_1635_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1265_, v_info_1266_, v_fst_1598_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec_ref(v_info_1266_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1661_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1661_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1661_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___y_1641_; size_t v___x_1647_; size_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = lean_ptr_addr(v_k_1579_);
v___x_1648_ = lean_ptr_addr(v_a_1636_);
v___x_1649_ = lean_usize_dec_eq(v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_inc(v_y_1578_);
lean_inc(v_i_1577_);
lean_inc(v_fvarId_1576_);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; lean_object* v_unused_1659_; lean_object* v_unused_1660_; 
v_unused_1657_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1660_);
v___x_1651_ = v_c_1267_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_dec(v_c_1267_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 3, v_a_1636_);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_fvarId_1576_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_i_1577_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_y_1578_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_a_1636_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
v___y_1641_ = v___x_1654_;
goto v___jp_1640_;
}
}
}
else
{
lean_dec(v_a_1636_);
v___y_1641_ = v_c_1267_;
goto v___jp_1640_;
}
v___jp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = lean_box(v___x_1583_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___y_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1643_);
v___x_1645_ = v___x_1638_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref_known(v_c_1267_, 4);
v_a_1662_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1635_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1635_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
default: 
{
size_t v___x_1670_; size_t v___x_1671_; uint8_t v___x_1672_; 
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1670_ = lean_ptr_addr(v_k_1579_);
v___x_1671_ = lean_ptr_addr(v_fst_1598_);
v___x_1672_ = lean_usize_dec_eq(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_inc(v_y_1578_);
lean_inc(v_i_1577_);
lean_inc(v_fvarId_1576_);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1680_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1683_);
v___x_1674_ = v_c_1267_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v_c_1267_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 3, v_fst_1598_);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_fvarId_1576_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_i_1577_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_y_1578_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_fst_1598_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v___y_1608_ = v___x_1677_;
goto v___jp_1607_;
}
}
}
else
{
lean_dec(v_fst_1598_);
v___y_1608_ = v_c_1267_;
goto v___jp_1607_;
}
}
}
v___jp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___y_1608_);
v___x_1610_ = v___x_1600_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___y_1608_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_snd_1596_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1610_);
v___x_1612_ = v___x_1605_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_box(v___x_1583_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___y_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1600_);
lean_dec(v_fst_1598_);
lean_dec(v_snd_1596_);
lean_dec_ref_known(v_c_1267_, 4);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_a_1685_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1602_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1602_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
else
{
lean_object* v_fst_1695_; size_t v___x_1696_; size_t v___x_1697_; uint8_t v___x_1698_; 
lean_dec_ref(v_instr_1581_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_fst_1695_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_fst_1695_);
lean_dec(v_a_1585_);
v___x_1696_ = lean_ptr_addr(v_k_1579_);
v___x_1697_ = lean_ptr_addr(v_fst_1695_);
v___x_1698_ = lean_usize_dec_eq(v___x_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_inc(v_y_1578_);
lean_inc(v_i_1577_);
lean_inc(v_fvarId_1576_);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1706_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1709_);
v___x_1700_ = v_c_1267_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_c_1267_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 3, v_fst_1695_);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fvarId_1576_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_i_1577_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_y_1578_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_fst_1695_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
v___y_1590_ = v___x_1703_;
goto v___jp_1589_;
}
}
}
else
{
lean_dec(v_fst_1695_);
v___y_1590_ = v_c_1267_;
goto v___jp_1589_;
}
}
v___jp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = lean_box(v___x_1583_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___y_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1592_);
v___x_1594_ = v___x_1587_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1581_);
lean_dec_ref_known(v_c_1267_, 4);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
return v___x_1584_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec_ref(v_instr_1581_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1711_ = lean_box(v___x_1583_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_c_1267_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
case 9:
{
lean_object* v_fvarId_1714_; lean_object* v_i_1715_; lean_object* v_offset_1716_; lean_object* v_y_1717_; lean_object* v_ty_1718_; lean_object* v_k_1719_; uint8_t v___x_1720_; lean_object* v_instr_1721_; uint8_t v___x_1722_; uint8_t v___x_1723_; 
v_fvarId_1714_ = lean_ctor_get(v_c_1267_, 0);
v_i_1715_ = lean_ctor_get(v_c_1267_, 1);
v_offset_1716_ = lean_ctor_get(v_c_1267_, 2);
v_y_1717_ = lean_ctor_get(v_c_1267_, 3);
v_ty_1718_ = lean_ctor_get(v_c_1267_, 4);
v_k_1719_ = lean_ctor_get(v_c_1267_, 5);
v___x_1720_ = 1;
v_instr_1721_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1720_, v_c_1267_);
lean_inc(v_x_1265_);
v___x_1722_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1721_, v_x_1265_);
v___x_1723_ = 1;
if (v___x_1722_ == 0)
{
lean_object* v___x_1724_; 
lean_inc_ref(v_k_1719_);
lean_inc_ref(v_info_1266_);
lean_inc(v_x_1265_);
v___x_1724_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1265_, v_info_1266_, v_k_1719_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1858_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1858_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1858_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___y_1730_; lean_object* v_snd_1736_; uint8_t v___x_1737_; 
v_snd_1736_ = lean_ctor_get(v_a_1725_, 1);
v___x_1737_ = lean_unbox(v_snd_1736_);
if (v___x_1737_ == 0)
{
lean_object* v_fst_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1839_; 
lean_inc(v_snd_1736_);
lean_del_object(v___x_1727_);
v_fst_1738_ = lean_ctor_get(v_a_1725_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1725_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v_a_1725_, 1);
lean_dec(v_unused_1840_);
v___x_1740_ = v_a_1725_;
v_isShared_1741_ = v_isSharedCheck_1839_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_fst_1738_);
lean_dec(v_a_1725_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1839_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; 
lean_inc(v_x_1265_);
v___x_1742_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1721_, v_x_1265_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1830_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1830_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1830_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___y_1748_; lean_object* v___y_1756_; uint8_t v___x_1760_; 
v___x_1760_ = lean_unbox(v_a_1743_);
lean_dec(v_a_1743_);
switch(v___x_1760_)
{
case 0:
{
size_t v___x_1761_; size_t v___x_1762_; uint8_t v___x_1763_; 
lean_del_object(v___x_1745_);
lean_del_object(v___x_1740_);
lean_dec(v_snd_1736_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1761_ = lean_ptr_addr(v_k_1719_);
v___x_1762_ = lean_ptr_addr(v_fst_1738_);
v___x_1763_ = lean_usize_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_inc_ref(v_ty_1718_);
lean_inc(v_y_1717_);
lean_inc(v_offset_1716_);
lean_inc(v_i_1715_);
lean_inc(v_fvarId_1714_);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1771_ = lean_ctor_get(v_c_1267_, 5);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_c_1267_, 4);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1776_);
v___x_1765_ = v_c_1267_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v_c_1267_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 5, v_fst_1738_);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fvarId_1714_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_i_1715_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_offset_1716_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_y_1717_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v_ty_1718_);
lean_ctor_set(v_reuseFailAlloc_1769_, 5, v_fst_1738_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
v___y_1756_ = v___x_1768_;
goto v___jp_1755_;
}
}
}
else
{
lean_dec(v_fst_1738_);
v___y_1756_ = v_c_1267_;
goto v___jp_1755_;
}
}
case 1:
{
lean_object* v___x_1777_; 
lean_del_object(v___x_1745_);
lean_del_object(v___x_1740_);
lean_dec(v_snd_1736_);
v___x_1777_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1265_, v_info_1266_, v_fst_1738_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec_ref(v_info_1266_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1805_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1805_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1805_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___y_1783_; size_t v___x_1789_; size_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_ptr_addr(v_k_1719_);
v___x_1790_ = lean_ptr_addr(v_a_1778_);
v___x_1791_ = lean_usize_dec_eq(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_inc_ref(v_ty_1718_);
lean_inc(v_y_1717_);
lean_inc(v_offset_1716_);
lean_inc(v_i_1715_);
lean_inc(v_fvarId_1714_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; 
v_unused_1799_ = lean_ctor_get(v_c_1267_, 5);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_c_1267_, 4);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1804_);
v___x_1793_ = v_c_1267_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_dec(v_c_1267_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 5, v_a_1778_);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_fvarId_1714_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_i_1715_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_offset_1716_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_y_1717_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_ty_1718_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v_a_1778_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
v___y_1783_ = v___x_1796_;
goto v___jp_1782_;
}
}
}
else
{
lean_dec(v_a_1778_);
v___y_1783_ = v_c_1267_;
goto v___jp_1782_;
}
v___jp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_box(v___x_1723_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___y_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1785_);
v___x_1787_ = v___x_1780_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref_known(v_c_1267_, 6);
v_a_1806_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1777_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1777_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
default: 
{
size_t v___x_1814_; size_t v___x_1815_; uint8_t v___x_1816_; 
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1814_ = lean_ptr_addr(v_k_1719_);
v___x_1815_ = lean_ptr_addr(v_fst_1738_);
v___x_1816_ = lean_usize_dec_eq(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_inc_ref(v_ty_1718_);
lean_inc(v_y_1717_);
lean_inc(v_offset_1716_);
lean_inc(v_i_1715_);
lean_inc(v_fvarId_1714_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; 
v_unused_1824_ = lean_ctor_get(v_c_1267_, 5);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_c_1267_, 4);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1829_);
v___x_1818_ = v_c_1267_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_c_1267_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 5, v_fst_1738_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_fvarId_1714_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_i_1715_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_offset_1716_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_y_1717_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_ty_1718_);
lean_ctor_set(v_reuseFailAlloc_1822_, 5, v_fst_1738_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
v___y_1748_ = v___x_1821_;
goto v___jp_1747_;
}
}
}
else
{
lean_dec(v_fst_1738_);
v___y_1748_ = v_c_1267_;
goto v___jp_1747_;
}
}
}
v___jp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___y_1748_);
v___x_1750_ = v___x_1740_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___y_1748_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_snd_1736_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1750_);
v___x_1752_ = v___x_1745_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
v___jp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_box(v___x_1723_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_del_object(v___x_1740_);
lean_dec(v_fst_1738_);
lean_dec(v_snd_1736_);
lean_dec_ref_known(v_c_1267_, 6);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_a_1831_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1742_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1742_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v_fst_1841_; size_t v___x_1842_; size_t v___x_1843_; uint8_t v___x_1844_; 
lean_dec_ref(v_instr_1721_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v_fst_1841_ = lean_ctor_get(v_a_1725_, 0);
lean_inc(v_fst_1841_);
lean_dec(v_a_1725_);
v___x_1842_ = lean_ptr_addr(v_k_1719_);
v___x_1843_ = lean_ptr_addr(v_fst_1841_);
v___x_1844_ = lean_usize_dec_eq(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_inc_ref(v_ty_1718_);
lean_inc(v_y_1717_);
lean_inc(v_offset_1716_);
lean_inc(v_i_1715_);
lean_inc(v_fvarId_1714_);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; 
v_unused_1852_ = lean_ctor_get(v_c_1267_, 5);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_c_1267_, 4);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_c_1267_, 2);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_c_1267_, 1);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_c_1267_, 0);
lean_dec(v_unused_1857_);
v___x_1846_ = v_c_1267_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_dec(v_c_1267_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 5, v_fst_1841_);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_fvarId_1714_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_i_1715_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_offset_1716_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_y_1717_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_ty_1718_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_fst_1841_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
v___y_1730_ = v___x_1849_;
goto v___jp_1729_;
}
}
}
else
{
lean_dec(v_fst_1841_);
v___y_1730_ = v_c_1267_;
goto v___jp_1729_;
}
}
v___jp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1731_ = lean_box(v___x_1723_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___y_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1732_);
v___x_1734_ = v___x_1727_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1721_);
lean_dec_ref_known(v_c_1267_, 6);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
return v___x_1724_;
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref(v_instr_1721_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1859_ = lean_box(v___x_1723_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v_c_1267_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
default: 
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v_c_1267_);
lean_dec_ref(v_info_1266_);
lean_dec(v_x_1265_);
v___x_1862_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
v___x_1863_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_1862_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object* v_x_1864_, lean_object* v_info_1865_, lean_object* v_c_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1873_; 
lean_inc_ref(v_info_1865_);
lean_inc(v_x_1864_);
v___x_1873_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1864_, v_info_1865_, v_c_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1886_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1886_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1886_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_snd_1878_; uint8_t v___x_1879_; 
v_snd_1878_ = lean_ctor_get(v_a_1874_, 1);
v___x_1879_ = lean_unbox(v_snd_1878_);
if (v___x_1879_ == 0)
{
lean_object* v_fst_1880_; lean_object* v___x_1881_; 
lean_del_object(v___x_1876_);
v_fst_1880_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_fst_1880_);
lean_dec(v_a_1874_);
v___x_1881_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1864_, v_info_1865_, v_fst_1880_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec_ref(v_info_1865_);
return v___x_1881_;
}
else
{
lean_object* v_fst_1882_; lean_object* v___x_1884_; 
lean_dec_ref(v_info_1865_);
lean_dec(v_x_1864_);
v_fst_1882_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_fst_1882_);
lean_dec(v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_fst_1882_);
v___x_1884_ = v___x_1876_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_fst_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_info_1865_);
lean_dec(v_x_1864_);
v_a_1887_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1873_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1873_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object* v_x_1895_, lean_object* v_info_1896_, lean_object* v_i_1897_, lean_object* v_as_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1895_, v_info_1896_, v_i_1897_, v_as_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object* v_x_1906_, lean_object* v_info_1907_, lean_object* v_c_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1906_, v_info_1907_, v_c_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec_ref(v_a_1909_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t v_pu_1916_, lean_object* v_alt_1917_, lean_object* v_f_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1917_, v_f_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object* v_pu_1926_, lean_object* v_alt_1927_, lean_object* v_f_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v_pu_boxed_1935_; lean_object* v_res_1936_; 
v_pu_boxed_1935_ = lean_unbox(v_pu_1926_);
v_res_1936_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_boxed_1935_, v_alt_1927_, v_f_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_toApplicative_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1980_; 
v___x_1944_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_1945_ = l_StateRefT_x27_instMonad___redArg(v___x_1944_);
v_toApplicative_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v___x_1945_, 1);
lean_dec(v_unused_1981_);
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1980_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_toApplicative_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1980_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_toFunctor_1950_; lean_object* v_toSeq_1951_; lean_object* v_toSeqLeft_1952_; lean_object* v_toSeqRight_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1978_; 
v_toFunctor_1950_ = lean_ctor_get(v_toApplicative_1946_, 0);
v_toSeq_1951_ = lean_ctor_get(v_toApplicative_1946_, 2);
v_toSeqLeft_1952_ = lean_ctor_get(v_toApplicative_1946_, 3);
v_toSeqRight_1953_ = lean_ctor_get(v_toApplicative_1946_, 4);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_toApplicative_1946_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v_toApplicative_1946_, 1);
lean_dec(v_unused_1979_);
v___x_1955_ = v_toApplicative_1946_;
v_isShared_1956_ = v_isSharedCheck_1978_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_toSeqRight_1953_);
lean_inc(v_toSeqLeft_1952_);
lean_inc(v_toSeq_1951_);
lean_inc(v_toFunctor_1950_);
lean_dec(v_toApplicative_1946_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1978_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___f_1957_; lean_object* v___f_1958_; lean_object* v___f_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1966_; 
v___f_1957_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_1958_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1950_);
v___f_1959_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1959_, 0, v_toFunctor_1950_);
v___f_1960_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1960_, 0, v_toFunctor_1950_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___f_1959_);
lean_ctor_set(v___x_1961_, 1, v___f_1960_);
v___f_1962_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1962_, 0, v_toSeqRight_1953_);
v___f_1963_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1963_, 0, v_toSeqLeft_1952_);
v___f_1964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1964_, 0, v_toSeq_1951_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 4, v___f_1962_);
lean_ctor_set(v___x_1955_, 3, v___f_1963_);
lean_ctor_set(v___x_1955_, 2, v___f_1964_);
lean_ctor_set(v___x_1955_, 1, v___f_1957_);
lean_ctor_set(v___x_1955_, 0, v___x_1961_);
v___x_1966_ = v___x_1955_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___f_1957_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v___f_1964_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v___f_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v___f_1962_);
v___x_1966_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___f_1958_);
lean_ctor_set(v___x_1948_, 0, v___x_1966_);
v___x_1968_ = v___x_1948_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___f_1958_);
v___x_1968_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___x_5620__overap_1974_; lean_object* v___x_1975_; 
v___x_1969_ = l_StateRefT_x27_instMonad___redArg(v___x_1968_);
v___x_1970_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_1971_ = l_instInhabitedOfMonad___redArg(v___x_1969_, v___x_1970_);
v___f_1972_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1972_, 0, v___x_1971_);
v___f_1973_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1973_, 0, v___f_1972_);
v___x_5620__overap_1974_ = lean_panic_fn_borrowed(v___f_1973_, v_msg_1937_);
lean_dec_ref(v___f_1973_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc_ref(v___y_1938_);
v___x_1975_ = lean_apply_6(v___x_5620__overap_1974_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, lean_box(0));
return v___x_1975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object* v_msg_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object* v_a_1990_, lean_object* v_fallback_1991_, lean_object* v_x_1992_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_inc(v_fallback_1991_);
return v_fallback_1991_;
}
else
{
lean_object* v_key_1993_; lean_object* v_value_1994_; lean_object* v_tail_1995_; uint8_t v___x_1996_; 
v_key_1993_ = lean_ctor_get(v_x_1992_, 0);
v_value_1994_ = lean_ctor_get(v_x_1992_, 1);
v_tail_1995_ = lean_ctor_get(v_x_1992_, 2);
v___x_1996_ = l_Lean_instBEqFVarId_beq(v_key_1993_, v_a_1990_);
if (v___x_1996_ == 0)
{
v_x_1992_ = v_tail_1995_;
goto _start;
}
else
{
lean_inc(v_value_1994_);
return v_value_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object* v_a_1998_, lean_object* v_fallback_1999_, lean_object* v_x_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_1998_, v_fallback_1999_, v_x_2000_);
lean_dec(v_x_2000_);
lean_dec(v_fallback_1999_);
lean_dec(v_a_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object* v_m_2002_, lean_object* v_a_2003_, lean_object* v_fallback_2004_){
_start:
{
lean_object* v_buckets_2005_; lean_object* v___x_2006_; uint64_t v___x_2007_; uint64_t v___x_2008_; uint64_t v___x_2009_; uint64_t v_fold_2010_; uint64_t v___x_2011_; uint64_t v___x_2012_; uint64_t v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_buckets_2005_ = lean_ctor_get(v_m_2002_, 1);
v___x_2006_ = lean_array_get_size(v_buckets_2005_);
v___x_2007_ = l_Lean_instHashableFVarId_hash(v_a_2003_);
v___x_2008_ = 32ULL;
v___x_2009_ = lean_uint64_shift_right(v___x_2007_, v___x_2008_);
v_fold_2010_ = lean_uint64_xor(v___x_2007_, v___x_2009_);
v___x_2011_ = 16ULL;
v___x_2012_ = lean_uint64_shift_right(v_fold_2010_, v___x_2011_);
v___x_2013_ = lean_uint64_xor(v_fold_2010_, v___x_2012_);
v___x_2014_ = lean_uint64_to_usize(v___x_2013_);
v___x_2015_ = lean_usize_of_nat(v___x_2006_);
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_sub(v___x_2015_, v___x_2016_);
v___x_2018_ = lean_usize_land(v___x_2014_, v___x_2017_);
v___x_2019_ = lean_array_uget_borrowed(v_buckets_2005_, v___x_2018_);
v___x_2020_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2003_, v_fallback_2004_, v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object* v_m_2021_, lean_object* v_a_2022_, lean_object* v_fallback_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2021_, v_a_2022_, v_fallback_2023_);
lean_dec(v_fallback_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_m_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v_ks_2029_; lean_object* v_vs_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2054_; 
v_ks_2029_ = lean_ctor_get(v_x_2025_, 0);
v_vs_2030_ = lean_ctor_get(v_x_2025_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_x_2025_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2032_ = v_x_2025_;
v_isShared_2033_ = v_isSharedCheck_2054_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_vs_2030_);
lean_inc(v_ks_2029_);
lean_dec(v_x_2025_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2054_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = lean_array_get_size(v_ks_2029_);
v___x_2035_ = lean_nat_dec_lt(v_x_2026_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_x_2026_);
v___x_2036_ = lean_array_push(v_ks_2029_, v_x_2027_);
v___x_2037_ = lean_array_push(v_vs_2030_, v_x_2028_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v___x_2037_);
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2039_ = v___x_2032_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
else
{
lean_object* v_k_x27_2041_; uint8_t v___x_2042_; 
v_k_x27_2041_ = lean_array_fget_borrowed(v_ks_2029_, v_x_2026_);
v___x_2042_ = l_Lean_instBEqFVarId_beq(v_x_2027_, v_k_x27_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2044_; 
if (v_isShared_2033_ == 0)
{
v___x_2044_ = v___x_2032_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_ks_2029_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_vs_2030_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_add(v_x_2026_, v___x_2045_);
lean_dec(v_x_2026_);
v_x_2025_ = v___x_2044_;
v_x_2026_ = v___x_2046_;
goto _start;
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2049_ = lean_array_fset(v_ks_2029_, v_x_2026_, v_x_2027_);
v___x_2050_ = lean_array_fset(v_vs_2030_, v_x_2026_, v_x_2028_);
lean_dec(v_x_2026_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v___x_2050_);
lean_ctor_set(v___x_2032_, 0, v___x_2049_);
v___x_2052_ = v___x_2032_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object* v_n_2055_, lean_object* v_k_2056_, lean_object* v_v_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_n_2055_, v___x_2058_, v_k_2056_, v_v_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object* v_x_2061_, size_t v_x_2062_, size_t v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v_es_2066_; size_t v___x_2067_; size_t v___x_2068_; lean_object* v_j_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_es_2066_ = lean_ctor_get(v_x_2061_, 0);
v___x_2067_ = ((size_t)31ULL);
v___x_2068_ = lean_usize_land(v_x_2062_, v___x_2067_);
v_j_2069_ = lean_usize_to_nat(v___x_2068_);
v___x_2070_ = lean_array_get_size(v_es_2066_);
v___x_2071_ = lean_nat_dec_lt(v_j_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v_j_2069_);
lean_dec(v_x_2065_);
lean_dec(v_x_2064_);
return v_x_2061_;
}
else
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2110_; 
lean_inc_ref(v_es_2066_);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_x_2061_, 0);
lean_dec(v_unused_2111_);
v___x_2073_ = v_x_2061_;
v_isShared_2074_ = v_isSharedCheck_2110_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v_x_2061_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2110_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_v_2075_; lean_object* v___x_2076_; lean_object* v_xs_x27_2077_; lean_object* v___y_2079_; 
v_v_2075_ = lean_array_fget(v_es_2066_, v_j_2069_);
v___x_2076_ = lean_box(0);
v_xs_x27_2077_ = lean_array_fset(v_es_2066_, v_j_2069_, v___x_2076_);
switch(lean_obj_tag(v_v_2075_))
{
case 0:
{
lean_object* v_key_2084_; lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2095_; 
v_key_2084_ = lean_ctor_get(v_v_2075_, 0);
v_val_2085_ = lean_ctor_get(v_v_2075_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_v_2075_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2087_ = v_v_2075_;
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_inc(v_key_2084_);
lean_dec(v_v_2075_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_instBEqFVarId_beq(v_x_2064_, v_key_2084_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2087_);
v___x_2090_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2084_, v_val_2085_, v_x_2064_, v_x_2065_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___y_2079_ = v___x_2091_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_val_2085_);
lean_dec(v_key_2084_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v_x_2065_);
lean_ctor_set(v___x_2087_, 0, v_x_2064_);
v___x_2093_ = v___x_2087_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_x_2064_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_x_2065_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v___y_2079_ = v___x_2093_;
goto v___jp_2078_;
}
}
}
}
case 1:
{
lean_object* v_node_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2108_; 
v_node_2096_ = lean_ctor_get(v_v_2075_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_v_2075_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2098_ = v_v_2075_;
v_isShared_2099_ = v_isSharedCheck_2108_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_node_2096_);
lean_dec(v_v_2075_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2108_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2100_ = ((size_t)5ULL);
v___x_2101_ = lean_usize_shift_right(v_x_2062_, v___x_2100_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_x_2063_, v___x_2102_);
v___x_2104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_2096_, v___x_2101_, v___x_2103_, v_x_2064_, v_x_2065_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2104_);
v___x_2106_ = v___x_2098_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
v___y_2079_ = v___x_2106_;
goto v___jp_2078_;
}
}
}
default: 
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_x_2064_);
lean_ctor_set(v___x_2109_, 1, v_x_2065_);
v___y_2079_ = v___x_2109_;
goto v___jp_2078_;
}
}
v___jp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_array_fset(v_xs_x27_2077_, v_j_2069_, v___y_2079_);
lean_dec(v_j_2069_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2080_);
v___x_2082_ = v___x_2073_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_ks_2112_; lean_object* v_vs_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2133_; 
v_ks_2112_ = lean_ctor_get(v_x_2061_, 0);
v_vs_2113_ = lean_ctor_get(v_x_2061_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2115_ = v_x_2061_;
v_isShared_2116_ = v_isSharedCheck_2133_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_vs_2113_);
lean_inc(v_ks_2112_);
lean_dec(v_x_2061_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2133_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_ks_2112_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_vs_2113_);
v___x_2118_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v_newNode_2119_; uint8_t v___y_2121_; size_t v___x_2127_; uint8_t v___x_2128_; 
v_newNode_2119_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_2118_, v_x_2064_, v_x_2065_);
v___x_2127_ = ((size_t)7ULL);
v___x_2128_ = lean_usize_dec_le(v___x_2127_, v_x_2063_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2129_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2119_);
v___x_2130_ = lean_unsigned_to_nat(4u);
v___x_2131_ = lean_nat_dec_lt(v___x_2129_, v___x_2130_);
lean_dec(v___x_2129_);
v___y_2121_ = v___x_2131_;
goto v___jp_2120_;
}
else
{
v___y_2121_ = v___x_2128_;
goto v___jp_2120_;
}
v___jp_2120_:
{
if (v___y_2121_ == 0)
{
lean_object* v_ks_2122_; lean_object* v_vs_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_ks_2122_ = lean_ctor_get(v_newNode_2119_, 0);
lean_inc_ref(v_ks_2122_);
v_vs_2123_ = lean_ctor_get(v_newNode_2119_, 1);
lean_inc_ref(v_vs_2123_);
lean_dec_ref(v_newNode_2119_);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_2063_, v_ks_2122_, v_vs_2123_, v___x_2124_, v___x_2125_);
lean_dec_ref(v_vs_2123_);
lean_dec_ref(v_ks_2122_);
return v___x_2126_;
}
else
{
return v_newNode_2119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t v_depth_2134_, lean_object* v_keys_2135_, lean_object* v_vals_2136_, lean_object* v_i_2137_, lean_object* v_entries_2138_){
_start:
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = lean_array_get_size(v_keys_2135_);
v___x_2140_ = lean_nat_dec_lt(v_i_2137_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec(v_i_2137_);
return v_entries_2138_;
}
else
{
lean_object* v_k_2141_; lean_object* v_v_2142_; uint64_t v___x_2143_; size_t v_h_2144_; size_t v___x_2145_; lean_object* v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; size_t v_h_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_k_2141_ = lean_array_fget_borrowed(v_keys_2135_, v_i_2137_);
v_v_2142_ = lean_array_fget_borrowed(v_vals_2136_, v_i_2137_);
v___x_2143_ = l_Lean_instHashableFVarId_hash(v_k_2141_);
v_h_2144_ = lean_uint64_to_usize(v___x_2143_);
v___x_2145_ = ((size_t)5ULL);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_sub(v_depth_2134_, v___x_2147_);
v___x_2149_ = lean_usize_mul(v___x_2145_, v___x_2148_);
v_h_2150_ = lean_usize_shift_right(v_h_2144_, v___x_2149_);
v___x_2151_ = lean_nat_add(v_i_2137_, v___x_2146_);
lean_dec(v_i_2137_);
lean_inc(v_v_2142_);
lean_inc(v_k_2141_);
v___x_2152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2138_, v_h_2150_, v_depth_2134_, v_k_2141_, v_v_2142_);
v_i_2137_ = v___x_2151_;
v_entries_2138_ = v___x_2152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_2154_, lean_object* v_keys_2155_, lean_object* v_vals_2156_, lean_object* v_i_2157_, lean_object* v_entries_2158_){
_start:
{
size_t v_depth_boxed_2159_; lean_object* v_res_2160_; 
v_depth_boxed_2159_ = lean_unbox_usize(v_depth_2154_);
lean_dec(v_depth_2154_);
v_res_2160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2159_, v_keys_2155_, v_vals_2156_, v_i_2157_, v_entries_2158_);
lean_dec_ref(v_vals_2156_);
lean_dec_ref(v_keys_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
size_t v_x_6230__boxed_2166_; size_t v_x_6231__boxed_2167_; lean_object* v_res_2168_; 
v_x_6230__boxed_2166_ = lean_unbox_usize(v_x_2162_);
lean_dec(v_x_2162_);
v_x_6231__boxed_2167_ = lean_unbox_usize(v_x_2163_);
lean_dec(v_x_2163_);
v_res_2168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2161_, v_x_6230__boxed_2166_, v_x_6231__boxed_2167_, v_x_2164_, v_x_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_){
_start:
{
uint64_t v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2172_ = l_Lean_instHashableFVarId_hash(v_x_2170_);
v___x_2173_ = lean_uint64_to_usize(v___x_2172_);
v___x_2174_ = ((size_t)1ULL);
v___x_2175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2169_, v___x_2173_, v___x_2174_, v_x_2170_, v_x_2171_);
return v___x_2175_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2176_, lean_object* v_i_2177_, lean_object* v_k_2178_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_array_get_size(v_keys_2176_);
v___x_2180_ = lean_nat_dec_lt(v_i_2177_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec(v_i_2177_);
return v___x_2180_;
}
else
{
lean_object* v_k_x27_2181_; uint8_t v___x_2182_; 
v_k_x27_2181_ = lean_array_fget_borrowed(v_keys_2176_, v_i_2177_);
v___x_2182_ = l_Lean_instBEqFVarId_beq(v_k_2178_, v_k_x27_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_add(v_i_2177_, v___x_2183_);
lean_dec(v_i_2177_);
v_i_2177_ = v___x_2184_;
goto _start;
}
else
{
lean_dec(v_i_2177_);
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2186_, lean_object* v_i_2187_, lean_object* v_k_2188_){
_start:
{
uint8_t v_res_2189_; lean_object* v_r_2190_; 
v_res_2189_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2186_, v_i_2187_, v_k_2188_);
lean_dec(v_k_2188_);
lean_dec_ref(v_keys_2186_);
v_r_2190_ = lean_box(v_res_2189_);
return v_r_2190_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2191_, size_t v_x_2192_, lean_object* v_x_2193_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
lean_object* v_es_2194_; lean_object* v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; lean_object* v_j_2198_; lean_object* v___x_2199_; 
v_es_2194_ = lean_ctor_get(v_x_2191_, 0);
v___x_2195_ = lean_box(2);
v___x_2196_ = ((size_t)31ULL);
v___x_2197_ = lean_usize_land(v_x_2192_, v___x_2196_);
v_j_2198_ = lean_usize_to_nat(v___x_2197_);
v___x_2199_ = lean_array_get_borrowed(v___x_2195_, v_es_2194_, v_j_2198_);
lean_dec(v_j_2198_);
switch(lean_obj_tag(v___x_2199_))
{
case 0:
{
lean_object* v_key_2200_; uint8_t v___x_2201_; 
v_key_2200_ = lean_ctor_get(v___x_2199_, 0);
v___x_2201_ = l_Lean_instBEqFVarId_beq(v_x_2193_, v_key_2200_);
return v___x_2201_;
}
case 1:
{
lean_object* v_node_2202_; size_t v___x_2203_; size_t v___x_2204_; 
v_node_2202_ = lean_ctor_get(v___x_2199_, 0);
v___x_2203_ = ((size_t)5ULL);
v___x_2204_ = lean_usize_shift_right(v_x_2192_, v___x_2203_);
v_x_2191_ = v_node_2202_;
v_x_2192_ = v___x_2204_;
goto _start;
}
default: 
{
uint8_t v___x_2206_; 
v___x_2206_ = 0;
return v___x_2206_;
}
}
}
else
{
lean_object* v_ks_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_ks_2207_ = lean_ctor_get(v_x_2191_, 0);
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2207_, v___x_2208_, v_x_2193_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
size_t v_x_6412__boxed_2213_; uint8_t v_res_2214_; lean_object* v_r_2215_; 
v_x_6412__boxed_2213_ = lean_unbox_usize(v_x_2211_);
lean_dec(v_x_2211_);
v_res_2214_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2210_, v_x_6412__boxed_2213_, v_x_2212_);
lean_dec(v_x_2212_);
lean_dec_ref(v_x_2210_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
uint64_t v___x_2218_; size_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2218_ = l_Lean_instHashableFVarId_hash(v_x_2217_);
v___x_2219_ = lean_uint64_to_usize(v___x_2218_);
v___x_2220_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2216_, v___x_2219_, v_x_2217_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_res_2223_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2221_, v_x_2222_);
lean_dec(v_x_2222_);
lean_dec_ref(v_x_2221_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2227_ = lean_unsigned_to_nat(59u);
v___x_2228_ = lean_unsigned_to_nat(281u);
v___x_2229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2230_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2231_ = l_mkPanicMessageWithDecl(v___x_2230_, v___x_2229_, v___x_2228_, v___x_2227_, v___x_2226_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
switch(lean_obj_tag(v_c_2232_))
{
case 0:
{
lean_object* v_decl_2239_; lean_object* v_k_2240_; lean_object* v___x_2241_; 
v_decl_2239_ = lean_ctor_get(v_c_2232_, 0);
v_k_2240_ = lean_ctor_get(v_c_2232_, 1);
lean_inc_ref(v_k_2240_);
v___x_2241_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2240_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2264_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2264_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2264_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
size_t v___x_2246_; size_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2246_ = lean_ptr_addr(v_k_2240_);
v___x_2247_ = lean_ptr_addr(v_a_2242_);
v___x_2248_ = lean_usize_dec_eq(v___x_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2258_; 
lean_inc_ref(v_decl_2239_);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_c_2232_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; lean_object* v_unused_2260_; 
v_unused_2259_ = lean_ctor_get(v_c_2232_, 1);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_c_2232_, 0);
lean_dec(v_unused_2260_);
v___x_2250_ = v_c_2232_;
v_isShared_2251_ = v_isSharedCheck_2258_;
goto v_resetjp_2249_;
}
else
{
lean_dec(v_c_2232_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2258_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_a_2242_);
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_decl_2239_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_a_2242_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2253_);
v___x_2255_ = v___x_2244_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_object* v___x_2262_; 
lean_dec(v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v_c_2232_);
v___x_2262_ = v___x_2244_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_c_2232_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2232_, 2);
return v___x_2241_;
}
}
case 2:
{
lean_object* v_decl_2265_; lean_object* v_k_2266_; lean_object* v_params_2267_; lean_object* v_type_2268_; lean_object* v_value_2269_; lean_object* v___x_2270_; 
v_decl_2265_ = lean_ctor_get(v_c_2232_, 0);
v_k_2266_ = lean_ctor_get(v_c_2232_, 1);
v_params_2267_ = lean_ctor_get(v_decl_2265_, 2);
v_type_2268_ = lean_ctor_get(v_decl_2265_, 3);
v_value_2269_ = lean_ctor_get(v_decl_2265_, 4);
lean_inc_ref(v_value_2269_);
v___x_2270_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2269_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = 1;
lean_inc_ref(v_params_2267_);
lean_inc_ref(v_type_2268_);
lean_inc_ref(v_decl_2265_);
v___x_2273_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2272_, v_decl_2265_, v_type_2268_, v_params_2267_, v_a_2271_, v_a_2235_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
lean_inc_ref(v_k_2266_);
v___x_2275_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2266_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2303_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2303_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2303_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
uint8_t v___y_2281_; size_t v___x_2297_; size_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = lean_ptr_addr(v_k_2266_);
v___x_2298_ = lean_ptr_addr(v_a_2276_);
v___x_2299_ = lean_usize_dec_eq(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
v___y_2281_ = v___x_2299_;
goto v___jp_2280_;
}
else
{
size_t v___x_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = lean_ptr_addr(v_decl_2265_);
v___x_2301_ = lean_ptr_addr(v_a_2274_);
v___x_2302_ = lean_usize_dec_eq(v___x_2300_, v___x_2301_);
v___y_2281_ = v___x_2302_;
goto v___jp_2280_;
}
v___jp_2280_:
{
if (v___y_2281_ == 0)
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2291_; 
v_isSharedCheck_2291_ = !lean_is_exclusive(v_c_2232_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; lean_object* v_unused_2293_; 
v_unused_2292_ = lean_ctor_get(v_c_2232_, 1);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_c_2232_, 0);
lean_dec(v_unused_2293_);
v___x_2283_ = v_c_2232_;
v_isShared_2284_ = v_isSharedCheck_2291_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v_c_2232_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2291_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v_a_2276_);
lean_ctor_set(v___x_2283_, 0, v_a_2274_);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2274_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_a_2276_);
v___x_2286_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2286_);
v___x_2288_ = v___x_2278_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v___x_2295_; 
lean_dec(v_a_2276_);
lean_dec(v_a_2274_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v_c_2232_);
v___x_2295_ = v___x_2278_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_c_2232_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
else
{
lean_dec(v_a_2274_);
lean_dec_ref_known(v_c_2232_, 2);
return v___x_2275_;
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref_known(v_c_2232_, 2);
v_a_2304_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2273_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2273_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2232_, 2);
return v___x_2270_;
}
}
case 3:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v_c_2232_);
return v___x_2312_;
}
case 4:
{
lean_object* v_cases_2313_; lean_object* v_typeName_2314_; lean_object* v_resultType_2315_; lean_object* v_discr_2316_; lean_object* v_alts_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2370_; 
v_cases_2313_ = lean_ctor_get(v_c_2232_, 0);
lean_inc_ref(v_cases_2313_);
v_typeName_2314_ = lean_ctor_get(v_cases_2313_, 0);
v_resultType_2315_ = lean_ctor_get(v_cases_2313_, 1);
v_discr_2316_ = lean_ctor_get(v_cases_2313_, 2);
v_alts_2317_ = lean_ctor_get(v_cases_2313_, 3);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_cases_2313_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2319_ = v_cases_2313_;
v_isShared_2320_ = v_isSharedCheck_2370_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_alts_2317_);
lean_inc(v_discr_2316_);
lean_inc(v_resultType_2315_);
lean_inc(v_typeName_2314_);
lean_dec(v_cases_2313_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2370_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_alreadyFound_2321_; uint8_t v_relaxedReuse_2322_; lean_object* v_ownedness_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; uint8_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; size_t v_sz_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v_alreadyFound_2321_ = lean_ctor_get(v_a_2233_, 0);
v_relaxedReuse_2322_ = lean_ctor_get_uint8(v_a_2233_, sizeof(void*)*2);
v_ownedness_2323_ = lean_ctor_get(v_a_2233_, 1);
v___x_2324_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2321_, v_discr_2316_);
v___x_2325_ = 0;
v___x_2326_ = lean_box(v___x_2325_);
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2323_, v_discr_2316_, v___x_2326_);
lean_dec(v___x_2326_);
v___x_2328_ = 1;
v___x_2329_ = lean_unbox(v___x_2327_);
lean_dec(v___x_2327_);
v___x_2330_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2329_, v___x_2328_);
v___x_2331_ = lean_box(0);
lean_inc_n(v_discr_2316_, 2);
lean_inc_ref(v_alreadyFound_2321_);
v___x_2332_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2321_, v_discr_2316_, v___x_2331_);
lean_inc_ref(v_ownedness_2323_);
v___x_2333_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v_ownedness_2323_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*2, v_relaxedReuse_2322_);
v_sz_2334_ = lean_array_size(v_alts_2317_);
v___x_2335_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2317_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2330_, v_discr_2316_, v___x_2324_, v_sz_2334_, v___x_2335_, v_alts_2317_, v___x_2333_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec_ref_known(v___x_2333_, 2);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2361_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2361_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2361_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
size_t v___x_2341_; size_t v___x_2342_; uint8_t v___x_2343_; 
v___x_2341_ = lean_ptr_addr(v_alts_2317_);
lean_dec_ref(v_alts_2317_);
v___x_2342_ = lean_ptr_addr(v_a_2337_);
v___x_2343_ = lean_usize_dec_eq(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2356_; 
v_isSharedCheck_2356_ = !lean_is_exclusive(v_c_2232_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v_c_2232_, 0);
lean_dec(v_unused_2357_);
v___x_2345_ = v_c_2232_;
v_isShared_2346_ = v_isSharedCheck_2356_;
goto v_resetjp_2344_;
}
else
{
lean_dec(v_c_2232_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2356_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 3, v_a_2337_);
v___x_2348_ = v___x_2319_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_typeName_2314_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_resultType_2315_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_discr_2316_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_a_2337_);
v___x_2348_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2348_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2350_);
v___x_2352_ = v___x_2339_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
else
{
lean_object* v___x_2359_; 
lean_dec(v_a_2337_);
lean_del_object(v___x_2319_);
lean_dec(v_discr_2316_);
lean_dec_ref(v_resultType_2315_);
lean_dec(v_typeName_2314_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v_c_2232_);
v___x_2359_ = v___x_2339_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_c_2232_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_del_object(v___x_2319_);
lean_dec_ref(v_alts_2317_);
lean_dec(v_discr_2316_);
lean_dec_ref(v_resultType_2315_);
lean_dec(v_typeName_2314_);
lean_dec_ref_known(v_c_2232_, 1);
v_a_2362_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2336_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2336_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
case 5:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v_c_2232_);
return v___x_2371_;
}
case 6:
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_c_2232_);
return v___x_2372_;
}
case 8:
{
lean_object* v_fvarId_2373_; lean_object* v_i_2374_; lean_object* v_y_2375_; lean_object* v_k_2376_; lean_object* v___x_2377_; 
v_fvarId_2373_ = lean_ctor_get(v_c_2232_, 0);
v_i_2374_ = lean_ctor_get(v_c_2232_, 1);
v_y_2375_ = lean_ctor_get(v_c_2232_, 2);
v_k_2376_ = lean_ctor_get(v_c_2232_, 3);
lean_inc_ref(v_k_2376_);
v___x_2377_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2376_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2402_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2402_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2402_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
size_t v___x_2382_; size_t v___x_2383_; uint8_t v___x_2384_; 
v___x_2382_ = lean_ptr_addr(v_k_2376_);
v___x_2383_ = lean_ptr_addr(v_a_2378_);
v___x_2384_ = lean_usize_dec_eq(v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2394_; 
lean_inc(v_y_2375_);
lean_inc(v_i_2374_);
lean_inc(v_fvarId_2373_);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_c_2232_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; 
v_unused_2395_ = lean_ctor_get(v_c_2232_, 3);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_c_2232_, 2);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_c_2232_, 1);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_c_2232_, 0);
lean_dec(v_unused_2398_);
v___x_2386_ = v_c_2232_;
v_isShared_2387_ = v_isSharedCheck_2394_;
goto v_resetjp_2385_;
}
else
{
lean_dec(v_c_2232_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2394_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 3, v_a_2378_);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_fvarId_2373_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_i_2374_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_y_2375_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_a_2378_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2389_);
v___x_2391_ = v___x_2380_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v___x_2400_; 
lean_dec(v_a_2378_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v_c_2232_);
v___x_2400_ = v___x_2380_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_c_2232_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2232_, 4);
return v___x_2377_;
}
}
case 9:
{
lean_object* v_fvarId_2403_; lean_object* v_i_2404_; lean_object* v_offset_2405_; lean_object* v_y_2406_; lean_object* v_ty_2407_; lean_object* v_k_2408_; lean_object* v___x_2409_; 
v_fvarId_2403_ = lean_ctor_get(v_c_2232_, 0);
v_i_2404_ = lean_ctor_get(v_c_2232_, 1);
v_offset_2405_ = lean_ctor_get(v_c_2232_, 2);
v_y_2406_ = lean_ctor_get(v_c_2232_, 3);
v_ty_2407_ = lean_ctor_get(v_c_2232_, 4);
v_k_2408_ = lean_ctor_get(v_c_2232_, 5);
lean_inc_ref(v_k_2408_);
v___x_2409_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2408_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2436_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2436_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2436_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
size_t v___x_2414_; size_t v___x_2415_; uint8_t v___x_2416_; 
v___x_2414_ = lean_ptr_addr(v_k_2408_);
v___x_2415_ = lean_ptr_addr(v_a_2410_);
v___x_2416_ = lean_usize_dec_eq(v___x_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2426_; 
lean_inc_ref(v_ty_2407_);
lean_inc(v_y_2406_);
lean_inc(v_offset_2405_);
lean_inc(v_i_2404_);
lean_inc(v_fvarId_2403_);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_c_2232_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; 
v_unused_2427_ = lean_ctor_get(v_c_2232_, 5);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_c_2232_, 4);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_c_2232_, 3);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_c_2232_, 2);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_c_2232_, 1);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_c_2232_, 0);
lean_dec(v_unused_2432_);
v___x_2418_ = v_c_2232_;
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v_c_2232_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 5, v_a_2410_);
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_fvarId_2403_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_i_2404_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_offset_2405_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_y_2406_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v_ty_2407_);
lean_ctor_set(v_reuseFailAlloc_2425_, 5, v_a_2410_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2421_);
v___x_2423_ = v___x_2412_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_object* v___x_2434_; 
lean_dec(v_a_2410_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v_c_2232_);
v___x_2434_ = v___x_2412_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_c_2232_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2232_, 6);
return v___x_2409_;
}
}
default: 
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec_ref(v_c_2232_);
v___x_2437_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2438_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2437_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
return v___x_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2447_, lean_object* v_discr_2448_, uint8_t v___x_2449_, size_t v_sz_2450_, size_t v_i_2451_, lean_object* v_bs_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_usize_dec_lt(v_i_2451_, v_sz_2450_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
lean_dec(v_discr_2448_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_bs_2452_);
return v___x_2460_;
}
else
{
lean_object* v___f_2461_; lean_object* v_v_2462_; lean_object* v___x_2463_; lean_object* v_bs_x27_2464_; lean_object* v_a_2466_; lean_object* v___y_2472_; lean_object* v___x_2482_; 
v___f_2461_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2462_ = lean_array_uget(v_bs_2452_, v_i_2451_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v_bs_x27_2464_ = lean_array_uset(v_bs_2452_, v_i_2451_, v___x_2463_);
v___x_2482_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2462_, v___f_2461_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
if (lean_obj_tag(v_a_2483_) == 1)
{
lean_object* v_info_2484_; lean_object* v_code_2485_; uint8_t v___y_2487_; uint8_t v___x_2499_; 
v_info_2484_ = lean_ctor_get(v_a_2483_, 0);
v_code_2485_ = lean_ctor_get(v_a_2483_, 1);
v___x_2499_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2484_);
if (v___x_2499_ == 0)
{
v___y_2487_ = v___x_2449_;
goto v___jp_2486_;
}
else
{
v___y_2487_ = v___x_2499_;
goto v___jp_2486_;
}
v___jp_2486_:
{
if (v___y_2487_ == 0)
{
if (v___x_2447_ == 0)
{
lean_object* v___x_2488_; 
lean_dec_ref_known(v___x_2482_, 1);
lean_inc_ref(v_code_2485_);
lean_inc_ref(v_info_2484_);
lean_inc(v_discr_2448_);
v___x_2488_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2448_, v_info_2484_, v_code_2485_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2483_, v_a_2489_);
v_a_2466_ = v___x_2490_;
goto v___jp_2465_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref_known(v_a_2483_, 2);
lean_dec_ref(v_bs_x27_2464_);
lean_dec(v_discr_2448_);
v_a_2491_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2488_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2488_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2483_, 2);
v___y_2472_ = v___x_2482_;
goto v___jp_2471_;
}
}
else
{
lean_dec_ref_known(v_a_2483_, 2);
v___y_2472_ = v___x_2482_;
goto v___jp_2471_;
}
}
}
else
{
lean_dec_ref_known(v_a_2483_, 1);
v___y_2472_ = v___x_2482_;
goto v___jp_2471_;
}
}
else
{
v___y_2472_ = v___x_2482_;
goto v___jp_2471_;
}
v___jp_2465_:
{
size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = ((size_t)1ULL);
v___x_2468_ = lean_usize_add(v_i_2451_, v___x_2467_);
v___x_2469_ = lean_array_uset(v_bs_x27_2464_, v_i_2451_, v_a_2466_);
v_i_2451_ = v___x_2468_;
v_bs_2452_ = v___x_2469_;
goto _start;
}
v___jp_2471_:
{
if (lean_obj_tag(v___y_2472_) == 0)
{
lean_object* v_a_2473_; 
v_a_2473_ = lean_ctor_get(v___y_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___y_2472_, 1);
v_a_2466_ = v_a_2473_;
goto v___jp_2465_;
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_bs_x27_2464_);
lean_dec(v_discr_2448_);
v_a_2474_ = lean_ctor_get(v___y_2472_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___y_2472_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___y_2472_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___y_2472_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2500_, lean_object* v_discr_2501_, lean_object* v___x_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_bs_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v___x_6473__boxed_2512_; uint8_t v___x_6475__boxed_2513_; size_t v_sz_boxed_2514_; size_t v_i_boxed_2515_; lean_object* v_res_2516_; 
v___x_6473__boxed_2512_ = lean_unbox(v___x_2500_);
v___x_6475__boxed_2513_ = lean_unbox(v___x_2502_);
v_sz_boxed_2514_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2515_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6473__boxed_2512_, v_discr_2501_, v___x_6475__boxed_2513_, v_sz_boxed_2514_, v_i_boxed_2515_, v_bs_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2518_, v_x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
uint8_t v_res_2524_; lean_object* v_r_2525_; 
v_res_2524_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2521_, v_x_2522_, v_x_2523_);
lean_dec(v_x_2523_);
lean_dec_ref(v_x_2522_);
v_r_2525_ = lean_box(v_res_2524_);
return v_r_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2526_, lean_object* v_m_2527_, lean_object* v_a_2528_, lean_object* v_fallback_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2527_, v_a_2528_, v_fallback_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2531_, lean_object* v_m_2532_, lean_object* v_a_2533_, lean_object* v_fallback_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2531_, v_m_2532_, v_a_2533_, v_fallback_2534_);
lean_dec(v_fallback_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_m_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2537_, v_x_2538_, v_x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2541_, lean_object* v_x_2542_, size_t v_x_2543_, lean_object* v_x_2544_){
_start:
{
uint8_t v___x_2545_; 
v___x_2545_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2542_, v_x_2543_, v_x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_){
_start:
{
size_t v_x_7024__boxed_2550_; uint8_t v_res_2551_; lean_object* v_r_2552_; 
v_x_7024__boxed_2550_ = lean_unbox_usize(v_x_2548_);
lean_dec(v_x_2548_);
v_res_2551_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2546_, v_x_2547_, v_x_7024__boxed_2550_, v_x_2549_);
lean_dec(v_x_2549_);
lean_dec_ref(v_x_2547_);
v_r_2552_ = lean_box(v_res_2551_);
return v_r_2552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2553_, lean_object* v_a_2554_, lean_object* v_fallback_2555_, lean_object* v_x_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2554_, v_fallback_2555_, v_x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2558_, lean_object* v_a_2559_, lean_object* v_fallback_2560_, lean_object* v_x_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2558_, v_a_2559_, v_fallback_2560_, v_x_2561_);
lean_dec(v_x_2561_);
lean_dec(v_fallback_2560_);
lean_dec(v_a_2559_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2563_, lean_object* v_x_2564_, size_t v_x_2565_, size_t v_x_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2564_, v_x_2565_, v_x_2566_, v_x_2567_, v_x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_){
_start:
{
size_t v_x_7040__boxed_2576_; size_t v_x_7041__boxed_2577_; lean_object* v_res_2578_; 
v_x_7040__boxed_2576_ = lean_unbox_usize(v_x_2572_);
lean_dec(v_x_2572_);
v_x_7041__boxed_2577_ = lean_unbox_usize(v_x_2573_);
lean_dec(v_x_2573_);
v_res_2578_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2570_, v_x_2571_, v_x_7040__boxed_2576_, v_x_7041__boxed_2577_, v_x_2574_, v_x_2575_);
return v_res_2578_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2579_, lean_object* v_keys_2580_, lean_object* v_vals_2581_, lean_object* v_heq_2582_, lean_object* v_i_2583_, lean_object* v_k_2584_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2580_, v_i_2583_, v_k_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2586_, lean_object* v_keys_2587_, lean_object* v_vals_2588_, lean_object* v_heq_2589_, lean_object* v_i_2590_, lean_object* v_k_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2586_, v_keys_2587_, v_vals_2588_, v_heq_2589_, v_i_2590_, v_k_2591_);
lean_dec(v_k_2591_);
lean_dec_ref(v_vals_2588_);
lean_dec_ref(v_keys_2587_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2594_, lean_object* v_n_2595_, lean_object* v_k_2596_, lean_object* v_v_2597_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_2595_, v_k_2596_, v_v_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2599_, size_t v_depth_2600_, lean_object* v_keys_2601_, lean_object* v_vals_2602_, lean_object* v_heq_2603_, lean_object* v_i_2604_, lean_object* v_entries_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2600_, v_keys_2601_, v_vals_2602_, v_i_2604_, v_entries_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2607_, lean_object* v_depth_2608_, lean_object* v_keys_2609_, lean_object* v_vals_2610_, lean_object* v_heq_2611_, lean_object* v_i_2612_, lean_object* v_entries_2613_){
_start:
{
size_t v_depth_boxed_2614_; lean_object* v_res_2615_; 
v_depth_boxed_2614_ = lean_unbox_usize(v_depth_2608_);
lean_dec(v_depth_2608_);
v_res_2615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_2607_, v_depth_boxed_2614_, v_keys_2609_, v_vals_2610_, v_heq_2611_, v_i_2612_, v_entries_2613_);
lean_dec_ref(v_vals_2610_);
lean_dec_ref(v_keys_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2617_, v_x_2618_, v_x_2619_, v_x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_toApplicative_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2695_; 
v___x_2631_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2632_ = l_StateRefT_x27_instMonad___redArg(v___x_2631_);
v_toApplicative_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2632_, 1);
lean_dec(v_unused_2696_);
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2695_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_toApplicative_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2695_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_toFunctor_2637_; lean_object* v_toSeq_2638_; lean_object* v_toSeqLeft_2639_; lean_object* v_toSeqRight_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2693_; 
v_toFunctor_2637_ = lean_ctor_get(v_toApplicative_2633_, 0);
v_toSeq_2638_ = lean_ctor_get(v_toApplicative_2633_, 2);
v_toSeqLeft_2639_ = lean_ctor_get(v_toApplicative_2633_, 3);
v_toSeqRight_2640_ = lean_ctor_get(v_toApplicative_2633_, 4);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_toApplicative_2633_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v_toApplicative_2633_, 1);
lean_dec(v_unused_2694_);
v___x_2642_ = v_toApplicative_2633_;
v_isShared_2643_ = v_isSharedCheck_2693_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_toSeqRight_2640_);
lean_inc(v_toSeqLeft_2639_);
lean_inc(v_toSeq_2638_);
lean_inc(v_toFunctor_2637_);
lean_dec(v_toApplicative_2633_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2693_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___f_2651_; lean_object* v___x_2653_; 
v___f_2644_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2645_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2637_);
v___f_2646_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2646_, 0, v_toFunctor_2637_);
v___f_2647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2647_, 0, v_toFunctor_2637_);
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___f_2646_);
lean_ctor_set(v___x_2648_, 1, v___f_2647_);
v___f_2649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2649_, 0, v_toSeqRight_2640_);
v___f_2650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2650_, 0, v_toSeqLeft_2639_);
v___f_2651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2651_, 0, v_toSeq_2638_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 4, v___f_2649_);
lean_ctor_set(v___x_2642_, 3, v___f_2650_);
lean_ctor_set(v___x_2642_, 2, v___f_2651_);
lean_ctor_set(v___x_2642_, 1, v___f_2644_);
lean_ctor_set(v___x_2642_, 0, v___x_2648_);
v___x_2653_ = v___x_2642_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___f_2644_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___f_2651_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v___f_2650_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v___f_2649_);
v___x_2653_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___f_2645_);
lean_ctor_set(v___x_2635_, 0, v___x_2653_);
v___x_2655_ = v___x_2635_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___f_2645_);
v___x_2655_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; lean_object* v_toApplicative_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2689_; 
v___x_2656_ = l_StateRefT_x27_instMonad___redArg(v___x_2655_);
v_toApplicative_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v___x_2656_, 1);
lean_dec(v_unused_2690_);
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2689_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_toApplicative_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2689_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_toFunctor_2661_; lean_object* v_toSeq_2662_; lean_object* v_toSeqLeft_2663_; lean_object* v_toSeqRight_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2687_; 
v_toFunctor_2661_ = lean_ctor_get(v_toApplicative_2657_, 0);
v_toSeq_2662_ = lean_ctor_get(v_toApplicative_2657_, 2);
v_toSeqLeft_2663_ = lean_ctor_get(v_toApplicative_2657_, 3);
v_toSeqRight_2664_ = lean_ctor_get(v_toApplicative_2657_, 4);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_toApplicative_2657_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v_toApplicative_2657_, 1);
lean_dec(v_unused_2688_);
v___x_2666_ = v_toApplicative_2657_;
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_toSeqRight_2664_);
lean_inc(v_toSeqLeft_2663_);
lean_inc(v_toSeq_2662_);
lean_inc(v_toFunctor_2661_);
lean_dec(v_toApplicative_2657_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___f_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___x_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___f_2675_; lean_object* v___x_2677_; 
v___f_2668_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2669_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2661_);
v___f_2670_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2670_, 0, v_toFunctor_2661_);
v___f_2671_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2671_, 0, v_toFunctor_2661_);
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___f_2670_);
lean_ctor_set(v___x_2672_, 1, v___f_2671_);
v___f_2673_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2673_, 0, v_toSeqRight_2664_);
v___f_2674_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2674_, 0, v_toSeqLeft_2663_);
v___f_2675_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2675_, 0, v_toSeq_2662_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 4, v___f_2673_);
lean_ctor_set(v___x_2666_, 3, v___f_2674_);
lean_ctor_set(v___x_2666_, 2, v___f_2675_);
lean_ctor_set(v___x_2666_, 1, v___f_2668_);
lean_ctor_set(v___x_2666_, 0, v___x_2672_);
v___x_2677_ = v___x_2666_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___f_2668_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v___f_2675_);
lean_ctor_set(v_reuseFailAlloc_2686_, 3, v___f_2674_);
lean_ctor_set(v_reuseFailAlloc_2686_, 4, v___f_2673_);
v___x_2677_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___f_2669_);
lean_ctor_set(v___x_2659_, 0, v___x_2677_);
v___x_2679_ = v___x_2659_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___f_2669_);
v___x_2679_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2508__overap_2683_; lean_object* v___x_2684_; 
v___x_2680_ = l_StateRefT_x27_instMonad___redArg(v___x_2679_);
v___x_2681_ = lean_box(0);
v___x_2682_ = l_instInhabitedOfMonad___redArg(v___x_2680_, v___x_2681_);
v___x_2508__overap_2683_ = lean_panic_fn_borrowed(v___x_2682_, v_msg_2624_);
lean_dec(v___x_2682_);
lean_inc(v___y_2629_);
lean_inc_ref(v___y_2628_);
lean_inc(v___y_2627_);
lean_inc_ref(v___y_2626_);
lean_inc(v___y_2625_);
v___x_2684_ = lean_apply_6(v___x_2508__overap_2683_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, lean_box(0));
return v___x_2684_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
return v_res_2704_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2707_ = lean_unsigned_to_nat(61u);
v___x_2708_ = lean_unsigned_to_nat(304u);
v___x_2709_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2710_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2711_ = l_mkPanicMessageWithDecl(v___x_2710_, v___x_2709_, v___x_2708_, v___x_2707_, v___x_2706_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
switch(lean_obj_tag(v_c_2712_))
{
case 0:
{
lean_object* v_decl_2719_; lean_object* v_value_2720_; 
v_decl_2719_ = lean_ctor_get(v_c_2712_, 0);
v_value_2720_ = lean_ctor_get(v_decl_2719_, 3);
if (lean_obj_tag(v_value_2720_) == 11)
{
lean_object* v_k_2721_; lean_object* v_var_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_inc_ref(v_value_2720_);
v_k_2721_ = lean_ctor_get(v_c_2712_, 1);
lean_inc_ref(v_k_2721_);
lean_dec_ref_known(v_c_2712_, 2);
v_var_2722_ = lean_ctor_get(v_value_2720_, 1);
lean_inc(v_var_2722_);
lean_dec_ref_known(v_value_2720_, 2);
v___x_2723_ = lean_st_ref_take(v_a_2713_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2723_, v_var_2722_, v___x_2724_);
v___x_2726_ = lean_st_ref_set(v_a_2713_, v___x_2725_);
v_c_2712_ = v_k_2721_;
goto _start;
}
else
{
lean_object* v_k_2728_; 
v_k_2728_ = lean_ctor_get(v_c_2712_, 1);
lean_inc_ref(v_k_2728_);
lean_dec_ref_known(v_c_2712_, 2);
v_c_2712_ = v_k_2728_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2730_; lean_object* v_k_2731_; lean_object* v_value_2732_; lean_object* v___x_2733_; 
v_decl_2730_ = lean_ctor_get(v_c_2712_, 0);
lean_inc_ref(v_decl_2730_);
v_k_2731_ = lean_ctor_get(v_c_2712_, 1);
lean_inc_ref(v_k_2731_);
lean_dec_ref_known(v_c_2712_, 2);
v_value_2732_ = lean_ctor_get(v_decl_2730_, 4);
lean_inc_ref(v_value_2732_);
lean_dec_ref(v_decl_2730_);
v___x_2733_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2732_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
v_c_2712_ = v_k_2731_;
goto _start;
}
else
{
lean_dec_ref(v_k_2731_);
return v___x_2733_;
}
}
case 3:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec_ref_known(v_c_2712_, 2);
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
return v___x_2736_;
}
case 4:
{
lean_object* v_cases_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2759_; 
v_cases_2737_ = lean_ctor_get(v_c_2712_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_c_2712_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2739_ = v_c_2712_;
v_isShared_2740_ = v_isSharedCheck_2759_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_cases_2737_);
lean_dec(v_c_2712_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2759_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v_alts_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_alts_2741_ = lean_ctor_get(v_cases_2737_, 3);
lean_inc_ref(v_alts_2741_);
lean_dec_ref(v_cases_2737_);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = lean_array_get_size(v_alts_2741_);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_nat_dec_lt(v___x_2742_, v___x_2743_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2747_; 
lean_dec_ref(v_alts_2741_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2744_);
v___x_2747_ = v___x_2739_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2744_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_nat_dec_le(v___x_2743_, v___x_2743_);
if (v___x_2749_ == 0)
{
if (v___x_2745_ == 0)
{
lean_object* v___x_2751_; 
lean_dec_ref(v_alts_2741_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2744_);
v___x_2751_ = v___x_2739_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2744_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
lean_del_object(v___x_2739_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = lean_usize_of_nat(v___x_2743_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2741_, v___x_2753_, v___x_2754_, v___x_2744_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec_ref(v_alts_2741_);
return v___x_2755_;
}
}
else
{
size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2739_);
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = lean_usize_of_nat(v___x_2743_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2741_, v___x_2756_, v___x_2757_, v___x_2744_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec_ref(v_alts_2741_);
return v___x_2758_;
}
}
}
}
case 5:
{
lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2767_; 
v_isSharedCheck_2767_ = !lean_is_exclusive(v_c_2712_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v_c_2712_, 0);
lean_dec(v_unused_2768_);
v___x_2761_ = v_c_2712_;
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
else
{
lean_dec(v_c_2712_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = lean_box(0);
if (v_isShared_2762_ == 0)
{
lean_ctor_set_tag(v___x_2761_, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2763_);
v___x_2765_ = v___x_2761_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
case 6:
{
lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2776_; 
v_isSharedCheck_2776_ = !lean_is_exclusive(v_c_2712_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; 
v_unused_2777_ = lean_ctor_get(v_c_2712_, 0);
lean_dec(v_unused_2777_);
v___x_2770_ = v_c_2712_;
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_c_2712_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_box(0);
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2772_);
v___x_2774_ = v___x_2770_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
case 8:
{
lean_object* v_k_2778_; 
v_k_2778_ = lean_ctor_get(v_c_2712_, 3);
lean_inc_ref(v_k_2778_);
lean_dec_ref_known(v_c_2712_, 4);
v_c_2712_ = v_k_2778_;
goto _start;
}
case 9:
{
lean_object* v_k_2780_; 
v_k_2780_ = lean_ctor_get(v_c_2712_, 5);
lean_inc_ref(v_k_2780_);
lean_dec_ref_known(v_c_2712_, 6);
v_c_2712_ = v_k_2780_;
goto _start;
}
default: 
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec_ref(v_c_2712_);
v___x_2782_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2783_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2782_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2783_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2784_, size_t v_i_2785_, size_t v_stop_2786_, lean_object* v_b_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___y_2795_; uint8_t v___x_2801_; 
v___x_2801_ = lean_usize_dec_eq(v_i_2785_, v_stop_2786_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_array_uget_borrowed(v_as_2784_, v_i_2785_);
switch(lean_obj_tag(v___x_2802_))
{
case 0:
{
lean_object* v_code_2803_; 
v_code_2803_ = lean_ctor_get(v___x_2802_, 2);
lean_inc_ref(v_code_2803_);
v___y_2795_ = v_code_2803_;
goto v___jp_2794_;
}
case 1:
{
lean_object* v_code_2804_; 
v_code_2804_ = lean_ctor_get(v___x_2802_, 1);
lean_inc_ref(v_code_2804_);
v___y_2795_ = v_code_2804_;
goto v___jp_2794_;
}
default: 
{
lean_object* v_code_2805_; 
v_code_2805_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_code_2805_);
v___y_2795_ = v_code_2805_;
goto v___jp_2794_;
}
}
}
else
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_b_2787_);
return v___x_2806_;
}
v___jp_2794_:
{
lean_object* v___x_2796_; 
v___x_2796_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2795_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; size_t v___x_2798_; size_t v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_add(v_i_2785_, v___x_2798_);
v_i_2785_ = v___x_2799_;
v_b_2787_ = v_a_2797_;
goto _start;
}
else
{
return v___x_2796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2807_, lean_object* v_i_2808_, lean_object* v_stop_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
size_t v_i_boxed_2817_; size_t v_stop_boxed_2818_; lean_object* v_res_2819_; 
v_i_boxed_2817_ = lean_unbox_usize(v_i_2808_);
lean_dec(v_i_2808_);
v_stop_boxed_2818_ = lean_unbox_usize(v_stop_2809_);
lean_dec(v_stop_2809_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2807_, v_i_boxed_2817_, v_stop_boxed_2818_, v_b_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v_as_2807_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
return v_res_2827_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2828_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2833_, lean_object* v_v_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
if (lean_obj_tag(v_v_2834_) == 0)
{
lean_object* v_code_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2865_; 
v_code_2841_ = lean_ctor_get(v_v_2834_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_v_2834_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2843_ = v_v_2834_;
v_isShared_2844_ = v_isSharedCheck_2865_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_code_2841_);
lean_dec(v_v_2834_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2865_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; 
lean_inc(v___y_2839_);
lean_inc_ref(v___y_2838_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc_ref(v___y_2835_);
v___x_2845_ = lean_apply_7(v_f_2833_, v_code_2841_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, lean_box(0));
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2856_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2856_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2856_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_a_2846_);
v___x_2851_ = v___x_2843_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2853_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2851_);
v___x_2853_ = v___x_2848_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2843_);
v_a_2857_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2845_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2845_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
else
{
lean_object* v___x_2866_; 
lean_dec_ref(v_f_2833_);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_v_2834_);
return v___x_2866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2867_, lean_object* v_v_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2867_, v_v_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2876_, lean_object* v_f_2877_, lean_object* v_v_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2877_, v_v_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2886_, lean_object* v_f_2887_, lean_object* v_v_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v_pu_boxed_2895_; lean_object* v_res_2896_; 
v_pu_boxed_2895_ = lean_unbox(v_pu_2886_);
v_res_2896_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_2895_, v_f_2887_, v_v_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2896_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_box(0));
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_alreadyFound_2906_; uint8_t v_relaxedReuse_2907_; lean_object* v_ownedness_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; uint8_t v_relaxedReuse_2915_; 
v_relaxedReuse_2915_ = lean_ctor_get_uint8(v___y_2899_, sizeof(void*)*2);
if (v_relaxedReuse_2915_ == 0)
{
lean_object* v_ownedness_2916_; lean_object* v___x_2917_; 
v_ownedness_2916_ = lean_ctor_get(v___y_2899_, 1);
v___x_2917_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v_alreadyFound_2906_ = v___x_2917_;
v_relaxedReuse_2907_ = v_relaxedReuse_2915_;
v_ownedness_2908_ = v_ownedness_2916_;
v___y_2909_ = v___y_2900_;
v___y_2910_ = v___y_2901_;
v___y_2911_ = v___y_2902_;
v___y_2912_ = v___y_2903_;
goto v___jp_2905_;
}
else
{
lean_object* v_ownedness_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_ownedness_2918_ = lean_ctor_get(v___y_2899_, 1);
v___x_2919_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_2920_ = lean_st_mk_ref(v___x_2919_);
lean_inc_ref(v_code_2898_);
v___x_2921_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_2898_, v___x_2920_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v___x_2922_; 
lean_dec_ref_known(v___x_2921_, 1);
v___x_2922_ = lean_st_ref_get(v___x_2920_);
lean_dec(v___x_2920_);
v_alreadyFound_2906_ = v___x_2922_;
v_relaxedReuse_2907_ = v_relaxedReuse_2915_;
v_ownedness_2908_ = v_ownedness_2918_;
v___y_2909_ = v___y_2900_;
v___y_2910_ = v___y_2901_;
v___y_2911_ = v___y_2902_;
v___y_2912_ = v___y_2903_;
goto v___jp_2905_;
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v___x_2920_);
lean_dec_ref(v_code_2898_);
v_a_2923_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2921_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2921_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
v___jp_2905_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_inc_ref(v_ownedness_2908_);
v___x_2913_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2913_, 0, v_alreadyFound_2906_);
lean_ctor_set(v___x_2913_, 1, v_ownedness_2908_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*2, v_relaxedReuse_2907_);
v___x_2914_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_2898_, v___x_2913_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec_ref_known(v___x_2913_, 2);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_toSignature_2947_; lean_object* v_value_2948_; uint8_t v_recursive_2949_; lean_object* v_inlineAttr_x3f_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2975_; 
v_toSignature_2947_ = lean_ctor_get(v_decl_2940_, 0);
v_value_2948_ = lean_ctor_get(v_decl_2940_, 1);
v_recursive_2949_ = lean_ctor_get_uint8(v_decl_2940_, sizeof(void*)*3);
v_inlineAttr_x3f_2950_ = lean_ctor_get(v_decl_2940_, 2);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_decl_2940_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2952_ = v_decl_2940_;
v_isShared_2953_ = v_isSharedCheck_2975_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_inlineAttr_x3f_2950_);
lean_inc(v_value_2948_);
lean_inc(v_toSignature_2947_);
lean_dec(v_decl_2940_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2975_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_2955_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_2954_, v_value_2948_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2966_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2966_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2966_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v_a_2956_);
v___x_2961_ = v___x_2952_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_toSignature_2947_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_a_2956_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_inlineAttr_x3f_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2965_, sizeof(void*)*3, v_recursive_2949_);
v___x_2961_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2963_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2961_);
v___x_2963_ = v___x_2958_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_del_object(v___x_2952_);
lean_dec(v_inlineAttr_x3f_2950_);
lean_dec_ref(v_toSignature_2947_);
v_a_2967_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2955_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2955_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec_ref(v_a_2977_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2985_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3018_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3018_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3018_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
uint8_t v_resetReuse_2995_; 
v_resetReuse_2995_ = lean_ctor_get_uint8(v_a_2991_, sizeof(void*)*4 + 2);
lean_dec(v_a_2991_);
if (v_resetReuse_2995_ == 0)
{
lean_object* v___x_2997_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_decl_2984_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_decl_2984_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
else
{
lean_object* v___x_2999_; 
lean_del_object(v___x_2993_);
lean_inc_ref(v_decl_2984_);
v___x_2999_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_n(v_a_3000_, 2);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_2984_, v_a_3000_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_3004_ = 0;
lean_inc(v_a_3000_);
v___x_3005_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v_a_3000_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*2, v___x_3004_);
v___x_3006_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3002_, v___x_3005_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec_ref_known(v___x_3005_, 2);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3008_, 0, v___x_3003_);
lean_ctor_set(v___x_3008_, 1, v_a_3000_);
lean_ctor_set_uint8(v___x_3008_, sizeof(void*)*2, v_resetReuse_2995_);
v___x_3009_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3007_, v___x_3008_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec_ref_known(v___x_3008_, 2);
return v___x_3009_;
}
else
{
lean_dec(v_a_3000_);
return v___x_3006_;
}
}
else
{
lean_dec(v_a_3000_);
return v___x_3001_;
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v_decl_2984_);
v_a_3010_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2999_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2999_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v_decl_2984_);
v_a_3019_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2990_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2990_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3040_ = 2;
v___x_3041_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3042_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3041_, v___x_3040_, v___x_3039_, v___x_3038_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3043_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_unsigned_to_nat(2506150707u);
v___x_3100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3101_ = l_Lean_Name_num___override(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3104_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3105_ = l_Lean_Name_str___override(v___x_3104_, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3108_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3109_ = l_Lean_Name_str___override(v___x_3108_, v___x_3107_);
return v___x_3109_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = lean_unsigned_to_nat(2u);
v___x_3111_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3112_ = l_Lean_Name_num___override(v___x_3111_, v___x_3110_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3114_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3115_ = 1;
v___x_3116_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3117_ = l_Lean_registerTraceClass(v___x_3114_, v___x_3115_, v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3119_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
