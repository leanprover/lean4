// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: public import Lean.Compiler.LCNF.PassManager
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elimDeadVars"};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadVars___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 0, 81, 239, 85, 207, 93, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadVars___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 243, 129, 181, 154, 70, 99, 130)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ElimDead"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 82, 16, 255, 163, 142, 141, 196)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 8, 203, 14, 95, 80, 254, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 234, 121, 60, 250, 43, 214, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 227, 118, 194, 153, 141, 66, 82)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 178, 120, 48, 202, 193, 105)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 72, 106, 172, 157, 167, 211, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(154, 254, 227, 186, 107, 229, 199, 236)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 208, 60, 24, 36, 96, 26, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 167, 57, 206, 2, 48, 8, 63)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 61, 197, 124, 13, 119, 183, 129)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 167, 154, 33, 100, 235, 233, 237)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(792928910) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(49, 145, 23, 34, 28, 29, 91, 149)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 85, 234, 87, 122, 159, 213, 105)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 221, 1, 151, 193, 161, 193, 61)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(79, 252, 64, 212, 189, 9, 17, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(lean_object* v_s_1_, lean_object* v_arg_2_){
_start:
{
if (lean_obj_tag(v_arg_2_) == 1)
{
lean_object* v_fvarId_3_; lean_object* v___x_4_; 
v_fvarId_3_ = lean_ctor_get(v_arg_2_, 0);
lean_inc(v_fvarId_3_);
lean_dec_ref_known(v_arg_2_, 1);
v___x_4_ = l_Lean_FVarIdSet_insert(v_s_1_, v_fvarId_3_);
return v___x_4_;
}
else
{
lean_dec(v_arg_2_);
return v_s_1_;
}
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t v_pu_5_, lean_object* v_s_6_, lean_object* v_arg_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_s_6_, v_arg_7_);
return v___x_8_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_5_ = stack[0].m_num;
lean_object* v_s_6_ = stack[1].m_obj;
lean_object* v_arg_7_ = stack[2].m_obj;
lean_object* v_res_9_;
v_res_9_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(v_pu_5_, v_s_6_, v_arg_7_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object* v_pu_10_, lean_object* v_s_11_, lean_object* v_arg_12_){
_start:
{
uint8_t v_pu_boxed_13_; lean_object* v_res_14_; 
v_pu_boxed_13_ = lean_unbox(v_pu_10_);
v_res_14_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(v_pu_boxed_13_, v_s_11_, v_arg_12_);
return v_res_14_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object* v_as_15_, size_t v_i_16_, size_t v_stop_17_, lean_object* v_b_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_usize_dec_eq(v_i_16_, v_stop_17_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; size_t v___x_22_; size_t v___x_23_; 
v___x_20_ = lean_array_uget_borrowed(v_as_15_, v_i_16_);
lean_inc(v___x_20_);
v___x_21_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_b_18_, v___x_20_);
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_add(v_i_16_, v___x_22_);
v_i_16_ = v___x_23_;
v_b_18_ = v___x_21_;
goto _start;
}
else
{
return v_b_18_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_15_ = stack[0].m_obj;
size_t v_i_16_ = stack[1].m_num;
size_t v_stop_17_ = stack[2].m_num;
lean_object* v_b_18_ = stack[3].m_obj;
lean_object* v_res_25_;
v_res_25_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_15_, v_i_16_, v_stop_17_, v_b_18_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object* v_as_26_, lean_object* v_i_27_, lean_object* v_stop_28_, lean_object* v_b_29_){
_start:
{
size_t v_i_boxed_30_; size_t v_stop_boxed_31_; lean_object* v_res_32_; 
v_i_boxed_30_ = lean_unbox_usize(v_i_27_);
lean_dec(v_i_27_);
v_stop_boxed_31_ = lean_unbox_usize(v_stop_28_);
lean_dec(v_stop_28_);
v_res_32_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_26_, v_i_boxed_30_, v_stop_boxed_31_, v_b_29_);
lean_dec_ref(v_as_26_);
return v_res_32_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t v_pu_33_, lean_object* v_s_34_, lean_object* v_args_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_array_get_size(v_args_35_);
v___x_38_ = lean_nat_dec_lt(v___x_36_, v___x_37_);
if (v___x_38_ == 0)
{
return v_s_34_;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = lean_nat_dec_le(v___x_37_, v___x_37_);
if (v___x_39_ == 0)
{
if (v___x_38_ == 0)
{
return v_s_34_;
}
else
{
size_t v___x_40_; size_t v___x_41_; lean_object* v___x_42_; 
v___x_40_ = ((size_t)0ULL);
v___x_41_ = lean_usize_of_nat(v___x_37_);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_35_, v___x_40_, v___x_41_, v_s_34_);
return v___x_42_;
}
}
else
{
size_t v___x_43_; size_t v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((size_t)0ULL);
v___x_44_ = lean_usize_of_nat(v___x_37_);
v___x_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_35_, v___x_43_, v___x_44_, v_s_34_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_33_ = stack[0].m_num;
lean_object* v_s_34_ = stack[1].m_obj;
lean_object* v_args_35_ = stack[2].m_obj;
lean_object* v_res_46_;
v_res_46_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_33_, v_s_34_, v_args_35_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* v_pu_47_, lean_object* v_s_48_, lean_object* v_args_49_){
_start:
{
uint8_t v_pu_boxed_50_; lean_object* v_res_51_; 
v_pu_boxed_50_ = lean_unbox(v_pu_47_);
v_res_51_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_boxed_50_, v_s_48_, v_args_49_);
lean_dec_ref(v_args_49_);
return v_res_51_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t v_pu_52_, lean_object* v_as_53_, size_t v_i_54_, size_t v_stop_55_, lean_object* v_b_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_53_, v_i_54_, v_stop_55_, v_b_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_52_ = stack[0].m_num;
lean_object* v_as_53_ = stack[1].m_obj;
size_t v_i_54_ = stack[2].m_num;
size_t v_stop_55_ = stack[3].m_num;
lean_object* v_b_56_ = stack[4].m_obj;
lean_object* v_res_58_;
v_res_58_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_52_, v_as_53_, v_i_54_, v_stop_55_, v_b_56_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* v_pu_59_, lean_object* v_as_60_, lean_object* v_i_61_, lean_object* v_stop_62_, lean_object* v_b_63_){
_start:
{
uint8_t v_pu_boxed_64_; size_t v_i_boxed_65_; size_t v_stop_boxed_66_; lean_object* v_res_67_; 
v_pu_boxed_64_ = lean_unbox(v_pu_59_);
v_i_boxed_65_ = lean_unbox_usize(v_i_61_);
lean_dec(v_i_61_);
v_stop_boxed_66_ = lean_unbox_usize(v_stop_62_);
lean_dec(v_stop_62_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_64_, v_as_60_, v_i_boxed_65_, v_stop_boxed_66_, v_b_63_);
lean_dec_ref(v_as_60_);
return v_res_67_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t v_pu_68_, lean_object* v_s_69_, lean_object* v_e_70_){
_start:
{
switch(lean_obj_tag(v_e_70_))
{
case 2:
{
lean_object* v_struct_71_; lean_object* v___x_72_; 
v_struct_71_ = lean_ctor_get(v_e_70_, 2);
lean_inc(v_struct_71_);
lean_dec_ref_known(v_e_70_, 3);
v___x_72_ = l_Lean_FVarIdSet_insert(v_s_69_, v_struct_71_);
return v___x_72_;
}
case 3:
{
lean_object* v_args_73_; lean_object* v___x_74_; 
v_args_73_ = lean_ctor_get(v_e_70_, 2);
lean_inc_ref(v_args_73_);
lean_dec_ref_known(v_e_70_, 3);
v___x_74_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_68_, v_s_69_, v_args_73_);
lean_dec_ref(v_args_73_);
return v___x_74_;
}
case 4:
{
lean_object* v_fvarId_75_; lean_object* v_args_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_fvarId_75_ = lean_ctor_get(v_e_70_, 0);
lean_inc(v_fvarId_75_);
v_args_76_ = lean_ctor_get(v_e_70_, 1);
lean_inc_ref(v_args_76_);
lean_dec_ref_known(v_e_70_, 2);
v___x_77_ = l_Lean_FVarIdSet_insert(v_s_69_, v_fvarId_75_);
v___x_78_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_68_, v___x_77_, v_args_76_);
lean_dec_ref(v_args_76_);
return v___x_78_;
}
case 5:
{
lean_object* v_args_79_; lean_object* v___x_80_; 
v_args_79_ = lean_ctor_get(v_e_70_, 1);
lean_inc_ref(v_args_79_);
lean_dec_ref_known(v_e_70_, 2);
v___x_80_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_68_, v_s_69_, v_args_79_);
lean_dec_ref(v_args_79_);
return v___x_80_;
}
case 6:
{
lean_object* v_var_81_; lean_object* v___x_82_; 
v_var_81_ = lean_ctor_get(v_e_70_, 1);
lean_inc(v_var_81_);
lean_dec_ref_known(v_e_70_, 2);
v___x_82_ = l_Lean_FVarIdSet_insert(v_s_69_, v_var_81_);
return v___x_82_;
}
case 7:
{
lean_object* v_var_83_; lean_object* v___x_84_; 
v_var_83_ = lean_ctor_get(v_e_70_, 1);
lean_inc(v_var_83_);
lean_dec_ref_known(v_e_70_, 2);
v___x_84_ = l_Lean_FVarIdSet_insert(v_s_69_, v_var_83_);
return v___x_84_;
}
case 8:
{
lean_object* v_var_85_; lean_object* v___x_86_; 
v_var_85_ = lean_ctor_get(v_e_70_, 2);
lean_inc(v_var_85_);
lean_dec_ref_known(v_e_70_, 3);
v___x_86_ = l_Lean_FVarIdSet_insert(v_s_69_, v_var_85_);
return v___x_86_;
}
case 9:
{
lean_object* v_args_87_; lean_object* v___x_88_; 
v_args_87_ = lean_ctor_get(v_e_70_, 1);
lean_inc_ref(v_args_87_);
lean_dec_ref_known(v_e_70_, 2);
v___x_88_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_68_, v_s_69_, v_args_87_);
lean_dec_ref(v_args_87_);
return v___x_88_;
}
case 10:
{
lean_object* v_args_89_; lean_object* v___x_90_; 
v_args_89_ = lean_ctor_get(v_e_70_, 1);
lean_inc_ref(v_args_89_);
lean_dec_ref_known(v_e_70_, 2);
v___x_90_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_68_, v_s_69_, v_args_89_);
lean_dec_ref(v_args_89_);
return v___x_90_;
}
case 11:
{
lean_object* v_var_91_; lean_object* v___x_92_; 
v_var_91_ = lean_ctor_get(v_e_70_, 1);
lean_inc(v_var_91_);
lean_dec_ref_known(v_e_70_, 2);
v___x_92_ = l_Lean_FVarIdSet_insert(v_s_69_, v_var_91_);
return v___x_92_;
}
case 12:
{
lean_object* v_var_93_; lean_object* v_args_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_var_93_ = lean_ctor_get(v_e_70_, 0);
lean_inc(v_var_93_);
v_args_94_ = lean_ctor_get(v_e_70_, 2);
lean_inc_ref(v_args_94_);
lean_dec_ref_known(v_e_70_, 3);
v___x_95_ = l_Lean_FVarIdSet_insert(v_s_69_, v_var_93_);
v___x_96_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_68_, v___x_95_, v_args_94_);
lean_dec_ref(v_args_94_);
return v___x_96_;
}
case 13:
{
lean_object* v_fvarId_97_; lean_object* v___x_98_; 
v_fvarId_97_ = lean_ctor_get(v_e_70_, 1);
lean_inc(v_fvarId_97_);
lean_dec_ref_known(v_e_70_, 2);
v___x_98_ = l_Lean_FVarIdSet_insert(v_s_69_, v_fvarId_97_);
return v___x_98_;
}
case 14:
{
lean_object* v_fvarId_99_; lean_object* v___x_100_; 
v_fvarId_99_ = lean_ctor_get(v_e_70_, 0);
lean_inc(v_fvarId_99_);
lean_dec_ref_known(v_e_70_, 1);
v___x_100_ = l_Lean_FVarIdSet_insert(v_s_69_, v_fvarId_99_);
return v___x_100_;
}
case 15:
{
lean_object* v_fvarId_101_; lean_object* v___x_102_; 
v_fvarId_101_ = lean_ctor_get(v_e_70_, 0);
lean_inc(v_fvarId_101_);
lean_dec_ref_known(v_e_70_, 1);
v___x_102_ = l_Lean_FVarIdSet_insert(v_s_69_, v_fvarId_101_);
return v___x_102_;
}
default: 
{
lean_dec(v_e_70_);
return v_s_69_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_68_ = stack[0].m_num;
lean_object* v_s_69_ = stack[1].m_obj;
lean_object* v_e_70_ = stack[2].m_obj;
lean_object* v_res_103_;
v_res_103_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_68_, v_s_69_, v_e_70_);
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object* v_pu_104_, lean_object* v_s_105_, lean_object* v_e_106_){
_start:
{
uint8_t v_pu_boxed_107_; lean_object* v_res_108_; 
v_pu_boxed_107_ = lean_unbox(v_pu_104_);
v_res_108_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_boxed_107_, v_s_105_, v_e_106_);
return v_res_108_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object* v_arg_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = lean_st_ref_take(v_a_110_);
v___x_113_ = lean_box(0);
v___x_114_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_112_, v_arg_109_);
v___x_115_ = lean_st_ref_put(v_a_110_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_113_);
return v___x_116_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_109_ = stack[0].m_obj;
lean_object* v_a_110_ = stack[1].m_obj;
lean_object* v_res_117_;
v_res_117_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(v_arg_109_, v_a_110_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object* v_arg_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(v_arg_118_, v_a_119_);
lean_dec(v_a_119_);
return v_res_121_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t v_pu_122_, lean_object* v_arg_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_130_ = lean_st_ref_take(v_a_124_);
v___x_131_ = lean_box(0);
v___x_132_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_130_, v_arg_123_);
v___x_133_ = lean_st_ref_put(v_a_124_, v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_131_);
return v___x_134_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_122_ = stack[0].m_num;
lean_object* v_arg_123_ = stack[1].m_obj;
lean_object* v_a_124_ = stack[2].m_obj;
lean_object* v_a_125_ = stack[3].m_obj;
lean_object* v_a_126_ = stack[4].m_obj;
lean_object* v_a_127_ = stack[5].m_obj;
lean_object* v_a_128_ = stack[6].m_obj;
lean_object* v_res_135_;
v_res_135_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(v_pu_122_, v_arg_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object* v_pu_136_, lean_object* v_arg_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
uint8_t v_pu_boxed_144_; lean_object* v_res_145_; 
v_pu_boxed_144_ = lean_unbox(v_pu_136_);
v_res_145_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(v_pu_boxed_144_, v_arg_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
return v_res_145_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t v_pu_146_, lean_object* v_e_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = lean_st_ref_take(v_a_148_);
v___x_151_ = lean_box(0);
v___x_152_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_146_, v___x_150_, v_e_147_);
v___x_153_ = lean_st_ref_put(v_a_148_, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_151_);
return v___x_154_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_146_ = stack[0].m_num;
lean_object* v_e_147_ = stack[1].m_obj;
lean_object* v_a_148_ = stack[2].m_obj;
lean_object* v_res_155_;
v_res_155_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(v_pu_146_, v_e_147_, v_a_148_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object* v_pu_156_, lean_object* v_e_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
uint8_t v_pu_boxed_160_; lean_object* v_res_161_; 
v_pu_boxed_160_ = lean_unbox(v_pu_156_);
v_res_161_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(v_pu_boxed_160_, v_e_157_, v_a_158_);
lean_dec(v_a_158_);
return v_res_161_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t v_pu_162_, lean_object* v_e_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = lean_st_ref_take(v_a_164_);
v___x_171_ = lean_box(0);
v___x_172_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_162_, v___x_170_, v_e_163_);
v___x_173_ = lean_st_ref_put(v_a_164_, v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_171_);
return v___x_174_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_162_ = stack[0].m_num;
lean_object* v_e_163_ = stack[1].m_obj;
lean_object* v_a_164_ = stack[2].m_obj;
lean_object* v_a_165_ = stack[3].m_obj;
lean_object* v_a_166_ = stack[4].m_obj;
lean_object* v_a_167_ = stack[5].m_obj;
lean_object* v_a_168_ = stack[6].m_obj;
lean_object* v_res_175_;
v_res_175_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(v_pu_162_, v_e_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object* v_pu_176_, lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
uint8_t v_pu_boxed_184_; lean_object* v_res_185_; 
v_pu_boxed_184_ = lean_unbox(v_pu_176_);
v_res_185_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(v_pu_boxed_184_, v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
return v_res_185_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object* v_fvarId_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = lean_st_ref_take(v_a_187_);
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_FVarIdSet_insert(v___x_189_, v_fvarId_186_);
v___x_192_ = lean_st_ref_put(v_a_187_, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_190_);
return v___x_193_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_186_ = stack[0].m_obj;
lean_object* v_a_187_ = stack[1].m_obj;
lean_object* v_res_194_;
v_res_194_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(v_fvarId_186_, v_a_187_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object* v_fvarId_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(v_fvarId_195_, v_a_196_);
lean_dec(v_a_196_);
return v_res_198_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object* v_fvarId_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = lean_st_ref_take(v_a_200_);
v___x_207_ = lean_box(0);
v___x_208_ = l_Lean_FVarIdSet_insert(v___x_206_, v_fvarId_199_);
v___x_209_ = lean_st_ref_put(v_a_200_, v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
return v___x_210_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_199_ = stack[0].m_obj;
lean_object* v_a_200_ = stack[1].m_obj;
lean_object* v_a_201_ = stack[2].m_obj;
lean_object* v_a_202_ = stack[3].m_obj;
lean_object* v_a_203_ = stack[4].m_obj;
lean_object* v_a_204_ = stack[5].m_obj;
lean_object* v_res_211_;
v_res_211_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(v_fvarId_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object* v_fvarId_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(v_fvarId_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
return v_res_219_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t v_pu_220_, lean_object* v_val_221_){
_start:
{
if (v_pu_220_ == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 1;
return v___x_222_;
}
else
{
switch(lean_obj_tag(v_val_221_))
{
case 4:
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
case 9:
{
lean_object* v_args_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_args_224_ = lean_ctor_get(v_val_221_, 1);
v___x_225_ = lean_array_get_size(v_args_224_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
return v___x_227_;
}
default: 
{
uint8_t v___x_228_; 
v___x_228_ = 1;
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_220_ = stack[0].m_num;
lean_object* v_val_221_ = stack[1].m_obj;
uint8_t v_res_229_;
v_res_229_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_220_, v_val_221_);
stack->m_num = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object* v_pu_230_, lean_object* v_val_231_){
_start:
{
uint8_t v_pu_boxed_232_; uint8_t v_res_233_; lean_object* v_r_234_; 
v_pu_boxed_232_ = lean_unbox(v_pu_230_);
v_res_233_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_boxed_232_, v_val_231_);
lean_dec(v_val_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object* v_as_235_, size_t v_i_236_, size_t v_stop_237_, lean_object* v_b_238_, lean_object* v___y_239_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_eq(v_i_236_, v_stop_237_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; size_t v___x_247_; size_t v___x_248_; 
v___x_242_ = lean_array_uget_borrowed(v_as_235_, v_i_236_);
v___x_243_ = lean_st_ref_take(v___y_239_);
v___x_244_ = lean_box(0);
lean_inc(v___x_242_);
v___x_245_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_243_, v___x_242_);
v___x_246_ = lean_st_ref_put(v___y_239_, v___x_245_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_add(v_i_236_, v___x_247_);
v_i_236_ = v___x_248_;
v_b_238_ = v___x_244_;
goto _start;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_b_238_);
return v___x_250_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_235_ = stack[0].m_obj;
size_t v_i_236_ = stack[1].m_num;
size_t v_stop_237_ = stack[2].m_num;
lean_object* v_b_238_ = stack[3].m_obj;
lean_object* v___y_239_ = stack[4].m_obj;
lean_object* v_res_251_;
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_235_, v_i_236_, v_stop_237_, v_b_238_, v___y_239_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object* v_as_252_, lean_object* v_i_253_, lean_object* v_stop_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
size_t v_i_boxed_258_; size_t v_stop_boxed_259_; lean_object* v_res_260_; 
v_i_boxed_258_ = lean_unbox_usize(v_i_253_);
lean_dec(v_i_253_);
v_stop_boxed_259_ = lean_unbox_usize(v_stop_254_);
lean_dec(v_stop_254_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_252_, v_i_boxed_258_, v_stop_boxed_259_, v_b_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v_as_252_);
return v_res_260_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object* v_k_261_, lean_object* v_t_262_){
_start:
{
if (lean_obj_tag(v_t_262_) == 0)
{
lean_object* v_k_263_; lean_object* v_l_264_; lean_object* v_r_265_; uint8_t v___x_266_; 
v_k_263_ = lean_ctor_get(v_t_262_, 1);
v_l_264_ = lean_ctor_get(v_t_262_, 3);
v_r_265_ = lean_ctor_get(v_t_262_, 4);
v___x_266_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_261_, v_k_263_);
switch(v___x_266_)
{
case 0:
{
v_t_262_ = v_l_264_;
goto _start;
}
case 1:
{
uint8_t v___x_268_; 
v___x_268_ = 1;
return v___x_268_;
}
default: 
{
v_t_262_ = v_r_265_;
goto _start;
}
}
}
else
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_261_ = stack[0].m_obj;
lean_object* v_t_262_ = stack[1].m_obj;
uint8_t v_res_271_;
v_res_271_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_261_, v_t_262_);
stack->m_num = v_res_271_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object* v_k_272_, lean_object* v_t_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_272_, v_t_273_);
lean_dec(v_t_273_);
lean_dec(v_k_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t v_pu_276_, lean_object* v_i_277_, lean_object* v_as_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_array_get_size(v_as_278_);
v___x_286_ = lean_nat_dec_lt(v_i_277_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec(v_i_277_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_as_278_);
return v___x_287_;
}
else
{
lean_object* v_a_288_; lean_object* v___y_290_; 
v_a_288_ = lean_array_fget_borrowed(v_as_278_, v_i_277_);
switch(lean_obj_tag(v_a_288_))
{
case 0:
{
lean_object* v_code_312_; 
v_code_312_ = lean_ctor_get(v_a_288_, 2);
lean_inc_ref(v_code_312_);
v___y_290_ = v_code_312_;
goto v___jp_289_;
}
case 1:
{
lean_object* v_code_313_; 
v_code_313_ = lean_ctor_get(v_a_288_, 1);
lean_inc_ref(v_code_313_);
v___y_290_ = v_code_313_;
goto v___jp_289_;
}
default: 
{
lean_object* v_code_314_; 
v_code_314_ = lean_ctor_get(v_a_288_, 0);
lean_inc_ref(v_code_314_);
v___y_290_ = v_code_314_;
goto v___jp_289_;
}
}
v___jp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_276_, v___y_290_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; size_t v___x_294_; size_t v___x_295_; uint8_t v___x_296_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
lean_inc(v_a_288_);
v___x_293_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_288_, v_a_292_);
v___x_294_ = lean_ptr_addr(v_a_288_);
v___x_295_ = lean_ptr_addr(v___x_293_);
v___x_296_ = lean_usize_dec_eq(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_i_277_, v___x_297_);
v___x_299_ = lean_array_fset(v_as_278_, v_i_277_, v___x_293_);
lean_dec(v_i_277_);
v_i_277_ = v___x_298_;
v_as_278_ = v___x_299_;
goto _start;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref(v___x_293_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_277_, v___x_301_);
lean_dec(v_i_277_);
v_i_277_ = v___x_302_;
goto _start;
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref(v_as_278_);
lean_dec(v_i_277_);
v_a_304_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_291_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_291_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_276_ = stack[0].m_num;
lean_object* v_i_277_ = stack[1].m_obj;
lean_object* v_as_278_ = stack[2].m_obj;
lean_object* v___y_279_ = stack[3].m_obj;
lean_object* v___y_280_ = stack[4].m_obj;
lean_object* v___y_281_ = stack[5].m_obj;
lean_object* v___y_282_ = stack[6].m_obj;
lean_object* v___y_283_ = stack[7].m_obj;
lean_object* v_res_315_;
v_res_315_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_276_, v_i_277_, v_as_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
stack->m_obj
 = v_res_315_;
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t v_pu_316_, lean_object* v_code_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___y_325_; 
switch(lean_obj_tag(v_code_317_))
{
case 0:
{
lean_object* v_decl_342_; lean_object* v_k_343_; lean_object* v___x_344_; 
v_decl_342_ = lean_ctor_get(v_code_317_, 0);
v_k_343_ = lean_ctor_get(v_code_317_, 1);
lean_inc_ref(v_k_343_);
v___x_344_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_343_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_395_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_395_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_395_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_395_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v_fvarId_350_; lean_object* v_value_351_; uint8_t v___y_375_; uint8_t v___x_393_; 
v___x_349_ = lean_st_ref_get(v_a_318_);
v_fvarId_350_ = lean_ctor_get(v_decl_342_, 0);
v_value_351_ = lean_ctor_get(v_decl_342_, 3);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_350_, v___x_349_);
lean_dec(v___x_349_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_316_, v_value_351_);
if (v___x_394_ == 0)
{
goto v___jp_352_;
}
else
{
v___y_375_ = v___x_393_;
goto v___jp_374_;
}
}
else
{
v___y_375_ = v___x_393_;
goto v___jp_374_;
}
v___jp_352_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; uint8_t v___x_358_; 
v___x_353_ = lean_st_ref_take(v_a_318_);
lean_inc(v_value_351_);
v___x_354_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_316_, v___x_353_, v_value_351_);
v___x_355_ = lean_st_ref_put(v_a_318_, v___x_354_);
v___x_356_ = lean_ptr_addr(v_k_343_);
v___x_357_ = lean_ptr_addr(v_a_345_);
v___x_358_ = lean_usize_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
lean_inc_ref(v_decl_342_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; 
v_unused_369_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_370_);
v___x_360_ = v_code_317_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_code_317_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_a_345_);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_decl_342_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_a_345_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_363_);
v___x_365_ = v___x_347_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v_a_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v_code_317_);
v___x_372_ = v___x_347_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_code_317_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
v___jp_374_:
{
if (v___y_375_ == 0)
{
lean_object* v___x_376_; 
lean_inc_ref(v_decl_342_);
lean_del_object(v___x_347_);
lean_dec_ref_known(v_code_317_, 2);
v___x_376_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_316_, v_decl_342_, v_a_320_);
lean_dec_ref(v_decl_342_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_376_, 0);
lean_dec(v_unused_384_);
v___x_378_ = v___x_376_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_dec(v___x_376_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v_a_345_);
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_345_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_345_);
v_a_385_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
goto v___jp_352_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 2);
return v___x_344_;
}
}
case 1:
{
lean_object* v_decl_396_; lean_object* v_k_397_; lean_object* v___x_398_; 
v_decl_396_ = lean_ctor_get(v_code_317_, 0);
v_k_397_ = lean_ctor_get(v_code_317_, 1);
lean_inc_ref(v_k_397_);
v___x_398_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_397_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v_fvarId_401_; uint8_t v___x_402_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = lean_st_ref_get(v_a_318_);
v_fvarId_401_ = lean_ctor_get(v_decl_396_, 0);
v___x_402_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_401_, v___x_400_);
lean_dec(v___x_400_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; lean_object* v___x_404_; 
lean_inc_ref(v_decl_396_);
lean_dec_ref_known(v_code_317_, 2);
v___x_403_ = 1;
v___x_404_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_316_, v_decl_396_, v___x_403_, v_a_320_);
lean_dec_ref(v_decl_396_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_404_, 0);
lean_dec(v_unused_412_);
v___x_406_ = v___x_404_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_dec(v___x_404_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_a_399_);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_399_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_a_399_);
v_a_413_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_404_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_404_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_421_; 
lean_inc_ref(v_decl_396_);
v___x_421_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_316_, v_decl_396_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_459_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_459_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_459_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_459_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
size_t v___x_426_; size_t v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_ptr_addr(v_k_397_);
v___x_427_ = lean_ptr_addr(v_a_399_);
v___x_428_ = lean_usize_dec_eq(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_438_; 
v_isSharedCheck_438_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; 
v_unused_439_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_440_);
v___x_430_ = v_code_317_;
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
else
{
lean_dec(v_code_317_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_a_399_);
lean_ctor_set(v___x_430_, 0, v_a_422_);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_a_399_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_433_);
v___x_435_ = v___x_424_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
size_t v___x_441_; size_t v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_ptr_addr(v_decl_396_);
v___x_442_ = lean_ptr_addr(v_a_422_);
v___x_443_ = lean_usize_dec_eq(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_isSharedCheck_453_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; 
v_unused_454_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_455_);
v___x_445_ = v_code_317_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_code_317_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v_a_399_);
lean_ctor_set(v___x_445_, 0, v_a_422_);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_422_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_a_399_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_448_);
v___x_450_ = v___x_424_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v_a_422_);
lean_dec(v_a_399_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v_code_317_);
v___x_457_ = v___x_424_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_code_317_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_399_);
lean_dec_ref_known(v_code_317_, 2);
v_a_460_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_421_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_421_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 2);
return v___x_398_;
}
}
case 2:
{
lean_object* v_decl_468_; lean_object* v_k_469_; lean_object* v___x_470_; 
v_decl_468_ = lean_ctor_get(v_code_317_, 0);
v_k_469_ = lean_ctor_get(v_code_317_, 1);
lean_inc_ref(v_k_469_);
v___x_470_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_469_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v_fvarId_473_; uint8_t v___x_474_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = lean_st_ref_get(v_a_318_);
v_fvarId_473_ = lean_ctor_get(v_decl_468_, 0);
v___x_474_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_473_, v___x_472_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; lean_object* v___x_476_; 
lean_inc_ref(v_decl_468_);
lean_dec_ref_known(v_code_317_, 2);
v___x_475_ = 1;
v___x_476_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_316_, v_decl_468_, v___x_475_, v_a_320_);
lean_dec_ref(v_decl_468_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___x_476_, 0);
lean_dec(v_unused_484_);
v___x_478_ = v___x_476_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_dec(v___x_476_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v_a_471_);
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_471_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_a_471_);
v_a_485_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_476_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_476_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_493_; 
lean_inc_ref(v_decl_468_);
v___x_493_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_316_, v_decl_468_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_531_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_531_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_531_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_531_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
size_t v___x_498_; size_t v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_ptr_addr(v_k_469_);
v___x_499_ = lean_ptr_addr(v_a_471_);
v___x_500_ = lean_usize_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_isSharedCheck_510_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; lean_object* v_unused_512_; 
v_unused_511_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_511_);
v_unused_512_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_512_);
v___x_502_ = v_code_317_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_code_317_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v_a_471_);
lean_ctor_set(v___x_502_, 0, v_a_494_);
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_a_471_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_505_);
v___x_507_ = v___x_496_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_decl_468_);
v___x_514_ = lean_ptr_addr(v_a_494_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_525_; 
v_isSharedCheck_525_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_526_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_527_);
v___x_517_ = v_code_317_;
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
else
{
lean_dec(v_code_317_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v_a_471_);
lean_ctor_set(v___x_517_, 0, v_a_494_);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_a_471_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_520_);
v___x_522_ = v___x_496_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v_a_494_);
lean_dec(v_a_471_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_code_317_);
v___x_529_ = v___x_496_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_code_317_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_471_);
lean_dec_ref_known(v_code_317_, 2);
v_a_532_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_493_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_493_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 2);
return v___x_470_;
}
}
case 3:
{
lean_object* v_fvarId_540_; lean_object* v_args_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_fvarId_540_ = lean_ctor_get(v_code_317_, 0);
v_args_541_ = lean_ctor_get(v_code_317_, 1);
v___x_542_ = lean_st_ref_take(v_a_318_);
lean_inc(v_fvarId_540_);
v___x_543_ = l_Lean_FVarIdSet_insert(v___x_542_, v_fvarId_540_);
v___x_544_ = lean_st_ref_put(v_a_318_, v___x_543_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_array_get_size(v_args_541_);
v___x_547_ = lean_nat_dec_lt(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_code_317_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_box(0);
v___x_550_ = lean_nat_dec_le(v___x_546_, v___x_546_);
if (v___x_550_ == 0)
{
if (v___x_547_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_code_317_);
return v___x_551_;
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_546_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_541_, v___x_552_, v___x_553_, v___x_549_, v_a_318_);
v___y_325_ = v___x_554_;
goto v___jp_324_;
}
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((size_t)0ULL);
v___x_556_ = lean_usize_of_nat(v___x_546_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_541_, v___x_555_, v___x_556_, v___x_549_, v_a_318_);
v___y_325_ = v___x_557_;
goto v___jp_324_;
}
}
}
case 4:
{
lean_object* v_cases_558_; lean_object* v_typeName_559_; lean_object* v_resultType_560_; lean_object* v_discr_561_; lean_object* v_alts_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_604_; 
v_cases_558_ = lean_ctor_get(v_code_317_, 0);
lean_inc_ref(v_cases_558_);
v_typeName_559_ = lean_ctor_get(v_cases_558_, 0);
v_resultType_560_ = lean_ctor_get(v_cases_558_, 1);
v_discr_561_ = lean_ctor_get(v_cases_558_, 2);
v_alts_562_ = lean_ctor_get(v_cases_558_, 3);
v_isSharedCheck_604_ = !lean_is_exclusive(v_cases_558_);
if (v_isSharedCheck_604_ == 0)
{
v___x_564_ = v_cases_558_;
v_isShared_565_ = v_isSharedCheck_604_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_alts_562_);
lean_inc(v_discr_561_);
lean_inc(v_resultType_560_);
lean_inc(v_typeName_559_);
lean_dec(v_cases_558_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_604_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_562_);
v___x_567_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_316_, v___x_566_, v_alts_562_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_595_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_595_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_595_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_595_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v___x_572_ = lean_st_ref_take(v_a_318_);
lean_inc(v_discr_561_);
v___x_573_ = l_Lean_FVarIdSet_insert(v___x_572_, v_discr_561_);
v___x_574_ = lean_st_ref_put(v_a_318_, v___x_573_);
v___x_575_ = lean_ptr_addr(v_alts_562_);
lean_dec_ref(v_alts_562_);
v___x_576_ = lean_ptr_addr(v_a_568_);
v___x_577_ = lean_usize_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_591_);
v___x_579_ = v_code_317_;
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
else
{
lean_dec(v_code_317_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 3, v_a_568_);
v___x_582_ = v___x_564_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_typeName_559_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_resultType_560_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_discr_561_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_a_568_);
v___x_582_ = v_reuseFailAlloc_589_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_582_);
v___x_584_ = v___x_579_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_584_);
v___x_586_ = v___x_570_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec(v_a_568_);
lean_del_object(v___x_564_);
lean_dec(v_discr_561_);
lean_dec_ref(v_resultType_560_);
lean_dec(v_typeName_559_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_code_317_);
v___x_593_ = v___x_570_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_code_317_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_del_object(v___x_564_);
lean_dec_ref(v_alts_562_);
lean_dec(v_discr_561_);
lean_dec_ref(v_resultType_560_);
lean_dec(v_typeName_559_);
lean_dec_ref_known(v_code_317_, 1);
v_a_596_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_567_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_567_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_fvarId_605_ = lean_ctor_get(v_code_317_, 0);
v___x_606_ = lean_st_ref_take(v_a_318_);
lean_inc(v_fvarId_605_);
v___x_607_ = l_Lean_FVarIdSet_insert(v___x_606_, v_fvarId_605_);
v___x_608_ = lean_st_ref_put(v_a_318_, v___x_607_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_code_317_);
return v___x_609_;
}
case 6:
{
lean_object* v___x_610_; 
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_code_317_);
return v___x_610_;
}
case 7:
{
lean_object* v_fvarId_611_; lean_object* v_i_612_; lean_object* v_y_613_; lean_object* v_k_614_; lean_object* v___x_615_; 
v_fvarId_611_ = lean_ctor_get(v_code_317_, 0);
v_i_612_ = lean_ctor_get(v_code_317_, 1);
v_y_613_ = lean_ctor_get(v_code_317_, 2);
v_k_614_ = lean_ctor_get(v_code_317_, 3);
lean_inc_ref(v_k_614_);
v___x_615_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_614_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_648_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_648_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_648_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_648_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_st_ref_get(v_a_318_);
v___x_621_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_611_, v___x_620_);
lean_dec(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref_known(v_code_317_, 4);
if (v_isShared_619_ == 0)
{
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_616_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; size_t v___x_628_; size_t v___x_629_; uint8_t v___x_630_; 
v___x_625_ = lean_st_ref_take(v_a_318_);
lean_inc(v_y_613_);
v___x_626_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_625_, v_y_613_);
v___x_627_ = lean_st_ref_put(v_a_318_, v___x_626_);
v___x_628_ = lean_ptr_addr(v_k_614_);
v___x_629_ = lean_ptr_addr(v_a_616_);
v___x_630_ = lean_usize_dec_eq(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_640_; 
lean_inc(v_y_613_);
lean_inc(v_i_612_);
lean_inc(v_fvarId_611_);
v_isSharedCheck_640_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_641_ = lean_ctor_get(v_code_317_, 3);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_code_317_, 2);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_644_);
v___x_632_ = v_code_317_;
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
else
{
lean_dec(v_code_317_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 3, v_a_616_);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fvarId_611_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_i_612_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_y_613_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_a_616_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_635_);
v___x_637_ = v___x_618_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v___x_646_; 
lean_dec(v_a_616_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_code_317_);
v___x_646_ = v___x_618_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_code_317_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 4);
return v___x_615_;
}
}
case 8:
{
lean_object* v_fvarId_649_; lean_object* v_i_650_; lean_object* v_y_651_; lean_object* v_k_652_; lean_object* v___x_653_; 
v_fvarId_649_ = lean_ctor_get(v_code_317_, 0);
v_i_650_ = lean_ctor_get(v_code_317_, 1);
v_y_651_ = lean_ctor_get(v_code_317_, 2);
v_k_652_ = lean_ctor_get(v_code_317_, 3);
lean_inc_ref(v_k_652_);
v___x_653_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_652_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_686_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_686_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_686_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_686_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_st_ref_get(v_a_318_);
v___x_659_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_649_, v___x_658_);
lean_dec(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref_known(v_code_317_, 4);
if (v_isShared_657_ == 0)
{
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_654_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; size_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_663_ = lean_st_ref_take(v_a_318_);
lean_inc(v_y_651_);
v___x_664_ = l_Lean_FVarIdSet_insert(v___x_663_, v_y_651_);
v___x_665_ = lean_st_ref_put(v_a_318_, v___x_664_);
v___x_666_ = lean_ptr_addr(v_k_652_);
v___x_667_ = lean_ptr_addr(v_a_654_);
v___x_668_ = lean_usize_dec_eq(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_y_651_);
lean_inc(v_i_650_);
lean_inc(v_fvarId_649_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_679_ = lean_ctor_get(v_code_317_, 3);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_code_317_, 2);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_682_);
v___x_670_ = v_code_317_;
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_code_317_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 3, v_a_654_);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fvarId_649_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_i_650_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_y_651_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_a_654_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_673_);
v___x_675_ = v___x_656_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v_a_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v_code_317_);
v___x_684_ = v___x_656_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_code_317_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 4);
return v___x_653_;
}
}
case 9:
{
lean_object* v_fvarId_687_; lean_object* v_i_688_; lean_object* v_offset_689_; lean_object* v_y_690_; lean_object* v_ty_691_; lean_object* v_k_692_; lean_object* v___x_693_; 
v_fvarId_687_ = lean_ctor_get(v_code_317_, 0);
v_i_688_ = lean_ctor_get(v_code_317_, 1);
v_offset_689_ = lean_ctor_get(v_code_317_, 2);
v_y_690_ = lean_ctor_get(v_code_317_, 3);
v_ty_691_ = lean_ctor_get(v_code_317_, 4);
v_k_692_ = lean_ctor_get(v_code_317_, 5);
lean_inc_ref(v_k_692_);
v___x_693_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_692_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_728_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_728_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_728_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_728_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_st_ref_get(v_a_318_);
v___x_699_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_687_, v___x_698_);
lean_dec(v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_701_; 
lean_dec_ref_known(v_code_317_, 6);
if (v_isShared_697_ == 0)
{
v___x_701_ = v___x_696_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_694_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v___x_703_ = lean_st_ref_take(v_a_318_);
lean_inc(v_y_690_);
v___x_704_ = l_Lean_FVarIdSet_insert(v___x_703_, v_y_690_);
v___x_705_ = lean_st_ref_put(v_a_318_, v___x_704_);
v___x_706_ = lean_ptr_addr(v_k_692_);
v___x_707_ = lean_ptr_addr(v_a_694_);
v___x_708_ = lean_usize_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_718_; 
lean_inc_ref(v_ty_691_);
lean_inc(v_y_690_);
lean_inc(v_offset_689_);
lean_inc(v_i_688_);
lean_inc(v_fvarId_687_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_719_ = lean_ctor_get(v_code_317_, 5);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_code_317_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_code_317_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_code_317_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_724_);
v___x_710_ = v_code_317_;
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
else
{
lean_dec(v_code_317_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 5, v_a_694_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fvarId_687_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_i_688_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_offset_689_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_y_690_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_ty_691_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_a_694_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_713_);
v___x_715_ = v___x_696_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v___x_726_; 
lean_dec(v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_code_317_);
v___x_726_ = v___x_696_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_code_317_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 6);
return v___x_693_;
}
}
case 10:
{
lean_object* v_fvarId_729_; lean_object* v_cidx_730_; lean_object* v_k_731_; lean_object* v___x_732_; 
v_fvarId_729_ = lean_ctor_get(v_code_317_, 0);
v_cidx_730_ = lean_ctor_get(v_code_317_, 1);
v_k_731_ = lean_ctor_get(v_code_317_, 2);
lean_inc_ref(v_k_731_);
v___x_732_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_731_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_759_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_759_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_759_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_759_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; size_t v___x_740_; size_t v___x_741_; uint8_t v___x_742_; 
v___x_737_ = lean_st_ref_take(v_a_318_);
lean_inc(v_fvarId_729_);
v___x_738_ = l_Lean_FVarIdSet_insert(v___x_737_, v_fvarId_729_);
v___x_739_ = lean_st_ref_put(v_a_318_, v___x_738_);
v___x_740_ = lean_ptr_addr(v_k_731_);
v___x_741_ = lean_ptr_addr(v_a_733_);
v___x_742_ = lean_usize_dec_eq(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_752_; 
lean_inc(v_cidx_730_);
lean_inc(v_fvarId_729_);
v_isSharedCheck_752_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; 
v_unused_753_ = lean_ctor_get(v_code_317_, 2);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_755_);
v___x_744_ = v_code_317_;
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
else
{
lean_dec(v_code_317_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 2, v_a_733_);
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_fvarId_729_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_cidx_730_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_a_733_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_747_);
v___x_749_ = v___x_735_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v___x_757_; 
lean_dec(v_a_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_code_317_);
v___x_757_ = v___x_735_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_code_317_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 3);
return v___x_732_;
}
}
case 11:
{
lean_object* v_fvarId_760_; lean_object* v_n_761_; uint8_t v_check_762_; uint8_t v_persistent_763_; lean_object* v_k_764_; lean_object* v___x_765_; 
v_fvarId_760_ = lean_ctor_get(v_code_317_, 0);
v_n_761_ = lean_ctor_get(v_code_317_, 1);
v_check_762_ = lean_ctor_get_uint8(v_code_317_, sizeof(void*)*3);
v_persistent_763_ = lean_ctor_get_uint8(v_code_317_, sizeof(void*)*3 + 1);
v_k_764_ = lean_ctor_get(v_code_317_, 2);
lean_inc_ref(v_k_764_);
v___x_765_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_764_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_792_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_792_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_792_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_792_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; uint8_t v___x_775_; 
v___x_770_ = lean_st_ref_take(v_a_318_);
lean_inc(v_fvarId_760_);
v___x_771_ = l_Lean_FVarIdSet_insert(v___x_770_, v_fvarId_760_);
v___x_772_ = lean_st_ref_put(v_a_318_, v___x_771_);
v___x_773_ = lean_ptr_addr(v_k_764_);
v___x_774_ = lean_ptr_addr(v_a_766_);
v___x_775_ = lean_usize_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_785_; 
lean_inc(v_n_761_);
lean_inc(v_fvarId_760_);
v_isSharedCheck_785_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; 
v_unused_786_ = lean_ctor_get(v_code_317_, 2);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_788_);
v___x_777_ = v_code_317_;
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_code_317_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 2, v_a_766_);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fvarId_760_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_n_761_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_a_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*3, v_check_762_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*3 + 1, v_persistent_763_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_780_);
v___x_782_ = v___x_768_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
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
else
{
lean_object* v___x_790_; 
lean_dec(v_a_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v_code_317_);
v___x_790_ = v___x_768_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_code_317_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 3);
return v___x_765_;
}
}
case 12:
{
lean_object* v_fvarId_793_; lean_object* v_n_794_; uint8_t v_check_795_; uint8_t v_persistent_796_; lean_object* v_objs_x3f_797_; lean_object* v_k_798_; lean_object* v___x_799_; 
v_fvarId_793_ = lean_ctor_get(v_code_317_, 0);
v_n_794_ = lean_ctor_get(v_code_317_, 1);
v_check_795_ = lean_ctor_get_uint8(v_code_317_, sizeof(void*)*4);
v_persistent_796_ = lean_ctor_get_uint8(v_code_317_, sizeof(void*)*4 + 1);
v_objs_x3f_797_ = lean_ctor_get(v_code_317_, 2);
v_k_798_ = lean_ctor_get(v_code_317_, 3);
lean_inc_ref(v_k_798_);
v___x_799_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_798_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_827_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_827_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_827_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_827_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; size_t v___x_807_; size_t v___x_808_; uint8_t v___x_809_; 
v___x_804_ = lean_st_ref_take(v_a_318_);
lean_inc(v_fvarId_793_);
v___x_805_ = l_Lean_FVarIdSet_insert(v___x_804_, v_fvarId_793_);
v___x_806_ = lean_st_ref_put(v_a_318_, v___x_805_);
v___x_807_ = lean_ptr_addr(v_k_798_);
v___x_808_ = lean_ptr_addr(v_a_800_);
v___x_809_ = lean_usize_dec_eq(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
lean_inc(v_objs_x3f_797_);
lean_inc(v_n_794_);
lean_inc(v_fvarId_793_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_820_ = lean_ctor_get(v_code_317_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_code_317_, 2);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_823_);
v___x_811_ = v_code_317_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_code_317_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 3, v_a_800_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fvarId_793_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_n_794_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_objs_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_a_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*4, v_check_795_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*4 + 1, v_persistent_796_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_814_);
v___x_816_ = v___x_802_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v___x_825_; 
lean_dec(v_a_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_code_317_);
v___x_825_ = v___x_802_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_code_317_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 4);
return v___x_799_;
}
}
default: 
{
lean_object* v_fvarId_828_; lean_object* v_k_829_; lean_object* v___x_830_; 
v_fvarId_828_ = lean_ctor_get(v_code_317_, 0);
v_k_829_ = lean_ctor_get(v_code_317_, 1);
lean_inc_ref(v_k_829_);
v___x_830_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_k_829_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_856_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_856_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; uint8_t v___x_840_; 
v___x_835_ = lean_st_ref_take(v_a_318_);
lean_inc(v_fvarId_828_);
v___x_836_ = l_Lean_FVarIdSet_insert(v___x_835_, v_fvarId_828_);
v___x_837_ = lean_st_ref_put(v_a_318_, v___x_836_);
v___x_838_ = lean_ptr_addr(v_k_829_);
v___x_839_ = lean_ptr_addr(v_a_831_);
v___x_840_ = lean_usize_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_850_; 
lean_inc(v_fvarId_828_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_code_317_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; lean_object* v_unused_852_; 
v_unused_851_ = lean_ctor_get(v_code_317_, 1);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_code_317_, 0);
lean_dec(v_unused_852_);
v___x_842_ = v_code_317_;
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_code_317_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_a_831_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fvarId_828_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_831_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_845_);
v___x_847_ = v___x_833_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v___x_854_; 
lean_dec(v_a_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_code_317_);
v___x_854_ = v___x_833_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_code_317_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_317_, 2);
return v___x_830_;
}
}
}
v___jp_324_:
{
if (lean_obj_tag(v___y_325_) == 0)
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v___y_325_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___y_325_, 0);
lean_dec(v_unused_333_);
v___x_327_ = v___y_325_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_dec(v___y_325_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v_code_317_);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_code_317_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_code_317_);
v_a_334_ = lean_ctor_get(v___y_325_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___y_325_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___y_325_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___y_325_);
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
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_316_ = stack[0].m_num;
lean_object* v_code_317_ = stack[1].m_obj;
lean_object* v_a_318_ = stack[2].m_obj;
lean_object* v_a_319_ = stack[3].m_obj;
lean_object* v_a_320_ = stack[4].m_obj;
lean_object* v_a_321_ = stack[5].m_obj;
lean_object* v_a_322_ = stack[6].m_obj;
lean_object* v_res_857_;
v_res_857_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_316_, v_code_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
stack->m_obj
 = v_res_857_;
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t v_pu_858_, lean_object* v_funDecl_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_params_866_; lean_object* v_type_867_; lean_object* v_value_868_; lean_object* v___x_869_; 
v_params_866_ = lean_ctor_get(v_funDecl_859_, 2);
lean_inc_ref(v_params_866_);
v_type_867_ = lean_ctor_get(v_funDecl_859_, 3);
lean_inc_ref(v_type_867_);
v_value_868_ = lean_ctor_get(v_funDecl_859_, 4);
lean_inc_ref(v_value_868_);
v___x_869_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_858_, v_value_868_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_858_, v_funDecl_859_, v_type_867_, v_params_866_, v_a_870_, v_a_862_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_type_867_);
lean_dec_ref(v_params_866_);
lean_dec_ref(v_funDecl_859_);
v_a_872_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_869_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_858_ = stack[0].m_num;
lean_object* v_funDecl_859_ = stack[1].m_obj;
lean_object* v_a_860_ = stack[2].m_obj;
lean_object* v_a_861_ = stack[3].m_obj;
lean_object* v_a_862_ = stack[4].m_obj;
lean_object* v_a_863_ = stack[5].m_obj;
lean_object* v_a_864_ = stack[6].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_858_, v_funDecl_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object* v_pu_881_, lean_object* v_funDecl_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
uint8_t v_pu_boxed_889_; lean_object* v_res_890_; 
v_pu_boxed_889_ = lean_unbox(v_pu_881_);
v_res_890_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_boxed_889_, v_funDecl_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object* v_pu_891_, lean_object* v_i_892_, lean_object* v_as_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v_pu_boxed_900_; lean_object* v_res_901_; 
v_pu_boxed_900_ = lean_unbox(v_pu_891_);
v_res_901_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_900_, v_i_892_, v_as_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* v_pu_902_, lean_object* v_code_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
uint8_t v_pu_boxed_910_; lean_object* v_res_911_; 
v_pu_boxed_910_ = lean_unbox(v_pu_902_);
v_res_911_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_boxed_910_, v_code_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
return v_res_911_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object* v_00_u03b2_912_, lean_object* v_k_913_, lean_object* v_t_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_913_, v_t_914_);
return v___x_915_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_913_ = stack[1].m_obj;
lean_object* v_t_914_ = stack[2].m_obj;
uint8_t v_res_916_;
v_res_916_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_box(0), v_k_913_, v_t_914_);
stack->m_num = v_res_916_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object* v_00_u03b2_917_, lean_object* v_k_918_, lean_object* v_t_919_){
_start:
{
uint8_t v_res_920_; lean_object* v_r_921_; 
v_res_920_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_917_, v_k_918_, v_t_919_);
lean_dec(v_t_919_);
lean_dec(v_k_918_);
v_r_921_ = lean_box(v_res_920_);
return v_r_921_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t v_pu_922_, lean_object* v_as_923_, size_t v_i_924_, size_t v_stop_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_923_, v_i_924_, v_stop_925_, v_b_926_, v___y_927_);
return v___x_933_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_922_ = stack[0].m_num;
lean_object* v_as_923_ = stack[1].m_obj;
size_t v_i_924_ = stack[2].m_num;
size_t v_stop_925_ = stack[3].m_num;
lean_object* v_b_926_ = stack[4].m_obj;
lean_object* v___y_927_ = stack[5].m_obj;
lean_object* v___y_928_ = stack[6].m_obj;
lean_object* v___y_929_ = stack[7].m_obj;
lean_object* v___y_930_ = stack[8].m_obj;
lean_object* v___y_931_ = stack[9].m_obj;
lean_object* v_res_934_;
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_922_, v_as_923_, v_i_924_, v_stop_925_, v_b_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object* v_pu_935_, lean_object* v_as_936_, lean_object* v_i_937_, lean_object* v_stop_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v_pu_boxed_946_; size_t v_i_boxed_947_; size_t v_stop_boxed_948_; lean_object* v_res_949_; 
v_pu_boxed_946_ = lean_unbox(v_pu_935_);
v_i_boxed_947_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_stop_boxed_948_ = lean_unbox_usize(v_stop_938_);
lean_dec(v_stop_938_);
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_946_, v_as_936_, v_i_boxed_947_, v_stop_boxed_948_, v_b_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v_as_936_);
return v_res_949_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object* v_f_950_, lean_object* v_v_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
if (lean_obj_tag(v_v_951_) == 0)
{
lean_object* v_code_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_981_; 
v_code_957_ = lean_ctor_get(v_v_951_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_v_951_);
if (v_isSharedCheck_981_ == 0)
{
v___x_959_ = v_v_951_;
v_isShared_960_ = v_isSharedCheck_981_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_code_957_);
lean_dec(v_v_951_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_981_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; 
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
v___x_961_ = lean_apply_6(v_f_950_, v_code_957_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_972_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_972_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_a_962_);
v___x_967_ = v___x_959_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_del_object(v___x_959_);
v_a_973_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_961_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_961_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
else
{
lean_object* v___x_982_; 
lean_dec_ref(v_f_950_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_v_951_);
return v___x_982_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_950_ = stack[0].m_obj;
lean_object* v_v_951_ = stack[1].m_obj;
lean_object* v___y_952_ = stack[2].m_obj;
lean_object* v___y_953_ = stack[3].m_obj;
lean_object* v___y_954_ = stack[4].m_obj;
lean_object* v___y_955_ = stack[5].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_950_, v_v_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object* v_f_984_, lean_object* v_v_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_984_, v_v_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_991_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t v_pu_992_, lean_object* v_f_993_, lean_object* v_v_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_993_, v_v_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1000_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_992_ = stack[0].m_num;
lean_object* v_f_993_ = stack[1].m_obj;
lean_object* v_v_994_ = stack[2].m_obj;
lean_object* v___y_995_ = stack[3].m_obj;
lean_object* v___y_996_ = stack[4].m_obj;
lean_object* v___y_997_ = stack[5].m_obj;
lean_object* v___y_998_ = stack[6].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_992_, v_f_993_, v_v_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object* v_pu_1002_, lean_object* v_f_1003_, lean_object* v_v_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
uint8_t v_pu_boxed_1010_; lean_object* v_res_1011_; 
v_pu_boxed_1010_ = lean_unbox(v_pu_1002_);
v_res_1011_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_1010_, v_f_1003_, v_v_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1011_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object* v___x_1012_, uint8_t v_pu_1013_, lean_object* v_code_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_st_mk_ref(v___x_1012_);
v___x_1021_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1013_, v_code_1014_, v___x_1020_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_st_ref_get(v___x_1020_);
lean_dec(v___x_1020_);
lean_dec(v___x_1026_);
if (v_isShared_1025_ == 0)
{
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1022_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_dec(v___x_1020_);
return v___x_1021_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1012_ = stack[0].m_obj;
uint8_t v_pu_1013_ = stack[1].m_num;
lean_object* v_code_1014_ = stack[2].m_obj;
lean_object* v___y_1015_ = stack[3].m_obj;
lean_object* v___y_1016_ = stack[4].m_obj;
lean_object* v___y_1017_ = stack[5].m_obj;
lean_object* v___y_1018_ = stack[6].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(v___x_1012_, v_pu_1013_, v_code_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object* v___x_1032_, lean_object* v_pu_1033_, lean_object* v_code_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_pu_boxed_1040_; lean_object* v_res_1041_; 
v_pu_boxed_1040_ = lean_unbox(v_pu_1033_);
v_res_1041_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(v___x_1032_, v_pu_boxed_1040_, v_code_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1041_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t v_pu_1042_, lean_object* v_decl_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_toSignature_1049_; lean_object* v_value_1050_; uint8_t v_recursive_1051_; lean_object* v_inlineAttr_x3f_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1079_; 
v_toSignature_1049_ = lean_ctor_get(v_decl_1043_, 0);
v_value_1050_ = lean_ctor_get(v_decl_1043_, 1);
v_recursive_1051_ = lean_ctor_get_uint8(v_decl_1043_, sizeof(void*)*3);
v_inlineAttr_x3f_1052_ = lean_ctor_get(v_decl_1043_, 2);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_decl_1043_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1054_ = v_decl_1043_;
v_isShared_1055_ = v_isSharedCheck_1079_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_inlineAttr_x3f_1052_);
lean_inc(v_value_1050_);
lean_inc(v_toSignature_1049_);
lean_dec(v_decl_1043_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1079_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_box(1);
v___x_1057_ = lean_box(v_pu_1042_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1058_, 0, v___x_1056_);
lean_closure_set(v___f_1058_, 1, v___x_1057_);
v___x_1059_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_1058_, v_value_1050_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1070_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_a_1060_);
v___x_1065_ = v___x_1054_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_toSignature_1049_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_a_1060_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_inlineAttr_x3f_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*3, v_recursive_1051_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_1054_);
lean_dec(v_inlineAttr_x3f_1052_);
lean_dec_ref(v_toSignature_1049_);
v_a_1071_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1059_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1059_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_elimDeadVars_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1042_ = stack[0].m_num;
lean_object* v_decl_1043_ = stack[1].m_obj;
lean_object* v_a_1044_ = stack[2].m_obj;
lean_object* v_a_1045_ = stack[3].m_obj;
lean_object* v_a_1046_ = stack[4].m_obj;
lean_object* v_a_1047_ = stack[5].m_obj;
lean_object* v_res_1080_;
v_res_1080_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v_pu_1042_, v_decl_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
stack->m_obj
 = v_res_1080_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object* v_pu_1081_, lean_object* v_decl_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
uint8_t v_pu_boxed_1088_; lean_object* v_res_1089_; 
v_pu_boxed_1088_ = lean_unbox(v_pu_1081_);
v_res_1089_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v_pu_boxed_1088_, v_decl_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
return v_res_1089_;
}
}
lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t v_phase_1093_, lean_object* v_occurrence_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1095_ = ((lean_object*)(l_Lean_Compiler_LCNF_elimDeadVars___closed__1));
v___x_1096_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1093_);
v___x_1097_ = lean_box(v___x_1096_);
v___x_1098_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed), 7, 1);
lean_closure_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1095_, v_phase_1093_, v___x_1098_, v_occurrence_1094_);
return v___x_1099_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_elimDeadVars_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1093_ = stack[0].m_num;
lean_object* v_occurrence_1094_ = stack[1].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_1093_, v_occurrence_1094_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object* v_phase_1101_, lean_object* v_occurrence_1102_){
_start:
{
uint8_t v_phase_boxed_1103_; lean_object* v_res_1104_; 
v_phase_boxed_1103_ = lean_unbox(v_phase_1101_);
v_res_1104_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_1103_, v_occurrence_1102_);
return v_res_1104_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1176_ = 1;
v___x_1177_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1178_ = l_Lean_registerTraceClass(v___x_1175_, v___x_1176_, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1179_;
v_res_1179_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
return v_res_1181_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ElimDead(builtin);
}
#ifdef __cplusplus
}
#endif
