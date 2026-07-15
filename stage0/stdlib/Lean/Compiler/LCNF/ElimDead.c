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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t v_pu_5_, lean_object* v_s_6_, lean_object* v_arg_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_s_6_, v_arg_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object* v_pu_9_, lean_object* v_s_10_, lean_object* v_arg_11_){
_start:
{
uint8_t v_pu_boxed_12_; lean_object* v_res_13_; 
v_pu_boxed_12_ = lean_unbox(v_pu_9_);
v_res_13_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(v_pu_boxed_12_, v_s_10_, v_arg_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object* v_as_14_, size_t v_i_15_, size_t v_stop_16_, lean_object* v_b_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_eq(v_i_15_, v_stop_16_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; size_t v___x_21_; size_t v___x_22_; 
v___x_19_ = lean_array_uget_borrowed(v_as_14_, v_i_15_);
lean_inc(v___x_19_);
v___x_20_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_b_17_, v___x_19_);
v___x_21_ = ((size_t)1ULL);
v___x_22_ = lean_usize_add(v_i_15_, v___x_21_);
v_i_15_ = v___x_22_;
v_b_17_ = v___x_20_;
goto _start;
}
else
{
return v_b_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object* v_as_24_, lean_object* v_i_25_, lean_object* v_stop_26_, lean_object* v_b_27_){
_start:
{
size_t v_i_boxed_28_; size_t v_stop_boxed_29_; lean_object* v_res_30_; 
v_i_boxed_28_ = lean_unbox_usize(v_i_25_);
lean_dec(v_i_25_);
v_stop_boxed_29_ = lean_unbox_usize(v_stop_26_);
lean_dec(v_stop_26_);
v_res_30_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_24_, v_i_boxed_28_, v_stop_boxed_29_, v_b_27_);
lean_dec_ref(v_as_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t v_pu_31_, lean_object* v_s_32_, lean_object* v_args_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_array_get_size(v_args_33_);
v___x_36_ = lean_nat_dec_lt(v___x_34_, v___x_35_);
if (v___x_36_ == 0)
{
return v_s_32_;
}
else
{
uint8_t v___x_37_; 
v___x_37_ = lean_nat_dec_le(v___x_35_, v___x_35_);
if (v___x_37_ == 0)
{
if (v___x_36_ == 0)
{
return v_s_32_;
}
else
{
size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; 
v___x_38_ = ((size_t)0ULL);
v___x_39_ = lean_usize_of_nat(v___x_35_);
v___x_40_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_33_, v___x_38_, v___x_39_, v_s_32_);
return v___x_40_;
}
}
else
{
size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((size_t)0ULL);
v___x_42_ = lean_usize_of_nat(v___x_35_);
v___x_43_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_33_, v___x_41_, v___x_42_, v_s_32_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* v_pu_44_, lean_object* v_s_45_, lean_object* v_args_46_){
_start:
{
uint8_t v_pu_boxed_47_; lean_object* v_res_48_; 
v_pu_boxed_47_ = lean_unbox(v_pu_44_);
v_res_48_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_boxed_47_, v_s_45_, v_args_46_);
lean_dec_ref(v_args_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t v_pu_49_, lean_object* v_as_50_, size_t v_i_51_, size_t v_stop_52_, lean_object* v_b_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_50_, v_i_51_, v_stop_52_, v_b_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* v_pu_55_, lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_stop_58_, lean_object* v_b_59_){
_start:
{
uint8_t v_pu_boxed_60_; size_t v_i_boxed_61_; size_t v_stop_boxed_62_; lean_object* v_res_63_; 
v_pu_boxed_60_ = lean_unbox(v_pu_55_);
v_i_boxed_61_ = lean_unbox_usize(v_i_57_);
lean_dec(v_i_57_);
v_stop_boxed_62_ = lean_unbox_usize(v_stop_58_);
lean_dec(v_stop_58_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_60_, v_as_56_, v_i_boxed_61_, v_stop_boxed_62_, v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t v_pu_64_, lean_object* v_s_65_, lean_object* v_e_66_){
_start:
{
switch(lean_obj_tag(v_e_66_))
{
case 2:
{
lean_object* v_struct_67_; lean_object* v___x_68_; 
v_struct_67_ = lean_ctor_get(v_e_66_, 2);
lean_inc(v_struct_67_);
lean_dec_ref_known(v_e_66_, 3);
v___x_68_ = l_Lean_FVarIdSet_insert(v_s_65_, v_struct_67_);
return v___x_68_;
}
case 3:
{
lean_object* v_args_69_; lean_object* v___x_70_; 
v_args_69_ = lean_ctor_get(v_e_66_, 2);
lean_inc_ref(v_args_69_);
lean_dec_ref_known(v_e_66_, 3);
v___x_70_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_69_);
lean_dec_ref(v_args_69_);
return v___x_70_;
}
case 4:
{
lean_object* v_fvarId_71_; lean_object* v_args_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_fvarId_71_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_fvarId_71_);
v_args_72_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_72_);
lean_dec_ref_known(v_e_66_, 2);
v___x_73_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_71_);
v___x_74_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v___x_73_, v_args_72_);
lean_dec_ref(v_args_72_);
return v___x_74_;
}
case 5:
{
lean_object* v_args_75_; lean_object* v___x_76_; 
v_args_75_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_75_);
lean_dec_ref_known(v_e_66_, 2);
v___x_76_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_75_);
lean_dec_ref(v_args_75_);
return v___x_76_;
}
case 6:
{
lean_object* v_var_77_; lean_object* v___x_78_; 
v_var_77_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_var_77_);
lean_dec_ref_known(v_e_66_, 2);
v___x_78_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_77_);
return v___x_78_;
}
case 7:
{
lean_object* v_var_79_; lean_object* v___x_80_; 
v_var_79_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_var_79_);
lean_dec_ref_known(v_e_66_, 2);
v___x_80_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_79_);
return v___x_80_;
}
case 8:
{
lean_object* v_var_81_; lean_object* v___x_82_; 
v_var_81_ = lean_ctor_get(v_e_66_, 2);
lean_inc(v_var_81_);
lean_dec_ref_known(v_e_66_, 3);
v___x_82_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_81_);
return v___x_82_;
}
case 9:
{
lean_object* v_args_83_; lean_object* v___x_84_; 
v_args_83_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_83_);
lean_dec_ref_known(v_e_66_, 2);
v___x_84_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_83_);
lean_dec_ref(v_args_83_);
return v___x_84_;
}
case 10:
{
lean_object* v_args_85_; lean_object* v___x_86_; 
v_args_85_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_85_);
lean_dec_ref_known(v_e_66_, 2);
v___x_86_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_85_);
lean_dec_ref(v_args_85_);
return v___x_86_;
}
case 11:
{
lean_object* v_var_87_; lean_object* v___x_88_; 
v_var_87_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_var_87_);
lean_dec_ref_known(v_e_66_, 2);
v___x_88_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_87_);
return v___x_88_;
}
case 12:
{
lean_object* v_var_89_; lean_object* v_args_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_var_89_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_var_89_);
v_args_90_ = lean_ctor_get(v_e_66_, 2);
lean_inc_ref(v_args_90_);
lean_dec_ref_known(v_e_66_, 3);
v___x_91_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_89_);
v___x_92_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v___x_91_, v_args_90_);
lean_dec_ref(v_args_90_);
return v___x_92_;
}
case 13:
{
lean_object* v_fvarId_93_; lean_object* v___x_94_; 
v_fvarId_93_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_fvarId_93_);
lean_dec_ref_known(v_e_66_, 2);
v___x_94_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_93_);
return v___x_94_;
}
case 14:
{
lean_object* v_fvarId_95_; lean_object* v___x_96_; 
v_fvarId_95_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_fvarId_95_);
lean_dec_ref_known(v_e_66_, 1);
v___x_96_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_95_);
return v___x_96_;
}
case 15:
{
lean_object* v_fvarId_97_; lean_object* v___x_98_; 
v_fvarId_97_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_fvarId_97_);
lean_dec_ref_known(v_e_66_, 1);
v___x_98_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_97_);
return v___x_98_;
}
default: 
{
lean_dec(v_e_66_);
return v_s_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object* v_pu_99_, lean_object* v_s_100_, lean_object* v_e_101_){
_start:
{
uint8_t v_pu_boxed_102_; lean_object* v_res_103_; 
v_pu_boxed_102_ = lean_unbox(v_pu_99_);
v_res_103_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_boxed_102_, v_s_100_, v_e_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object* v_arg_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_107_ = lean_st_ref_take(v_a_105_);
v___x_108_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_107_, v_arg_104_);
v___x_109_ = lean_st_ref_set(v_a_105_, v___x_108_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object* v_arg_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(v_arg_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t v_pu_116_, lean_object* v_arg_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = lean_st_ref_take(v_a_118_);
v___x_125_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_124_, v_arg_117_);
v___x_126_ = lean_st_ref_set(v_a_118_, v___x_125_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object* v_pu_129_, lean_object* v_arg_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_pu_boxed_137_; lean_object* v_res_138_; 
v_pu_boxed_137_ = lean_unbox(v_pu_129_);
v_res_138_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(v_pu_boxed_137_, v_arg_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t v_pu_139_, lean_object* v_e_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = lean_st_ref_take(v_a_141_);
v___x_144_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_139_, v___x_143_, v_e_140_);
v___x_145_ = lean_st_ref_set(v_a_141_, v___x_144_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object* v_pu_148_, lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
uint8_t v_pu_boxed_152_; lean_object* v_res_153_; 
v_pu_boxed_152_ = lean_unbox(v_pu_148_);
v_res_153_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(v_pu_boxed_152_, v_e_149_, v_a_150_);
lean_dec(v_a_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t v_pu_154_, lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_162_ = lean_st_ref_take(v_a_156_);
v___x_163_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_154_, v___x_162_, v_e_155_);
v___x_164_ = lean_st_ref_set(v_a_156_, v___x_163_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object* v_pu_167_, lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
uint8_t v_pu_boxed_175_; lean_object* v_res_176_; 
v_pu_boxed_175_ = lean_unbox(v_pu_167_);
v_res_176_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(v_pu_boxed_175_, v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object* v_fvarId_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = lean_st_ref_take(v_a_178_);
v___x_181_ = l_Lean_FVarIdSet_insert(v___x_180_, v_fvarId_177_);
v___x_182_ = lean_st_ref_set(v_a_178_, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object* v_fvarId_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(v_fvarId_185_, v_a_186_);
lean_dec(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object* v_fvarId_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = lean_st_ref_take(v_a_190_);
v___x_197_ = l_Lean_FVarIdSet_insert(v___x_196_, v_fvarId_189_);
v___x_198_ = lean_st_ref_set(v_a_190_, v___x_197_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object* v_fvarId_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(v_fvarId_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
return v_res_208_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t v_pu_209_, lean_object* v_val_210_){
_start:
{
if (v_pu_209_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
else
{
switch(lean_obj_tag(v_val_210_))
{
case 1:
{
uint8_t v___x_212_; 
v___x_212_ = 1;
return v___x_212_;
}
case 4:
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
case 9:
{
lean_object* v_args_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_args_214_ = lean_ctor_get(v_val_210_, 1);
v___x_215_ = lean_array_get_size(v_args_214_);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_nat_dec_eq(v___x_215_, v___x_216_);
return v___x_217_;
}
default: 
{
uint8_t v___x_218_; 
v___x_218_ = 1;
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object* v_pu_219_, lean_object* v_val_220_){
_start:
{
uint8_t v_pu_boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v_pu_boxed_221_ = lean_unbox(v_pu_219_);
v_res_222_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_boxed_221_, v_val_220_);
lean_dec(v_val_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object* v_as_224_, size_t v_i_225_, size_t v_stop_226_, lean_object* v_b_227_, lean_object* v___y_228_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_usize_dec_eq(v_i_225_, v_stop_226_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; 
v___x_231_ = lean_st_ref_take(v___y_228_);
v___x_232_ = lean_array_uget_borrowed(v_as_224_, v_i_225_);
lean_inc(v___x_232_);
v___x_233_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_231_, v___x_232_);
v___x_234_ = lean_st_ref_set(v___y_228_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_i_225_, v___x_236_);
v_i_225_ = v___x_237_;
v_b_227_ = v___x_235_;
goto _start;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v_b_227_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object* v_as_240_, lean_object* v_i_241_, lean_object* v_stop_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; lean_object* v_res_248_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_241_);
lean_dec(v_i_241_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_242_);
lean_dec(v_stop_242_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_240_, v_i_boxed_246_, v_stop_boxed_247_, v_b_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v_as_240_);
return v_res_248_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object* v_k_249_, lean_object* v_t_250_){
_start:
{
if (lean_obj_tag(v_t_250_) == 0)
{
lean_object* v_k_251_; lean_object* v_l_252_; lean_object* v_r_253_; uint8_t v___x_254_; 
v_k_251_ = lean_ctor_get(v_t_250_, 1);
v_l_252_ = lean_ctor_get(v_t_250_, 3);
v_r_253_ = lean_ctor_get(v_t_250_, 4);
v___x_254_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_249_, v_k_251_);
switch(v___x_254_)
{
case 0:
{
v_t_250_ = v_l_252_;
goto _start;
}
case 1:
{
uint8_t v___x_256_; 
v___x_256_ = 1;
return v___x_256_;
}
default: 
{
v_t_250_ = v_r_253_;
goto _start;
}
}
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object* v_k_259_, lean_object* v_t_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_259_, v_t_260_);
lean_dec(v_t_260_);
lean_dec(v_k_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t v_pu_263_, lean_object* v_i_264_, lean_object* v_as_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_array_get_size(v_as_265_);
v___x_273_ = lean_nat_dec_lt(v_i_264_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_i_264_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_as_265_);
return v___x_274_;
}
else
{
lean_object* v_a_275_; lean_object* v___y_277_; 
v_a_275_ = lean_array_fget_borrowed(v_as_265_, v_i_264_);
switch(lean_obj_tag(v_a_275_))
{
case 0:
{
lean_object* v_code_299_; 
v_code_299_ = lean_ctor_get(v_a_275_, 2);
lean_inc_ref(v_code_299_);
v___y_277_ = v_code_299_;
goto v___jp_276_;
}
case 1:
{
lean_object* v_code_300_; 
v_code_300_ = lean_ctor_get(v_a_275_, 1);
lean_inc_ref(v_code_300_);
v___y_277_ = v_code_300_;
goto v___jp_276_;
}
default: 
{
lean_object* v_code_301_; 
v_code_301_ = lean_ctor_get(v_a_275_, 0);
lean_inc_ref(v_code_301_);
v___y_277_ = v_code_301_;
goto v___jp_276_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_263_, v___y_277_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; size_t v___x_281_; size_t v___x_282_; uint8_t v___x_283_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
lean_inc(v_a_275_);
v___x_280_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_275_, v_a_279_);
v___x_281_ = lean_ptr_addr(v_a_275_);
v___x_282_ = lean_ptr_addr(v___x_280_);
v___x_283_ = lean_usize_dec_eq(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_264_, v___x_284_);
v___x_286_ = lean_array_fset(v_as_265_, v_i_264_, v___x_280_);
lean_dec(v_i_264_);
v_i_264_ = v___x_285_;
v_as_265_ = v___x_286_;
goto _start;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref(v___x_280_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_i_264_, v___x_288_);
lean_dec(v_i_264_);
v_i_264_ = v___x_289_;
goto _start;
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_as_265_);
lean_dec(v_i_264_);
v_a_291_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_278_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_278_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t v_pu_302_, lean_object* v_code_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___y_311_; 
switch(lean_obj_tag(v_code_303_))
{
case 0:
{
lean_object* v_decl_328_; lean_object* v_k_329_; lean_object* v___x_330_; 
v_decl_328_ = lean_ctor_get(v_code_303_, 0);
v_k_329_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_329_);
v___x_330_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_329_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_381_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_381_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_381_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_381_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_fvarId_336_; lean_object* v_value_337_; uint8_t v___y_361_; uint8_t v___x_379_; 
v___x_335_ = lean_st_ref_get(v_a_304_);
v_fvarId_336_ = lean_ctor_get(v_decl_328_, 0);
v_value_337_ = lean_ctor_get(v_decl_328_, 3);
v___x_379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_336_, v___x_335_);
lean_dec(v___x_335_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_302_, v_value_337_);
if (v___x_380_ == 0)
{
goto v___jp_338_;
}
else
{
v___y_361_ = v___x_379_;
goto v___jp_360_;
}
}
else
{
v___y_361_ = v___x_379_;
goto v___jp_360_;
}
v___jp_338_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; uint8_t v___x_344_; 
v___x_339_ = lean_st_ref_take(v_a_304_);
lean_inc(v_value_337_);
v___x_340_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_302_, v___x_339_, v_value_337_);
v___x_341_ = lean_st_ref_set(v_a_304_, v___x_340_);
v___x_342_ = lean_ptr_addr(v_k_329_);
v___x_343_ = lean_ptr_addr(v_a_331_);
v___x_344_ = lean_usize_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_354_; 
lean_inc_ref(v_decl_328_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_355_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_356_);
v___x_346_ = v_code_303_;
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_code_303_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_a_331_);
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_decl_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_a_331_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_349_);
v___x_351_ = v___x_333_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_code_303_);
v___x_358_ = v___x_333_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_code_303_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
v___jp_360_:
{
if (v___y_361_ == 0)
{
lean_object* v___x_362_; 
lean_inc_ref(v_decl_328_);
lean_del_object(v___x_333_);
lean_dec_ref_known(v_code_303_, 2);
v___x_362_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_302_, v_decl_328_, v_a_306_);
lean_dec_ref(v_decl_328_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_370_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_a_331_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_331_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_331_);
v_a_371_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_362_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
goto v___jp_338_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_330_;
}
}
case 1:
{
lean_object* v_decl_382_; lean_object* v_k_383_; lean_object* v___x_384_; 
v_decl_382_ = lean_ctor_get(v_code_303_, 0);
v_k_383_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_383_);
v___x_384_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_383_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v_fvarId_387_; uint8_t v___x_388_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = lean_st_ref_get(v_a_304_);
v_fvarId_387_ = lean_ctor_get(v_decl_382_, 0);
v___x_388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_387_, v___x_386_);
lean_dec(v___x_386_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; lean_object* v___x_390_; 
lean_inc_ref(v_decl_382_);
lean_dec_ref_known(v_code_303_, 2);
v___x_389_ = 1;
v___x_390_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_302_, v_decl_382_, v___x_389_, v_a_306_);
lean_dec_ref(v_decl_382_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_398_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v_a_385_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_385_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_385_);
v_a_399_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_390_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_390_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_407_; 
lean_inc_ref(v_decl_382_);
v___x_407_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_302_, v_decl_382_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_435_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_435_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_435_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_435_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint8_t v___y_413_; size_t v___x_429_; size_t v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_ptr_addr(v_k_383_);
v___x_430_ = lean_ptr_addr(v_a_385_);
v___x_431_ = lean_usize_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
v___y_413_ = v___x_431_;
goto v___jp_412_;
}
else
{
size_t v___x_432_; size_t v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_ptr_addr(v_decl_382_);
v___x_433_ = lean_ptr_addr(v_a_408_);
v___x_434_ = lean_usize_dec_eq(v___x_432_, v___x_433_);
v___y_413_ = v___x_434_;
goto v___jp_412_;
}
v___jp_412_:
{
if (v___y_413_ == 0)
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; 
v_unused_424_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_425_);
v___x_415_ = v_code_303_;
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_code_303_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_a_385_);
lean_ctor_set(v___x_415_, 0, v_a_408_);
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_a_385_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_418_);
v___x_420_ = v___x_410_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v___x_427_; 
lean_dec(v_a_408_);
lean_dec(v_a_385_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_code_303_);
v___x_427_ = v___x_410_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_code_303_);
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
lean_dec(v_a_385_);
lean_dec_ref_known(v_code_303_, 2);
v_a_436_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_407_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_407_);
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
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_384_;
}
}
case 2:
{
lean_object* v_decl_444_; lean_object* v_k_445_; lean_object* v___x_446_; 
v_decl_444_ = lean_ctor_get(v_code_303_, 0);
v_k_445_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_445_);
v___x_446_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_445_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v_fvarId_449_; uint8_t v___x_450_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = lean_st_ref_get(v_a_304_);
v_fvarId_449_ = lean_ctor_get(v_decl_444_, 0);
v___x_450_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_449_, v___x_448_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; lean_object* v___x_452_; 
lean_inc_ref(v_decl_444_);
lean_dec_ref_known(v_code_303_, 2);
v___x_451_ = 1;
v___x_452_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_302_, v_decl_444_, v___x_451_, v_a_306_);
lean_dec_ref(v_decl_444_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v___x_452_, 0);
lean_dec(v_unused_460_);
v___x_454_ = v___x_452_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_dec(v___x_452_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_a_447_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_447_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_a_447_);
v_a_461_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_452_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_452_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v___x_469_; 
lean_inc_ref(v_decl_444_);
v___x_469_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_302_, v_decl_444_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_497_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_497_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_497_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_497_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___y_475_; size_t v___x_491_; size_t v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_ptr_addr(v_k_445_);
v___x_492_ = lean_ptr_addr(v_a_447_);
v___x_493_ = lean_usize_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
v___y_475_ = v___x_493_;
goto v___jp_474_;
}
else
{
size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_ptr_addr(v_decl_444_);
v___x_495_ = lean_ptr_addr(v_a_470_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
v___y_475_ = v___x_496_;
goto v___jp_474_;
}
v___jp_474_:
{
if (v___y_475_ == 0)
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_485_; 
v_isSharedCheck_485_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; 
v_unused_486_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_487_);
v___x_477_ = v_code_303_;
v_isShared_478_ = v_isSharedCheck_485_;
goto v_resetjp_476_;
}
else
{
lean_dec(v_code_303_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_485_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v_a_447_);
lean_ctor_set(v___x_477_, 0, v_a_470_);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_470_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_a_447_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_480_);
v___x_482_ = v___x_472_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v___x_489_; 
lean_dec(v_a_470_);
lean_dec(v_a_447_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v_code_303_);
v___x_489_ = v___x_472_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_code_303_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_a_447_);
lean_dec_ref_known(v_code_303_, 2);
v_a_498_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_469_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_469_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_446_;
}
}
case 3:
{
lean_object* v_fvarId_506_; lean_object* v_args_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_fvarId_506_ = lean_ctor_get(v_code_303_, 0);
v_args_507_ = lean_ctor_get(v_code_303_, 1);
v___x_508_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_506_);
v___x_509_ = l_Lean_FVarIdSet_insert(v___x_508_, v_fvarId_506_);
v___x_510_ = lean_st_ref_set(v_a_304_, v___x_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_array_get_size(v_args_507_);
v___x_513_ = lean_nat_dec_lt(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_code_303_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_box(0);
v___x_516_ = lean_nat_dec_le(v___x_512_, v___x_512_);
if (v___x_516_ == 0)
{
if (v___x_513_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_code_303_);
return v___x_517_;
}
else
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_518_ = ((size_t)0ULL);
v___x_519_ = lean_usize_of_nat(v___x_512_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_507_, v___x_518_, v___x_519_, v___x_515_, v_a_304_);
v___y_311_ = v___x_520_;
goto v___jp_310_;
}
}
else
{
size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v___x_521_ = ((size_t)0ULL);
v___x_522_ = lean_usize_of_nat(v___x_512_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_507_, v___x_521_, v___x_522_, v___x_515_, v_a_304_);
v___y_311_ = v___x_523_;
goto v___jp_310_;
}
}
}
case 4:
{
lean_object* v_cases_524_; lean_object* v_typeName_525_; lean_object* v_resultType_526_; lean_object* v_discr_527_; lean_object* v_alts_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_570_; 
v_cases_524_ = lean_ctor_get(v_code_303_, 0);
lean_inc_ref(v_cases_524_);
v_typeName_525_ = lean_ctor_get(v_cases_524_, 0);
v_resultType_526_ = lean_ctor_get(v_cases_524_, 1);
v_discr_527_ = lean_ctor_get(v_cases_524_, 2);
v_alts_528_ = lean_ctor_get(v_cases_524_, 3);
v_isSharedCheck_570_ = !lean_is_exclusive(v_cases_524_);
if (v_isSharedCheck_570_ == 0)
{
v___x_530_ = v_cases_524_;
v_isShared_531_ = v_isSharedCheck_570_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_alts_528_);
lean_inc(v_discr_527_);
lean_inc(v_resultType_526_);
lean_inc(v_typeName_525_);
lean_dec(v_cases_524_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_570_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_528_);
v___x_533_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_302_, v___x_532_, v_alts_528_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_561_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_561_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_561_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_561_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; size_t v___x_541_; size_t v___x_542_; uint8_t v___x_543_; 
v___x_538_ = lean_st_ref_take(v_a_304_);
lean_inc(v_discr_527_);
v___x_539_ = l_Lean_FVarIdSet_insert(v___x_538_, v_discr_527_);
v___x_540_ = lean_st_ref_set(v_a_304_, v___x_539_);
v___x_541_ = lean_ptr_addr(v_alts_528_);
lean_dec_ref(v_alts_528_);
v___x_542_ = lean_ptr_addr(v_a_534_);
v___x_543_ = lean_usize_dec_eq(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_556_; 
v_isSharedCheck_556_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_557_);
v___x_545_ = v_code_303_;
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
else
{
lean_dec(v_code_303_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 3, v_a_534_);
v___x_548_ = v___x_530_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_typeName_525_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_resultType_526_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_discr_527_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_a_534_);
v___x_548_ = v_reuseFailAlloc_555_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_550_);
v___x_552_ = v___x_536_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
else
{
lean_object* v___x_559_; 
lean_dec(v_a_534_);
lean_del_object(v___x_530_);
lean_dec(v_discr_527_);
lean_dec_ref(v_resultType_526_);
lean_dec(v_typeName_525_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_code_303_);
v___x_559_ = v___x_536_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_code_303_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_del_object(v___x_530_);
lean_dec_ref(v_alts_528_);
lean_dec(v_discr_527_);
lean_dec_ref(v_resultType_526_);
lean_dec(v_typeName_525_);
lean_dec_ref_known(v_code_303_, 1);
v_a_562_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_533_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_533_);
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
lean_object* v_fvarId_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_fvarId_571_ = lean_ctor_get(v_code_303_, 0);
v___x_572_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_571_);
v___x_573_ = l_Lean_FVarIdSet_insert(v___x_572_, v_fvarId_571_);
v___x_574_ = lean_st_ref_set(v_a_304_, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_code_303_);
return v___x_575_;
}
case 6:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_code_303_);
return v___x_576_;
}
case 7:
{
lean_object* v_fvarId_577_; lean_object* v_i_578_; lean_object* v_y_579_; lean_object* v_k_580_; lean_object* v___x_581_; 
v_fvarId_577_ = lean_ctor_get(v_code_303_, 0);
v_i_578_ = lean_ctor_get(v_code_303_, 1);
v_y_579_ = lean_ctor_get(v_code_303_, 2);
v_k_580_ = lean_ctor_get(v_code_303_, 3);
lean_inc_ref(v_k_580_);
v___x_581_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_580_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_614_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_614_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_614_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_614_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_st_ref_get(v_a_304_);
v___x_587_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_577_, v___x_586_);
lean_dec(v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_589_; 
lean_dec_ref_known(v_code_303_, 4);
if (v_isShared_585_ == 0)
{
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_582_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; size_t v___x_594_; size_t v___x_595_; uint8_t v___x_596_; 
v___x_591_ = lean_st_ref_take(v_a_304_);
lean_inc(v_y_579_);
v___x_592_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_591_, v_y_579_);
v___x_593_ = lean_st_ref_set(v_a_304_, v___x_592_);
v___x_594_ = lean_ptr_addr(v_k_580_);
v___x_595_ = lean_ptr_addr(v_a_582_);
v___x_596_ = lean_usize_dec_eq(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
lean_inc(v_y_579_);
lean_inc(v_i_578_);
lean_inc(v_fvarId_577_);
v_isSharedCheck_606_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; lean_object* v_unused_609_; lean_object* v_unused_610_; 
v_unused_607_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_609_);
v_unused_610_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_610_);
v___x_598_ = v_code_303_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_dec(v_code_303_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 3, v_a_582_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_fvarId_577_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_i_578_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_y_579_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_a_582_);
v___x_601_ = v_reuseFailAlloc_605_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_601_);
v___x_603_ = v___x_584_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec(v_a_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_code_303_);
v___x_612_ = v___x_584_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_code_303_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 4);
return v___x_581_;
}
}
case 8:
{
lean_object* v_fvarId_615_; lean_object* v_i_616_; lean_object* v_y_617_; lean_object* v_k_618_; lean_object* v___x_619_; 
v_fvarId_615_ = lean_ctor_get(v_code_303_, 0);
v_i_616_ = lean_ctor_get(v_code_303_, 1);
v_y_617_ = lean_ctor_get(v_code_303_, 2);
v_k_618_ = lean_ctor_get(v_code_303_, 3);
lean_inc_ref(v_k_618_);
v___x_619_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_618_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_652_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_652_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_652_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_652_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_st_ref_get(v_a_304_);
v___x_625_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_615_, v___x_624_);
lean_dec(v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref_known(v_code_303_, 4);
if (v_isShared_623_ == 0)
{
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_620_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_629_ = lean_st_ref_take(v_a_304_);
lean_inc(v_y_617_);
v___x_630_ = l_Lean_FVarIdSet_insert(v___x_629_, v_y_617_);
v___x_631_ = lean_st_ref_set(v_a_304_, v___x_630_);
v___x_632_ = lean_ptr_addr(v_k_618_);
v___x_633_ = lean_ptr_addr(v_a_620_);
v___x_634_ = lean_usize_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_644_; 
lean_inc(v_y_617_);
lean_inc(v_i_616_);
lean_inc(v_fvarId_615_);
v_isSharedCheck_644_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_645_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_648_);
v___x_636_ = v_code_303_;
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
else
{
lean_dec(v_code_303_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 3, v_a_620_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fvarId_615_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_i_616_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_y_617_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_a_620_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_639_);
v___x_641_ = v___x_622_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v_a_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_code_303_);
v___x_650_ = v___x_622_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_code_303_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 4);
return v___x_619_;
}
}
case 9:
{
lean_object* v_fvarId_653_; lean_object* v_i_654_; lean_object* v_offset_655_; lean_object* v_y_656_; lean_object* v_ty_657_; lean_object* v_k_658_; lean_object* v___x_659_; 
v_fvarId_653_ = lean_ctor_get(v_code_303_, 0);
v_i_654_ = lean_ctor_get(v_code_303_, 1);
v_offset_655_ = lean_ctor_get(v_code_303_, 2);
v_y_656_ = lean_ctor_get(v_code_303_, 3);
v_ty_657_ = lean_ctor_get(v_code_303_, 4);
v_k_658_ = lean_ctor_get(v_code_303_, 5);
lean_inc_ref(v_k_658_);
v___x_659_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_658_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_694_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_694_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_694_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_694_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_st_ref_get(v_a_304_);
v___x_665_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_653_, v___x_664_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref_known(v_code_303_, 6);
if (v_isShared_663_ == 0)
{
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_660_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v___x_672_; size_t v___x_673_; uint8_t v___x_674_; 
v___x_669_ = lean_st_ref_take(v_a_304_);
lean_inc(v_y_656_);
v___x_670_ = l_Lean_FVarIdSet_insert(v___x_669_, v_y_656_);
v___x_671_ = lean_st_ref_set(v_a_304_, v___x_670_);
v___x_672_ = lean_ptr_addr(v_k_658_);
v___x_673_ = lean_ptr_addr(v_a_660_);
v___x_674_ = lean_usize_dec_eq(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_684_; 
lean_inc_ref(v_ty_657_);
lean_inc(v_y_656_);
lean_inc(v_offset_655_);
lean_inc(v_i_654_);
lean_inc(v_fvarId_653_);
v_isSharedCheck_684_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_685_ = lean_ctor_get(v_code_303_, 5);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_code_303_, 4);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_690_);
v___x_676_ = v_code_303_;
v_isShared_677_ = v_isSharedCheck_684_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_code_303_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_684_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 5, v_a_660_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_fvarId_653_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_i_654_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_offset_655_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_y_656_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_ty_657_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v_a_660_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_679_);
v___x_681_ = v___x_662_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_object* v___x_692_; 
lean_dec(v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_code_303_);
v___x_692_ = v___x_662_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_code_303_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 6);
return v___x_659_;
}
}
case 10:
{
lean_object* v_fvarId_695_; lean_object* v_cidx_696_; lean_object* v_k_697_; lean_object* v___x_698_; 
v_fvarId_695_ = lean_ctor_get(v_code_303_, 0);
v_cidx_696_ = lean_ctor_get(v_code_303_, 1);
v_k_697_ = lean_ctor_get(v_code_303_, 2);
lean_inc_ref(v_k_697_);
v___x_698_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_697_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_725_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_725_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_725_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_725_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v___x_703_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_695_);
v___x_704_ = l_Lean_FVarIdSet_insert(v___x_703_, v_fvarId_695_);
v___x_705_ = lean_st_ref_set(v_a_304_, v___x_704_);
v___x_706_ = lean_ptr_addr(v_k_697_);
v___x_707_ = lean_ptr_addr(v_a_699_);
v___x_708_ = lean_usize_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_718_; 
lean_inc(v_cidx_696_);
lean_inc(v_fvarId_695_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; 
v_unused_719_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_721_);
v___x_710_ = v_code_303_;
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
else
{
lean_dec(v_code_303_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 2, v_a_699_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fvarId_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_cidx_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_a_699_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_713_);
v___x_715_ = v___x_701_;
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
lean_object* v___x_723_; 
lean_dec(v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_code_303_);
v___x_723_ = v___x_701_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_code_303_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 3);
return v___x_698_;
}
}
case 11:
{
lean_object* v_fvarId_726_; lean_object* v_n_727_; uint8_t v_check_728_; uint8_t v_persistent_729_; lean_object* v_k_730_; lean_object* v___x_731_; 
v_fvarId_726_ = lean_ctor_get(v_code_303_, 0);
v_n_727_ = lean_ctor_get(v_code_303_, 1);
v_check_728_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*3);
v_persistent_729_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*3 + 1);
v_k_730_ = lean_ctor_get(v_code_303_, 2);
lean_inc_ref(v_k_730_);
v___x_731_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_730_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_758_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_758_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_758_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_758_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; size_t v___x_739_; size_t v___x_740_; uint8_t v___x_741_; 
v___x_736_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_726_);
v___x_737_ = l_Lean_FVarIdSet_insert(v___x_736_, v_fvarId_726_);
v___x_738_ = lean_st_ref_set(v_a_304_, v___x_737_);
v___x_739_ = lean_ptr_addr(v_k_730_);
v___x_740_ = lean_ptr_addr(v_a_732_);
v___x_741_ = lean_usize_dec_eq(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
lean_inc(v_n_727_);
lean_inc(v_fvarId_726_);
v_isSharedCheck_751_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_752_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_754_);
v___x_743_ = v_code_303_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_dec(v_code_303_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 2, v_a_732_);
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fvarId_726_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_n_727_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_a_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_750_, sizeof(void*)*3, v_check_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_750_, sizeof(void*)*3 + 1, v_persistent_729_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_746_);
v___x_748_ = v___x_734_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v___x_756_; 
lean_dec(v_a_732_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v_code_303_);
v___x_756_ = v___x_734_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_code_303_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 3);
return v___x_731_;
}
}
case 12:
{
lean_object* v_fvarId_759_; lean_object* v_n_760_; uint8_t v_check_761_; uint8_t v_persistent_762_; lean_object* v_objs_x3f_763_; lean_object* v_k_764_; lean_object* v___x_765_; 
v_fvarId_759_ = lean_ctor_get(v_code_303_, 0);
v_n_760_ = lean_ctor_get(v_code_303_, 1);
v_check_761_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*4);
v_persistent_762_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*4 + 1);
v_objs_x3f_763_ = lean_ctor_get(v_code_303_, 2);
v_k_764_ = lean_ctor_get(v_code_303_, 3);
lean_inc_ref(v_k_764_);
v___x_765_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_764_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_793_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_793_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_793_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_793_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; uint8_t v___x_775_; 
v___x_770_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_759_);
v___x_771_ = l_Lean_FVarIdSet_insert(v___x_770_, v_fvarId_759_);
v___x_772_ = lean_st_ref_set(v_a_304_, v___x_771_);
v___x_773_ = lean_ptr_addr(v_k_764_);
v___x_774_ = lean_ptr_addr(v_a_766_);
v___x_775_ = lean_usize_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_785_; 
lean_inc(v_objs_x3f_763_);
lean_inc(v_n_760_);
lean_inc(v_fvarId_759_);
v_isSharedCheck_785_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_786_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_789_);
v___x_777_ = v_code_303_;
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_code_303_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 3, v_a_766_);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fvarId_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_n_760_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_objs_x3f_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_a_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*4, v_check_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*4 + 1, v_persistent_762_);
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
lean_object* v___x_791_; 
lean_dec(v_a_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v_code_303_);
v___x_791_ = v___x_768_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_code_303_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 4);
return v___x_765_;
}
}
default: 
{
lean_object* v_fvarId_794_; lean_object* v_k_795_; lean_object* v___x_796_; 
v_fvarId_794_ = lean_ctor_get(v_code_303_, 0);
v_k_795_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_795_);
v___x_796_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_795_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_822_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_822_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_822_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_822_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; uint8_t v___x_806_; 
v___x_801_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_794_);
v___x_802_ = l_Lean_FVarIdSet_insert(v___x_801_, v_fvarId_794_);
v___x_803_ = lean_st_ref_set(v_a_304_, v___x_802_);
v___x_804_ = lean_ptr_addr(v_k_795_);
v___x_805_ = lean_ptr_addr(v_a_797_);
v___x_806_ = lean_usize_dec_eq(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_816_; 
lean_inc(v_fvarId_794_);
v_isSharedCheck_816_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_817_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_818_);
v___x_808_ = v_code_303_;
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_code_303_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_a_797_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fvarId_794_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_a_797_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_811_);
v___x_813_ = v___x_799_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v___x_820_; 
lean_dec(v_a_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_code_303_);
v___x_820_ = v___x_799_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_code_303_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_796_;
}
}
}
v___jp_310_:
{
if (lean_obj_tag(v___y_311_) == 0)
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_isSharedCheck_318_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v___y_311_, 0);
lean_dec(v_unused_319_);
v___x_313_ = v___y_311_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_dec(v___y_311_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v_code_303_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_code_303_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_code_303_);
v_a_320_ = lean_ctor_get(v___y_311_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___y_311_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___y_311_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t v_pu_823_, lean_object* v_funDecl_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_params_831_; lean_object* v_type_832_; lean_object* v_value_833_; lean_object* v___x_834_; 
v_params_831_ = lean_ctor_get(v_funDecl_824_, 2);
lean_inc_ref(v_params_831_);
v_type_832_ = lean_ctor_get(v_funDecl_824_, 3);
lean_inc_ref(v_type_832_);
v_value_833_ = lean_ctor_get(v_funDecl_824_, 4);
lean_inc_ref(v_value_833_);
v___x_834_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_823_, v_value_833_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_836_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_836_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_823_, v_funDecl_824_, v_type_832_, v_params_831_, v_a_835_, v_a_827_);
return v___x_836_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_type_832_);
lean_dec_ref(v_params_831_);
lean_dec_ref(v_funDecl_824_);
v_a_837_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_834_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_834_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object* v_pu_845_, lean_object* v_funDecl_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
uint8_t v_pu_boxed_853_; lean_object* v_res_854_; 
v_pu_boxed_853_ = lean_unbox(v_pu_845_);
v_res_854_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_boxed_853_, v_funDecl_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object* v_pu_855_, lean_object* v_i_856_, lean_object* v_as_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
uint8_t v_pu_boxed_864_; lean_object* v_res_865_; 
v_pu_boxed_864_ = lean_unbox(v_pu_855_);
v_res_865_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_864_, v_i_856_, v_as_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* v_pu_866_, lean_object* v_code_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
uint8_t v_pu_boxed_874_; lean_object* v_res_875_; 
v_pu_boxed_874_ = lean_unbox(v_pu_866_);
v_res_875_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_boxed_874_, v_code_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
return v_res_875_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object* v_00_u03b2_876_, lean_object* v_k_877_, lean_object* v_t_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_877_, v_t_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object* v_00_u03b2_880_, lean_object* v_k_881_, lean_object* v_t_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_880_, v_k_881_, v_t_882_);
lean_dec(v_t_882_);
lean_dec(v_k_881_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t v_pu_885_, lean_object* v_as_886_, size_t v_i_887_, size_t v_stop_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_886_, v_i_887_, v_stop_888_, v_b_889_, v___y_890_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object* v_pu_897_, lean_object* v_as_898_, lean_object* v_i_899_, lean_object* v_stop_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v_pu_boxed_908_; size_t v_i_boxed_909_; size_t v_stop_boxed_910_; lean_object* v_res_911_; 
v_pu_boxed_908_ = lean_unbox(v_pu_897_);
v_i_boxed_909_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_stop_boxed_910_ = lean_unbox_usize(v_stop_900_);
lean_dec(v_stop_900_);
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_908_, v_as_898_, v_i_boxed_909_, v_stop_boxed_910_, v_b_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v_as_898_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object* v_f_912_, lean_object* v_v_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
if (lean_obj_tag(v_v_913_) == 0)
{
lean_object* v_code_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_943_; 
v_code_919_ = lean_ctor_get(v_v_913_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_v_913_);
if (v_isSharedCheck_943_ == 0)
{
v___x_921_ = v_v_913_;
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_code_919_);
lean_dec(v_v_913_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; 
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_923_ = lean_apply_6(v_f_912_, v_code_919_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_934_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_a_924_);
v___x_929_ = v___x_921_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_929_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_del_object(v___x_921_);
v_a_935_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_923_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_923_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v_f_912_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_v_913_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object* v_f_945_, lean_object* v_v_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_945_, v_v_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t v_pu_953_, lean_object* v_f_954_, lean_object* v_v_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_954_, v_v_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object* v_pu_962_, lean_object* v_f_963_, lean_object* v_v_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v_pu_boxed_970_; lean_object* v_res_971_; 
v_pu_boxed_970_ = lean_unbox(v_pu_962_);
v_res_971_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_970_, v_f_963_, v_v_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object* v___x_972_, uint8_t v_pu_973_, lean_object* v_code_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_st_mk_ref(v___x_972_);
v___x_981_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_973_, v_code_974_, v___x_980_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_990_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_st_ref_get(v___x_980_);
lean_dec(v___x_980_);
lean_dec(v___x_986_);
if (v_isShared_985_ == 0)
{
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_982_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_dec(v___x_980_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object* v___x_991_, lean_object* v_pu_992_, lean_object* v_code_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
uint8_t v_pu_boxed_999_; lean_object* v_res_1000_; 
v_pu_boxed_999_ = lean_unbox(v_pu_992_);
v_res_1000_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(v___x_991_, v_pu_boxed_999_, v_code_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t v_pu_1001_, lean_object* v_decl_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_toSignature_1008_; lean_object* v_value_1009_; uint8_t v_recursive_1010_; lean_object* v_inlineAttr_x3f_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1038_; 
v_toSignature_1008_ = lean_ctor_get(v_decl_1002_, 0);
v_value_1009_ = lean_ctor_get(v_decl_1002_, 1);
v_recursive_1010_ = lean_ctor_get_uint8(v_decl_1002_, sizeof(void*)*3);
v_inlineAttr_x3f_1011_ = lean_ctor_get(v_decl_1002_, 2);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_decl_1002_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1013_ = v_decl_1002_;
v_isShared_1014_ = v_isSharedCheck_1038_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_inlineAttr_x3f_1011_);
lean_inc(v_value_1009_);
lean_inc(v_toSignature_1008_);
lean_dec(v_decl_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1038_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_box(1);
v___x_1016_ = lean_box(v_pu_1001_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1017_, 0, v___x_1015_);
lean_closure_set(v___f_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_1017_, v_value_1009_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_a_1019_);
v___x_1024_ = v___x_1013_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_toSignature_1008_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1019_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_inlineAttr_x3f_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*3, v_recursive_1010_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1024_);
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_1013_);
lean_dec(v_inlineAttr_x3f_1011_);
lean_dec_ref(v_toSignature_1008_);
v_a_1030_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1018_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1018_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object* v_pu_1039_, lean_object* v_decl_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
uint8_t v_pu_boxed_1046_; lean_object* v_res_1047_; 
v_pu_boxed_1046_ = lean_unbox(v_pu_1039_);
v_res_1047_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v_pu_boxed_1046_, v_decl_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t v_phase_1051_, lean_object* v_occurrence_1052_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1053_ = ((lean_object*)(l_Lean_Compiler_LCNF_elimDeadVars___closed__1));
v___x_1054_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1051_);
v___x_1055_ = lean_box(v___x_1054_);
v___x_1056_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed), 7, 1);
lean_closure_set(v___x_1056_, 0, v___x_1055_);
v___x_1057_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1053_, v_phase_1051_, v___x_1056_, v_occurrence_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object* v_phase_1058_, lean_object* v_occurrence_1059_){
_start:
{
uint8_t v_phase_boxed_1060_; lean_object* v_res_1061_; 
v_phase_boxed_1060_ = lean_unbox(v_phase_1058_);
v_res_1061_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_1060_, v_occurrence_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1133_ = 1;
v___x_1134_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1135_ = l_Lean_registerTraceClass(v___x_1132_, v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
return v_res_1137_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
