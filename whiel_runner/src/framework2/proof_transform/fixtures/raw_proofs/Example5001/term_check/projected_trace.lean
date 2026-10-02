  -- step23 definition folding
  have step23 := step13
  change ((∃ v81 v82 : ι,(Xor' («_op_zRes» v81 v82) («_op_zTcl» v81 v82))) ∧ (∀ v0 : ι,((∃ v1 v2 : ι,((«_op_zBase» v1 v2) ∧ (v0=v1))) ∨ (∃ v3 v4 : ι,((«_op_zBase» v3 v4) ∧ (v0=v4))) ∨ (∃ v5 v6 : ι,((«_op_zEdge» v5 v6) ∧ (v0=v5))) ∨ («_sP8» v0) ∨ (∃ v9 v10 : ι,(v0=v9)) ∨ (∃ v11 v12 : ι,(v0=v12)) ∨ («_sP7» v0) ∨ («_sP6» v0) ∨ («_sP5» v0) ∨ («_sP4» v0) ∨ («_sP3» v0) ∨ («_sP2» v0) ∨ («_sP1» v0) ∨ («_sP0» v0) ∨ (∃ v29 v30 : ι,(v0=v29)) ∨ (∃ v31 v32 : ι,(v0=v32)) ∨ (∃ v33 v34 : ι,(v0=v33)) ∨ (∃ v35 v36 : ι,(v0=v36)) ∨ (∃ v37 v38 : ι,(v0=v37)) ∨ (∃ v39 v40 : ι,(v0=v40)) ∨ (∃ v41 v42 : ι,(v0=v41)) ∨ (∃ v43 v44 : ι,(v0=v44)) ∨ (∃ v45 v46 : ι,(v0=v45)) ∨ (∃ v47 v48 : ι,(v0=v48)))) ∧ (∀ v49 v50 : ι,(¬(«_op_zWorkT» v49 v50))) ∧ (∀ v51 v52 : ι,((«_op_zTcl» v51 v52) ↔ («_oa_zTcl» v51 v52))) ∧ (∀ v53 v54 : ι,((«_op_zTcl» v53 v54) ∨ (∀ v55 v56 v57 v58 : ι,((¬(«_oa_zTcl» v55 v56)) ∨ (¬(«_op_zEdge» v57 v58)) ∨ (¬(v56=v57)) ∨ (¬(v53=v55)) ∨ (¬(v54=v58)))))) ∧ (∀ v59 v60 : ι,((«_op_zRes» v59 v60) ∨ (∃ v65 v66 v67 v68 : ι,((«_op_zWorkT» v65 v66) ∧ («_op_zEdge» v67 v68) ∧ (v66=v67) ∧ (v59=v65) ∧ (v60=v68))) ∨ (∀ v61 v62 v63 v64 : ι,((¬(«_op_zRes» v61 v62)) ∨ (¬(«_op_zEdge» v63 v64)) ∨ (¬(v62=v63)) ∨ (¬(v59=v61)) ∨ (¬(v60=v64)))))) ∧ (∀ v69 v70 : ι,((«_op_zRes» v69 v70) ∨ (¬(«_op_zBase» v69 v70)))) ∧ (∀ v71 v72 : ι,((«_op_zTcl» v71 v72) ∨ (¬(«_op_zBase» v71 v72)))) ∧ (∀ v73 v74 : ι,((«_op_zRes» v73 v74) ∨ (¬(«_oa_zTcl» v73 v74)))) ∧ (∀ v75 v76 : ι,((«_op_zTcl» v75 v76) ∨ (¬(«_op_zRes» v75 v76)))) ∧ (∀ v77 v78 : ι,((«_op_zRes» v77 v78) ∨ (¬(«_op_zTcl» v77 v78)))) ∧ (∀ v79 v80 : ι,((«_op_zTcl» v79 v80) ∨ (¬(«_op_zWorkT» v79 v80))))) at step23
  have step60 := inf_s60  step23
  have step61 := inf_s61  step60
  -- step79 skolemisation
  exists_prenex at step61
  let ⟨«_sK27»,«_sK28»,«_sK29»,«_sK30»,«_sK31»,«_sK32»,«_sK33»,«_sK34»,«_sK35»,«_sK36»,«_sK37»,«_sK38»,«_sK39»,«_sK40»,«_sK41»,«_sK42»,«_sK43»,«_sK44»,«_sK45»,«_sK46»,«_sK47»,«_sK48»,«_sK49»,«_sK50»,step79'⟩ := step61
  have step79 : ((((¬(«_op_zTcl» («_sK27») («_sK28»))) ∨ (¬(«_op_zRes» («_sK27») («_sK28»)))) ∧ ((«_op_zTcl» («_sK27») («_sK28»)) ∨ («_op_zRes» («_sK27») («_sK28»)))) ∧ (∀ v2 : ι,(((«_op_zBase» («_sK29» v2) («_sK30» v2)) ∧ ((«_sK29» v2)=v2)) ∨ ((«_op_zBase» («_sK31» v2) («_sK32» v2)) ∧ ((«_sK32» v2)=v2)) ∨ ((«_op_zEdge» («_sK33» v2) («_sK34» v2)) ∧ ((«_sK33» v2)=v2)) ∨ («_sP8» v2) ∨ ((«_sK35» v2)=v2) ∨ ((«_sK36» v2)=v2) ∨ («_sP7» v2) ∨ («_sP6» v2) ∨ («_sP5» v2) ∨ («_sP4» v2) ∨ («_sP3» v2) ∨ («_sP2» v2) ∨ («_sP1» v2) ∨ («_sP0» v2) ∨ ((«_sK37» v2)=v2) ∨ ((«_sK38» v2)=v2) ∨ ((«_sK39» v2)=v2) ∨ ((«_sK40» v2)=v2) ∨ ((«_sK41» v2)=v2) ∨ ((«_sK42» v2)=v2) ∨ ((«_sK43» v2)=v2) ∨ ((«_sK44» v2)=v2) ∨ ((«_sK45» v2)=v2) ∨ ((«_sK46» v2)=v2))) ∧ (∀ v33 v34 : ι,(¬(«_op_zWorkT» v33 v34))) ∧ (∀ v35 v36 : ι,(((«_op_zTcl» v35 v36) ∨ (¬(«_oa_zTcl» v35 v36))) ∧ ((«_oa_zTcl» v35 v36) ∨ (¬(«_op_zTcl» v35 v36))))) ∧ (∀ v37 v38 : ι,((«_op_zTcl» v37 v38) ∨ (∀ v39 v40 v41 v42 : ι,((¬(«_oa_zTcl» v39 v40)) ∨ (¬(«_op_zEdge» v41 v42)) ∨ (¬(v40=v41)) ∨ (¬(v37=v39)) ∨ (¬(v38=v42)))))) ∧ (∀ v43 v44 : ι,((«_op_zRes» v43 v44) ∨ ((«_op_zWorkT» («_sK47» v43 v44) («_sK48» v43 v44)) ∧ («_op_zEdge» («_sK49» v43 v44) («_sK50» v43 v44)) ∧ ((«_sK48» v43 v44)=(«_sK49» v43 v44)) ∧ ((«_sK47» v43 v44)=v43) ∧ ((«_sK50» v43 v44)=v44)) ∨ (∀ v49 v50 v51 v52 : ι,((¬(«_op_zRes» v49 v50)) ∨ (¬(«_op_zEdge» v51 v52)) ∨ (¬(v50=v51)) ∨ (¬(v43=v49)) ∨ (¬(v44=v52)))))) ∧ (∀ v53 v54 : ι,((«_op_zRes» v53 v54) ∨ (¬(«_op_zBase» v53 v54)))) ∧ (∀ v55 v56 : ι,((«_op_zTcl» v55 v56) ∨ (¬(«_op_zBase» v55 v56)))) ∧ (∀ v57 v58 : ι,((«_op_zRes» v57 v58) ∨ (¬(«_oa_zTcl» v57 v58)))) ∧ (∀ v59 v60 : ι,((«_op_zTcl» v59 v60) ∨ (¬(«_op_zRes» v59 v60)))) ∧ (∀ v61 v62 : ι,((«_op_zRes» v61 v62) ∨ (¬(«_op_zTcl» v61 v62)))) ∧ (∀ v63 v64 : ι,((«_op_zTcl» v63 v64) ∨ (¬(«_op_zWorkT» v63 v64))))) := by symm_match using step79'
  have step99 : (∀ v61 v62 : ι, (¬(«_op_zTcl» v61 v62)) ∨ («_op_zRes» v61 v62)) := by
    vampire_project_ordered using step79

  have step100 : (∀ v59 v60 : ι, («_op_zTcl» v59 v60) ∨ (¬(«_op_zRes» v59 v60))) := by
    vampire_project_ordered using step79

  have step121 : ((«_op_zTcl» («_sK27») («_sK28»)) ∨ («_op_zRes» («_sK27») («_sK28»))) := by
    vampire_project_ordered using step79

  have step122 : ((¬(«_op_zTcl» («_sK27») («_sK28»))) ∨ (¬(«_op_zRes» («_sK27») («_sK28»)))) := by
    vampire_project_ordered using step79

  have step141 := inf_s141  step121 step100
  have step142 := inf_s142  step122 step100
  have step145 := inf_s145  step99 step141
  have step146 := inf_s146  step145 step142
  exact step146
