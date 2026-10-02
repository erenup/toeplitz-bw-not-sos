import ToeplitzSOS.Negative.WitnessArithmetic

/-! Kernel-checked block sums for all 1024² entries of the witness. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ToeplitzSOS.Negative.Witness

private theorem block_0 : upperBlock 0 = (179060801680773729969021763844 : ℤ) := by decide +kernel

private theorem block_1 : upperBlock 1 = (1071143171353529442989350390978 : ℤ) := by decide +kernel

private theorem block_2 : upperBlock 2 = (2532166975789782643930727874696 : ℤ) := by decide +kernel

private theorem block_3 : upperBlock 3 = (4143540093503396891007885808070 : ℤ) := by decide +kernel

private theorem block_4 : upperBlock 4 = (5479249624684301586022844335918 : ℤ) := by decide +kernel

private theorem block_5 : upperBlock 5 = (6231162185332986051142424826456 : ℤ) := by decide +kernel

private theorem block_6 : upperBlock 6 = (6271456005751951730198693298024 : ℤ) := by decide +kernel

private theorem block_7 : upperBlock 7 = (5646219243616432642531125081354 : ℤ) := by decide +kernel

private theorem block_8 : upperBlock 8 = (4520752121272931586308083630766 : ℤ) := by decide +kernel

private theorem block_9 : upperBlock 9 = (3110889045002218015848924477572 : ℤ) := by decide +kernel

private theorem block_10 : upperBlock 10 = (1624290455183783844579699769440 : ℤ) := by decide +kernel

private theorem block_11 : upperBlock 11 = (224729189230667367601451734516 : ℤ) := by decide +kernel

private theorem block_12 : upperBlock 12 = (-981005816452452394594125403926 : ℤ) := by decide +kernel

private theorem block_13 : upperBlock 13 = (-1940158272716355950232710169360 : ℤ) := by decide +kernel

private theorem block_14 : upperBlock 14 = (-2642093002548919121748097513076 : ℤ) := by decide +kernel

private theorem block_15 : upperBlock 15 = (-3104567649808590925755889685194 : ℤ) := by decide +kernel

private theorem block_16 : upperBlock 16 = (-3360874006332316148244663594506 : ℤ) := by decide +kernel

private theorem block_17 : upperBlock 17 = (-3450365877967568682922759918294 : ℤ) := by decide +kernel

private theorem block_18 : upperBlock 18 = (-3412029341465773670133992773874 : ℤ) := by decide +kernel

private theorem block_19 : upperBlock 19 = (-3280801762328370852115984321714 : ℤ) := by decide +kernel

private theorem block_20 : upperBlock 20 = (-3085830723418478826738125260432 : ℤ) := by decide +kernel

private theorem block_21 : upperBlock 21 = (-2850118655785868971577322408632 : ℤ) := by decide +kernel

private theorem block_22 : upperBlock 22 = (-2590724502647054116382136104080 : ℤ) := by decide +kernel

private theorem block_23 : upperBlock 23 = (-2319343282257232860220670198390 : ℤ) := by decide +kernel

private theorem block_24 : upperBlock 24 = (-2042841740583280771714225716226 : ℤ) := by decide +kernel

private theorem block_25 : upperBlock 25 = (-1763363092099815090490794546454 : ℤ) := by decide +kernel

private theorem block_26 : upperBlock 26 = (-1477609003242975872239354915306 : ℤ) := by decide +kernel

private theorem block_27 : upperBlock 27 = (-1173946990377604932603577679900 : ℤ) := by decide +kernel

private theorem block_28 : upperBlock 28 = (-823438133310833987238366958010 : ℤ) := by decide +kernel

private theorem block_29 : upperBlock 29 = (-347628335453729094886675907214 : ℤ) := by decide +kernel

private theorem block_30 : upperBlock 30 = (539088215573906650802614095092 : ℤ) := by decide +kernel

private theorem block_31 : upperBlock 31 = (2564026722600516785937584795020 : ℤ) := by decide +kernel

private theorem block_32 : upperBlock 32 = (-32846351765910505932869550034 : ℤ) := by decide +kernel

private theorem block_33 : upperBlock 33 = (-213065043995962720180852717788 : ℤ) := by decide +kernel

private theorem block_34 : upperBlock 34 = (-581936350418716776032918497208 : ℤ) := by decide +kernel

private theorem block_35 : upperBlock 35 = (-1158054261397167295944086651892 : ℤ) := by decide +kernel

private theorem block_36 : upperBlock 36 = (-1937081068577994538422441050414 : ℤ) := by decide +kernel

private theorem block_37 : upperBlock 37 = (-2877490681898991095480595732728 : ℤ) := by decide +kernel

private theorem block_38 : upperBlock 38 = (-3902523067423413601416796941940 : ℤ) := by decide +kernel

private theorem block_39 : upperBlock 39 = (-4915953079048156667512413222650 : ℤ) := by decide +kernel

private theorem block_40 : upperBlock 40 = (-5823750971111431340605784448604 : ℤ) := by decide +kernel

private theorem block_41 : upperBlock 41 = (-6552266472093864223979100587180 : ℤ) := by decide +kernel

private theorem block_42 : upperBlock 42 = (-7058195703014828947302984132112 : ℤ) := by decide +kernel

private theorem block_43 : upperBlock 43 = (-7329524269371499100565590650410 : ℤ) := by decide +kernel

private theorem block_44 : upperBlock 44 = (-7380020700415847532015345357448 : ℤ) := by decide +kernel

private theorem block_45 : upperBlock 45 = (-7240773338893215270432584037606 : ℤ) := by decide +kernel

private theorem block_46 : upperBlock 46 = (-6951522197140926099924119311598 : ℤ) := by decide +kernel

private theorem block_47 : upperBlock 47 = (-6553714890563757281636695392938 : ℤ) := by decide +kernel

private theorem block_48 : upperBlock 48 = (-6085672167256279657361535200746 : ℤ) := by decide +kernel

private theorem block_49 : upperBlock 49 = (-5579965594693342027264986821972 : ℤ) := by decide +kernel

private theorem block_50 : upperBlock 50 = (-5062407655316193428716188492684 : ℤ) := by decide +kernel

private theorem block_51 : upperBlock 51 = (-4552153327935011241803467029814 : ℤ) := by decide +kernel

private theorem block_52 : upperBlock 52 = (-4062410295735646650915767978568 : ℤ) := by decide +kernel

private theorem block_53 : upperBlock 53 = (-3601445381332849556857803668652 : ℤ) := by decide +kernel

private theorem block_54 : upperBlock 54 = (-3173559503490830176255922692536 : ℤ) := by decide +kernel

private theorem block_55 : upperBlock 55 = (-2779969859012292631307145096770 : ℤ) := by decide +kernel

private theorem block_56 : upperBlock 56 = (-2419460727293565456658251458556 : ℤ) := by decide +kernel

private theorem block_57 : upperBlock 57 = (-2088689938235968305943578153728 : ℤ) := by decide +kernel

private theorem block_58 : upperBlock 58 = (-1781984989788637038734145663390 : ℤ) := by decide +kernel

private theorem block_59 : upperBlock 59 = (-1490049841826506771900568241724 : ℤ) := by decide +kernel

private theorem block_60 : upperBlock 60 = (-1195818247932136293496208299072 : ℤ) := by decide +kernel

private theorem block_61 : upperBlock 61 = (-860222443020302843027694990076 : ℤ) := by decide +kernel

private theorem block_62 : upperBlock 62 = (-361915287262829728337280277436 : ℤ) := by decide +kernel

private theorem block_63 : upperBlock 63 = (305668951718130237264140084992 : ℤ) := by decide +kernel

/-- The sum of the directed integer upper bounds is strictly negative
with magnitude exceeding `2^42 * 2^64`. All 1024² entries are checked by kernel reduction. -/
theorem fullUpper_lt : fullUpper < -(2 : ℤ)^42 * 2^64 := by
  unfold fullUpper
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, block_0, block_1, block_2, block_3, block_4, block_5, block_6, block_7, block_8, block_9, block_10, block_11, block_12, block_13, block_14, block_15, block_16, block_17, block_18, block_19, block_20, block_21, block_22, block_23, block_24, block_25, block_26, block_27, block_28, block_29, block_30, block_31, block_32, block_33, block_34, block_35, block_36, block_37, block_38, block_39, block_40, block_41, block_42, block_43, block_44, block_45, block_46, block_47, block_48, block_49, block_50, block_51, block_52, block_53, block_54, block_55, block_56, block_57, block_58, block_59, block_60, block_61, block_62, block_63]

end ToeplitzSOS.Negative.Witness
