import PEqualNP.Research.AffineClique
namespace PEqualNP.Research.AffineClique
set_option maxRecDepth 80000
set_option maxHeartbeats 8000000
private def suffix215 : List Cell := []
private theorem safe215 : branches (cap 4) suffix215 = true := rfl
private def suffix214 : List Cell := (24,25) :: suffix215
private theorem safe214 : branches (cap 4) suffix214 = true := by
  rw [suffix214, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe215⟩
private def suffix213 : List Cell := (24,20) :: suffix214
private theorem safe213 : branches (cap 4) suffix213 = true := by
  rw [suffix213, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe214⟩
private def suffix212 : List Cell := (24,15) :: suffix213
private theorem safe212 : branches (cap 4) suffix212 = true := by
  rw [suffix212, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe213⟩
private def suffix211 : List Cell := (24,10) :: suffix212
private theorem safe211 : branches (cap 4) suffix211 = true := by
  rw [suffix211, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe212⟩
private def suffix210 : List Cell := (24,0) :: suffix211
private theorem safe210 : branches (cap 4) suffix210 = true := by
  rw [suffix210, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe211⟩
private def suffix209 : List Cell := (23,25) :: suffix210
private theorem safe209 : branches (cap 4) suffix209 = true := by
  rw [suffix209, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe210⟩
private def suffix208 : List Cell := (23,20) :: suffix209
private theorem safe208 : branches (cap 4) suffix208 = true := by
  rw [suffix208, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe209⟩
private def suffix207 : List Cell := (23,15) :: suffix208
private theorem safe207 : branches (cap 4) suffix207 = true := by
  rw [suffix207, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe208⟩
private def suffix206 : List Cell := (23,5) :: suffix207
private theorem safe206 : branches (cap 4) suffix206 = true := by
  rw [suffix206, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe207⟩
private def suffix205 : List Cell := (23,0) :: suffix206
private theorem safe205 : branches (cap 4) suffix205 = true := by
  rw [suffix205, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe206⟩
private def suffix204 : List Cell := (22,25) :: suffix205
private theorem safe204 : branches (cap 4) suffix204 = true := by
  rw [suffix204, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe205⟩
private def suffix203 : List Cell := (22,20) :: suffix204
private theorem safe203 : branches (cap 4) suffix203 = true := by
  rw [suffix203, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe204⟩
private def suffix202 : List Cell := (22,10) :: suffix203
private theorem safe202 : branches (cap 4) suffix202 = true := by
  rw [suffix202, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe203⟩
private def suffix201 : List Cell := (22,5) :: suffix202
private theorem safe201 : branches (cap 4) suffix201 = true := by
  rw [suffix201, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe202⟩
private def suffix200 : List Cell := (22,0) :: suffix201
private theorem safe200 : branches (cap 4) suffix200 = true := by
  rw [suffix200, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe201⟩
private def suffix199 : List Cell := (21,28) :: suffix200
private theorem safe199 : branches (cap 4) suffix199 = true := by
  rw [suffix199, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe200⟩
private def suffix198 : List Cell := (21,27) :: suffix199
private theorem safe198 : branches (cap 4) suffix198 = true := by
  rw [suffix198, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe199⟩
private def suffix197 : List Cell := (21,26) :: suffix198
private theorem safe197 : branches (cap 4) suffix197 = true := by
  rw [suffix197, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe198⟩
private def suffix196 : List Cell := (21,25) :: suffix197
private theorem safe196 : branches (cap 4) suffix196 = true := by
  rw [suffix196, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe197⟩
private def suffix195 : List Cell := (21,24) :: suffix196
private theorem safe195 : branches (cap 4) suffix195 = true := by
  rw [suffix195, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe196⟩
private def suffix194 : List Cell := (21,23) :: suffix195
private theorem safe194 : branches (cap 4) suffix194 = true := by
  rw [suffix194, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe195⟩
private def suffix193 : List Cell := (21,22) :: suffix194
private theorem safe193 : branches (cap 4) suffix193 = true := by
  rw [suffix193, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe194⟩
private def suffix192 : List Cell := (21,21) :: suffix193
private theorem safe192 : branches (cap 4) suffix192 = true := by
  rw [suffix192, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe193⟩
private def suffix191 : List Cell := (21,18) :: suffix192
private theorem safe191 : branches (cap 4) suffix191 = true := by
  rw [suffix191, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe192⟩
private def suffix190 : List Cell := (21,17) :: suffix191
private theorem safe190 : branches (cap 4) suffix190 = true := by
  rw [suffix190, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe191⟩
private def suffix189 : List Cell := (21,16) :: suffix190
private theorem safe189 : branches (cap 4) suffix189 = true := by
  rw [suffix189, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe190⟩
private def suffix188 : List Cell := (21,15) :: suffix189
private theorem safe188 : branches (cap 4) suffix188 = true := by
  rw [suffix188, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe189⟩
private def suffix187 : List Cell := (21,14) :: suffix188
private theorem safe187 : branches (cap 4) suffix187 = true := by
  rw [suffix187, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe188⟩
private def suffix186 : List Cell := (21,12) :: suffix187
private theorem safe186 : branches (cap 4) suffix186 = true := by
  rw [suffix186, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe187⟩
private def suffix185 : List Cell := (21,11) :: suffix186
private theorem safe185 : branches (cap 4) suffix185 = true := by
  rw [suffix185, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe186⟩
private def suffix184 : List Cell := (21,10) :: suffix185
private theorem safe184 : branches (cap 4) suffix184 = true := by
  rw [suffix184, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe185⟩
private def suffix183 : List Cell := (21,9) :: suffix184
private theorem safe183 : branches (cap 4) suffix183 = true := by
  rw [suffix183, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe184⟩
private def suffix182 : List Cell := (21,8) :: suffix183
private theorem safe182 : branches (cap 4) suffix182 = true := by
  rw [suffix182, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe183⟩
private def suffix181 : List Cell := (21,6) :: suffix182
private theorem safe181 : branches (cap 4) suffix181 = true := by
  rw [suffix181, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe182⟩
private def suffix180 : List Cell := (21,5) :: suffix181
private theorem safe180 : branches (cap 4) suffix180 = true := by
  rw [suffix180, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe181⟩
private def suffix179 : List Cell := (21,4) :: suffix180
private theorem safe179 : branches (cap 4) suffix179 = true := by
  rw [suffix179, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe180⟩
private def suffix178 : List Cell := (21,3) :: suffix179
private theorem safe178 : branches (cap 4) suffix178 = true := by
  rw [suffix178, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe179⟩
private def suffix177 : List Cell := (21,2) :: suffix178
private theorem safe177 : branches (cap 4) suffix177 = true := by
  rw [suffix177, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe178⟩
private def suffix176 : List Cell := (21,0) :: suffix177
private theorem safe176 : branches (cap 4) suffix176 = true := by
  rw [suffix176, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe177⟩
private def suffix175 : List Cell := (20,25) :: suffix176
private theorem safe175 : branches (cap 4) suffix175 = true := by
  rw [suffix175, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe176⟩
private def suffix174 : List Cell := (20,20) :: suffix175
private theorem safe174 : branches (cap 4) suffix174 = true := by
  rw [suffix174, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe175⟩
private def suffix173 : List Cell := (20,15) :: suffix174
private theorem safe173 : branches (cap 4) suffix173 = true := by
  rw [suffix173, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe174⟩
private def suffix172 : List Cell := (20,10) :: suffix173
private theorem safe172 : branches (cap 4) suffix172 = true := by
  rw [suffix172, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe173⟩
private def suffix171 : List Cell := (20,5) :: suffix172
private theorem safe171 : branches (cap 4) suffix171 = true := by
  rw [suffix171, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe172⟩
private def suffix170 : List Cell := (19,25) :: suffix171
private theorem safe170 : branches (cap 4) suffix170 = true := by
  rw [suffix170, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe171⟩
private def suffix169 : List Cell := (19,20) :: suffix170
private theorem safe169 : branches (cap 4) suffix169 = true := by
  rw [suffix169, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe170⟩
private def suffix168 : List Cell := (19,10) :: suffix169
private theorem safe168 : branches (cap 4) suffix168 = true := by
  rw [suffix168, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe169⟩
private def suffix167 : List Cell := (19,5) :: suffix168
private theorem safe167 : branches (cap 4) suffix167 = true := by
  rw [suffix167, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe168⟩
private def suffix166 : List Cell := (19,0) :: suffix167
private theorem safe166 : branches (cap 4) suffix166 = true := by
  rw [suffix166, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe167⟩
private def suffix165 : List Cell := (18,25) :: suffix166
private theorem safe165 : branches (cap 4) suffix165 = true := by
  rw [suffix165, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe166⟩
private def suffix164 : List Cell := (18,20) :: suffix165
private theorem safe164 : branches (cap 4) suffix164 = true := by
  rw [suffix164, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe165⟩
private def suffix163 : List Cell := (18,15) :: suffix164
private theorem safe163 : branches (cap 4) suffix163 = true := by
  rw [suffix163, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe164⟩
private def suffix162 : List Cell := (18,10) :: suffix163
private theorem safe162 : branches (cap 4) suffix162 = true := by
  rw [suffix162, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe163⟩
private def suffix161 : List Cell := (18,0) :: suffix162
private theorem safe161 : branches (cap 4) suffix161 = true := by
  rw [suffix161, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe162⟩
private def suffix160 : List Cell := (17,25) :: suffix161
private theorem safe160 : branches (cap 4) suffix160 = true := by
  rw [suffix160, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe161⟩
private def suffix159 : List Cell := (17,15) :: suffix160
private theorem safe159 : branches (cap 4) suffix159 = true := by
  rw [suffix159, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe160⟩
private def suffix158 : List Cell := (17,10) :: suffix159
private theorem safe158 : branches (cap 4) suffix158 = true := by
  rw [suffix158, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe159⟩
private def suffix157 : List Cell := (17,5) :: suffix158
private theorem safe157 : branches (cap 4) suffix157 = true := by
  rw [suffix157, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe158⟩
private def suffix156 : List Cell := (17,0) :: suffix157
private theorem safe156 : branches (cap 4) suffix156 = true := by
  rw [suffix156, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe157⟩
private def suffix155 : List Cell := (16,29) :: suffix156
private theorem safe155 : branches (cap 4) suffix155 = true := by
  rw [suffix155, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe156⟩
private def suffix154 : List Cell := (16,27) :: suffix155
private theorem safe154 : branches (cap 4) suffix154 = true := by
  rw [suffix154, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe155⟩
private def suffix153 : List Cell := (16,26) :: suffix154
private theorem safe153 : branches (cap 4) suffix153 = true := by
  rw [suffix153, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe154⟩
private def suffix152 : List Cell := (16,25) :: suffix153
private theorem safe152 : branches (cap 4) suffix152 = true := by
  rw [suffix152, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe153⟩
private def suffix151 : List Cell := (16,23) :: suffix152
private theorem safe151 : branches (cap 4) suffix151 = true := by
  rw [suffix151, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe152⟩
private def suffix150 : List Cell := (16,22) :: suffix151
private theorem safe150 : branches (cap 4) suffix150 = true := by
  rw [suffix150, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe151⟩
private def suffix149 : List Cell := (16,21) :: suffix150
private theorem safe149 : branches (cap 4) suffix149 = true := by
  rw [suffix149, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe150⟩
private def suffix148 : List Cell := (16,20) :: suffix149
private theorem safe148 : branches (cap 4) suffix148 = true := by
  rw [suffix148, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe149⟩
private def suffix147 : List Cell := (16,19) :: suffix148
private theorem safe147 : branches (cap 4) suffix147 = true := by
  rw [suffix147, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe148⟩
private def suffix146 : List Cell := (16,18) :: suffix147
private theorem safe146 : branches (cap 4) suffix146 = true := by
  rw [suffix146, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe147⟩
private def suffix145 : List Cell := (16,16) :: suffix146
private theorem safe145 : branches (cap 4) suffix145 = true := by
  rw [suffix145, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe146⟩
private def suffix144 : List Cell := (16,15) :: suffix145
private theorem safe144 : branches (cap 4) suffix144 = true := by
  rw [suffix144, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe145⟩
private def suffix143 : List Cell := (16,14) :: suffix144
private theorem safe143 : branches (cap 4) suffix143 = true := by
  rw [suffix143, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe144⟩
private def suffix142 : List Cell := (16,13) :: suffix143
private theorem safe142 : branches (cap 4) suffix142 = true := by
  rw [suffix142, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe143⟩
private def suffix141 : List Cell := (16,12) :: suffix142
private theorem safe141 : branches (cap 4) suffix141 = true := by
  rw [suffix141, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe142⟩
private def suffix140 : List Cell := (16,11) :: suffix141
private theorem safe140 : branches (cap 4) suffix140 = true := by
  rw [suffix140, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe141⟩
private def suffix139 : List Cell := (16,9) :: suffix140
private theorem safe139 : branches (cap 4) suffix139 = true := by
  rw [suffix139, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe140⟩
private def suffix138 : List Cell := (16,7) :: suffix139
private theorem safe138 : branches (cap 4) suffix138 = true := by
  rw [suffix138, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe139⟩
private def suffix137 : List Cell := (16,6) :: suffix138
private theorem safe137 : branches (cap 4) suffix137 = true := by
  rw [suffix137, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe138⟩
private def suffix136 : List Cell := (16,5) :: suffix137
private theorem safe136 : branches (cap 4) suffix136 = true := by
  rw [suffix136, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe137⟩
private def suffix135 : List Cell := (16,4) :: suffix136
private theorem safe135 : branches (cap 4) suffix135 = true := by
  rw [suffix135, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe136⟩
private def suffix134 : List Cell := (16,3) :: suffix135
private theorem safe134 : branches (cap 4) suffix134 = true := by
  rw [suffix134, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe135⟩
private def suffix133 : List Cell := (16,2) :: suffix134
private theorem safe133 : branches (cap 4) suffix133 = true := by
  rw [suffix133, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe134⟩
private def suffix132 : List Cell := (16,0) :: suffix133
private theorem safe132 : branches (cap 4) suffix132 = true := by
  rw [suffix132, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe133⟩
private def suffix131 : List Cell := (15,25) :: suffix132
private theorem safe131 : branches (cap 4) suffix131 = true := by
  rw [suffix131, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe132⟩
private def suffix130 : List Cell := (15,20) :: suffix131
private theorem safe130 : branches (cap 4) suffix130 = true := by
  rw [suffix130, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe131⟩
private def suffix129 : List Cell := (15,15) :: suffix130
private theorem safe129 : branches (cap 4) suffix129 = true := by
  rw [suffix129, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe130⟩
private def suffix128 : List Cell := (15,10) :: suffix129
private theorem safe128 : branches (cap 4) suffix128 = true := by
  rw [suffix128, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe129⟩
private def suffix127 : List Cell := (15,5) :: suffix128
private theorem safe127 : branches (cap 4) suffix127 = true := by
  rw [suffix127, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe128⟩
private def suffix126 : List Cell := (14,25) :: suffix127
private theorem safe126 : branches (cap 4) suffix126 = true := by
  rw [suffix126, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe127⟩
private def suffix125 : List Cell := (14,20) :: suffix126
private theorem safe125 : branches (cap 4) suffix125 = true := by
  rw [suffix125, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe126⟩
private def suffix124 : List Cell := (14,15) :: suffix125
private theorem safe124 : branches (cap 4) suffix124 = true := by
  rw [suffix124, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe125⟩
private def suffix123 : List Cell := (14,5) :: suffix124
private theorem safe123 : branches (cap 4) suffix123 = true := by
  rw [suffix123, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe124⟩
private def suffix122 : List Cell := (14,0) :: suffix123
private theorem safe122 : branches (cap 4) suffix122 = true := by
  rw [suffix122, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe123⟩
private def suffix121 : List Cell := (13,25) :: suffix122
private theorem safe121 : branches (cap 4) suffix121 = true := by
  rw [suffix121, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe122⟩
private def suffix120 : List Cell := (13,15) :: suffix121
private theorem safe120 : branches (cap 4) suffix120 = true := by
  rw [suffix120, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe121⟩
private def suffix119 : List Cell := (13,10) :: suffix120
private theorem safe119 : branches (cap 4) suffix119 = true := by
  rw [suffix119, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe120⟩
private def suffix118 : List Cell := (13,5) :: suffix119
private theorem safe118 : branches (cap 4) suffix118 = true := by
  rw [suffix118, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe119⟩
private def suffix117 : List Cell := (13,0) :: suffix118
private theorem safe117 : branches (cap 4) suffix117 = true := by
  rw [suffix117, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe118⟩
private def suffix116 : List Cell := (12,25) :: suffix117
private theorem safe116 : branches (cap 4) suffix116 = true := by
  rw [suffix116, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe117⟩
private def suffix115 : List Cell := (12,20) :: suffix116
private theorem safe115 : branches (cap 4) suffix115 = true := by
  rw [suffix115, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe116⟩
private def suffix114 : List Cell := (12,15) :: suffix115
private theorem safe114 : branches (cap 4) suffix114 = true := by
  rw [suffix114, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe115⟩
private def suffix113 : List Cell := (12,10) :: suffix114
private theorem safe113 : branches (cap 4) suffix113 = true := by
  rw [suffix113, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe114⟩
private def suffix112 : List Cell := (12,0) :: suffix113
private theorem safe112 : branches (cap 4) suffix112 = true := by
  rw [suffix112, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe113⟩
private def suffix111 : List Cell := (11,29) :: suffix112
private theorem safe111 : branches (cap 4) suffix111 = true := by
  rw [suffix111, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe112⟩
private def suffix110 : List Cell := (11,28) :: suffix111
private theorem safe110 : branches (cap 4) suffix110 = true := by
  rw [suffix110, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe111⟩
private def suffix109 : List Cell := (11,26) :: suffix110
private theorem safe109 : branches (cap 4) suffix109 = true := by
  rw [suffix109, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe110⟩
private def suffix108 : List Cell := (11,25) :: suffix109
private theorem safe108 : branches (cap 4) suffix108 = true := by
  rw [suffix108, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe109⟩
private def suffix107 : List Cell := (11,24) :: suffix108
private theorem safe107 : branches (cap 4) suffix107 = true := by
  rw [suffix107, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe108⟩
private def suffix106 : List Cell := (11,22) :: suffix107
private theorem safe106 : branches (cap 4) suffix106 = true := by
  rw [suffix106, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe107⟩
private def suffix105 : List Cell := (11,21) :: suffix106
private theorem safe105 : branches (cap 4) suffix105 = true := by
  rw [suffix105, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe106⟩
private def suffix104 : List Cell := (11,20) :: suffix105
private theorem safe104 : branches (cap 4) suffix104 = true := by
  rw [suffix104, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe105⟩
private def suffix103 : List Cell := (11,19) :: suffix104
private theorem safe103 : branches (cap 4) suffix103 = true := by
  rw [suffix103, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe104⟩
private def suffix102 : List Cell := (11,18) :: suffix103
private theorem safe102 : branches (cap 4) suffix102 = true := by
  rw [suffix102, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe103⟩
private def suffix101 : List Cell := (11,17) :: suffix102
private theorem safe101 : branches (cap 4) suffix101 = true := by
  rw [suffix101, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe102⟩
private def suffix100 : List Cell := (11,16) :: suffix101
private theorem safe100 : branches (cap 4) suffix100 = true := by
  rw [suffix100, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe101⟩
private def suffix99 : List Cell := (11,14) :: suffix100
private theorem safe99 : branches (cap 4) suffix99 = true := by
  rw [suffix99, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe100⟩
private def suffix98 : List Cell := (11,13) :: suffix99
private theorem safe98 : branches (cap 4) suffix98 = true := by
  rw [suffix98, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe99⟩
private def suffix97 : List Cell := (11,11) :: suffix98
private theorem safe97 : branches (cap 4) suffix97 = true := by
  rw [suffix97, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe98⟩
private def suffix96 : List Cell := (11,10) :: suffix97
private theorem safe96 : branches (cap 4) suffix96 = true := by
  rw [suffix96, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe97⟩
private def suffix95 : List Cell := (11,8) :: suffix96
private theorem safe95 : branches (cap 4) suffix95 = true := by
  rw [suffix95, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe96⟩
private def suffix94 : List Cell := (11,7) :: suffix95
private theorem safe94 : branches (cap 4) suffix94 = true := by
  rw [suffix94, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe95⟩
private def suffix93 : List Cell := (11,6) :: suffix94
private theorem safe93 : branches (cap 4) suffix93 = true := by
  rw [suffix93, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe94⟩
private def suffix92 : List Cell := (11,5) :: suffix93
private theorem safe92 : branches (cap 4) suffix92 = true := by
  rw [suffix92, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe93⟩
private def suffix91 : List Cell := (11,4) :: suffix92
private theorem safe91 : branches (cap 4) suffix91 = true := by
  rw [suffix91, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe92⟩
private def suffix90 : List Cell := (11,3) :: suffix91
private theorem safe90 : branches (cap 4) suffix90 = true := by
  rw [suffix90, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe91⟩
private def suffix89 : List Cell := (11,2) :: suffix90
private theorem safe89 : branches (cap 4) suffix89 = true := by
  rw [suffix89, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe90⟩
private def suffix88 : List Cell := (11,0) :: suffix89
private theorem safe88 : branches (cap 4) suffix88 = true := by
  rw [suffix88, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe89⟩
private def suffix87 : List Cell := (10,25) :: suffix88
private theorem safe87 : branches (cap 4) suffix87 = true := by
  rw [suffix87, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe88⟩
private def suffix86 : List Cell := (10,20) :: suffix87
private theorem safe86 : branches (cap 4) suffix86 = true := by
  rw [suffix86, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe87⟩
private def suffix85 : List Cell := (10,15) :: suffix86
private theorem safe85 : branches (cap 4) suffix85 = true := by
  rw [suffix85, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe86⟩
private def suffix84 : List Cell := (10,10) :: suffix85
private theorem safe84 : branches (cap 4) suffix84 = true := by
  rw [suffix84, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe85⟩
private def suffix83 : List Cell := (10,5) :: suffix84
private theorem safe83 : branches (cap 4) suffix83 = true := by
  rw [suffix83, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe84⟩
private def suffix82 : List Cell := (9,25) :: suffix83
private theorem safe82 : branches (cap 4) suffix82 = true := by
  rw [suffix82, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe83⟩
private def suffix81 : List Cell := (9,15) :: suffix82
private theorem safe81 : branches (cap 4) suffix81 = true := by
  rw [suffix81, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe82⟩
private def suffix80 : List Cell := (9,10) :: suffix81
private theorem safe80 : branches (cap 4) suffix80 = true := by
  rw [suffix80, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe81⟩
private def suffix79 : List Cell := (9,5) :: suffix80
private theorem safe79 : branches (cap 4) suffix79 = true := by
  rw [suffix79, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe80⟩
private def suffix78 : List Cell := (9,0) :: suffix79
private theorem safe78 : branches (cap 4) suffix78 = true := by
  rw [suffix78, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe79⟩
private def suffix77 : List Cell := (8,25) :: suffix78
private theorem safe77 : branches (cap 4) suffix77 = true := by
  rw [suffix77, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe78⟩
private def suffix76 : List Cell := (8,20) :: suffix77
private theorem safe76 : branches (cap 4) suffix76 = true := by
  rw [suffix76, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe77⟩
private def suffix75 : List Cell := (8,10) :: suffix76
private theorem safe75 : branches (cap 4) suffix75 = true := by
  rw [suffix75, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe76⟩
private def suffix74 : List Cell := (8,5) :: suffix75
private theorem safe74 : branches (cap 4) suffix74 = true := by
  rw [suffix74, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe75⟩
private def suffix73 : List Cell := (8,0) :: suffix74
private theorem safe73 : branches (cap 4) suffix73 = true := by
  rw [suffix73, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe74⟩
private def suffix72 : List Cell := (7,25) :: suffix73
private theorem safe72 : branches (cap 4) suffix72 = true := by
  rw [suffix72, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe73⟩
private def suffix71 : List Cell := (7,20) :: suffix72
private theorem safe71 : branches (cap 4) suffix71 = true := by
  rw [suffix71, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe72⟩
private def suffix70 : List Cell := (7,15) :: suffix71
private theorem safe70 : branches (cap 4) suffix70 = true := by
  rw [suffix70, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe71⟩
private def suffix69 : List Cell := (7,5) :: suffix70
private theorem safe69 : branches (cap 4) suffix69 = true := by
  rw [suffix69, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe70⟩
private def suffix68 : List Cell := (7,0) :: suffix69
private theorem safe68 : branches (cap 4) suffix68 = true := by
  rw [suffix68, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe69⟩
private def suffix67 : List Cell := (6,29) :: suffix68
private theorem safe67 : branches (cap 4) suffix67 = true := by
  rw [suffix67, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe68⟩
private def suffix66 : List Cell := (6,28) :: suffix67
private theorem safe66 : branches (cap 4) suffix66 = true := by
  rw [suffix66, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe67⟩
private def suffix65 : List Cell := (6,27) :: suffix66
private theorem safe65 : branches (cap 4) suffix65 = true := by
  rw [suffix65, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe66⟩
private def suffix64 : List Cell := (6,25) :: suffix65
private theorem safe64 : branches (cap 4) suffix64 = true := by
  rw [suffix64, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe65⟩
private def suffix63 : List Cell := (6,24) :: suffix64
private theorem safe63 : branches (cap 4) suffix63 = true := by
  rw [suffix63, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe64⟩
private def suffix62 : List Cell := (6,23) :: suffix63
private theorem safe62 : branches (cap 4) suffix62 = true := by
  rw [suffix62, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe63⟩
private def suffix61 : List Cell := (6,21) :: suffix62
private theorem safe61 : branches (cap 4) suffix61 = true := by
  rw [suffix61, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe62⟩
private def suffix60 : List Cell := (6,20) :: suffix61
private theorem safe60 : branches (cap 4) suffix60 = true := by
  rw [suffix60, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe61⟩
private def suffix59 : List Cell := (6,19) :: suffix60
private theorem safe59 : branches (cap 4) suffix59 = true := by
  rw [suffix59, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe60⟩
private def suffix58 : List Cell := (6,17) :: suffix59
private theorem safe58 : branches (cap 4) suffix58 = true := by
  rw [suffix58, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe59⟩
private def suffix57 : List Cell := (6,16) :: suffix58
private theorem safe57 : branches (cap 4) suffix57 = true := by
  rw [suffix57, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe58⟩
private def suffix56 : List Cell := (6,15) :: suffix57
private theorem safe56 : branches (cap 4) suffix56 = true := by
  rw [suffix56, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe57⟩
private def suffix55 : List Cell := (6,13) :: suffix56
private theorem safe55 : branches (cap 4) suffix55 = true := by
  rw [suffix55, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe56⟩
private def suffix54 : List Cell := (6,12) :: suffix55
private theorem safe54 : branches (cap 4) suffix54 = true := by
  rw [suffix54, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe55⟩
private def suffix53 : List Cell := (6,11) :: suffix54
private theorem safe53 : branches (cap 4) suffix53 = true := by
  rw [suffix53, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe54⟩
private def suffix52 : List Cell := (6,10) :: suffix53
private theorem safe52 : branches (cap 4) suffix52 = true := by
  rw [suffix52, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe53⟩
private def suffix51 : List Cell := (6,9) :: suffix52
private theorem safe51 : branches (cap 4) suffix51 = true := by
  rw [suffix51, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe52⟩
private def suffix50 : List Cell := (6,8) :: suffix51
private theorem safe50 : branches (cap 4) suffix50 = true := by
  rw [suffix50, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe51⟩
private def suffix49 : List Cell := (6,7) :: suffix50
private theorem safe49 : branches (cap 4) suffix49 = true := by
  rw [suffix49, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe50⟩
private def suffix48 : List Cell := (6,6) :: suffix49
private theorem safe48 : branches (cap 4) suffix48 = true := by
  rw [suffix48, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe49⟩
private def suffix47 : List Cell := (6,4) :: suffix48
private theorem safe47 : branches (cap 4) suffix47 = true := by
  rw [suffix47, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe48⟩
private def suffix46 : List Cell := (6,3) :: suffix47
private theorem safe46 : branches (cap 4) suffix46 = true := by
  rw [suffix46, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe47⟩
private def suffix45 : List Cell := (6,2) :: suffix46
private theorem safe45 : branches (cap 4) suffix45 = true := by
  rw [suffix45, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe46⟩
private def suffix44 : List Cell := (6,0) :: suffix45
private theorem safe44 : branches (cap 4) suffix44 = true := by
  rw [suffix44, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe45⟩
private def suffix43 : List Cell := (5,25) :: suffix44
private theorem safe43 : branches (cap 4) suffix43 = true := by
  rw [suffix43, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe44⟩
private def suffix42 : List Cell := (5,20) :: suffix43
private theorem safe42 : branches (cap 4) suffix42 = true := by
  rw [suffix42, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe43⟩
private def suffix41 : List Cell := (5,15) :: suffix42
private theorem safe41 : branches (cap 4) suffix41 = true := by
  rw [suffix41, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe42⟩
private def suffix40 : List Cell := (5,10) :: suffix41
private theorem safe40 : branches (cap 4) suffix40 = true := by
  rw [suffix40, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe41⟩
private def suffix39 : List Cell := (5,5) :: suffix40
private theorem safe39 : branches (cap 4) suffix39 = true := by
  rw [suffix39, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe40⟩
private def suffix38 : List Cell := (4,20) :: suffix39
private theorem safe38 : branches (cap 4) suffix38 = true := by
  rw [suffix38, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe39⟩
private def suffix37 : List Cell := (4,15) :: suffix38
private theorem safe37 : branches (cap 4) suffix37 = true := by
  rw [suffix37, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe38⟩
private def suffix36 : List Cell := (4,10) :: suffix37
private theorem safe36 : branches (cap 4) suffix36 = true := by
  rw [suffix36, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe37⟩
private def suffix35 : List Cell := (4,5) :: suffix36
private theorem safe35 : branches (cap 4) suffix35 = true := by
  rw [suffix35, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe36⟩
private def suffix34 : List Cell := (4,0) :: suffix35
private theorem safe34 : branches (cap 4) suffix34 = true := by
  rw [suffix34, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe35⟩
private def suffix33 : List Cell := (3,20) :: suffix34
private theorem safe33 : branches (cap 4) suffix33 = true := by
  rw [suffix33, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe34⟩
private def suffix32 : List Cell := (3,15) :: suffix33
private theorem safe32 : branches (cap 4) suffix32 = true := by
  rw [suffix32, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe33⟩
private def suffix31 : List Cell := (3,10) :: suffix32
private theorem safe31 : branches (cap 4) suffix31 = true := by
  rw [suffix31, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe32⟩
private def suffix30 : List Cell := (3,5) :: suffix31
private theorem safe30 : branches (cap 4) suffix30 = true := by
  rw [suffix30, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe31⟩
private def suffix29 : List Cell := (3,0) :: suffix30
private theorem safe29 : branches (cap 4) suffix29 = true := by
  rw [suffix29, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe30⟩
private def suffix28 : List Cell := (2,20) :: suffix29
private theorem safe28 : branches (cap 4) suffix28 = true := by
  rw [suffix28, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe29⟩
private def suffix27 : List Cell := (2,15) :: suffix28
private theorem safe27 : branches (cap 4) suffix27 = true := by
  rw [suffix27, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe28⟩
private def suffix26 : List Cell := (2,10) :: suffix27
private theorem safe26 : branches (cap 4) suffix26 = true := by
  rw [suffix26, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe27⟩
private def suffix25 : List Cell := (2,5) :: suffix26
private theorem safe25 : branches (cap 4) suffix25 = true := by
  rw [suffix25, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe26⟩
private def suffix24 : List Cell := (2,0) :: suffix25
private theorem safe24 : branches (cap 4) suffix24 = true := by
  rw [suffix24, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe25⟩
private def suffix23 : List Cell := (1,29) :: suffix24
private theorem safe23 : branches (cap 4) suffix23 = true := by
  rw [suffix23, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe24⟩
private def suffix22 : List Cell := (1,28) :: suffix23
private theorem safe22 : branches (cap 4) suffix22 = true := by
  rw [suffix22, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe23⟩
private def suffix21 : List Cell := (1,27) :: suffix22
private theorem safe21 : branches (cap 4) suffix21 = true := by
  rw [suffix21, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe22⟩
private def suffix20 : List Cell := (1,26) :: suffix21
private theorem safe20 : branches (cap 4) suffix20 = true := by
  rw [suffix20, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe21⟩
private def suffix19 : List Cell := (1,24) :: suffix20
private theorem safe19 : branches (cap 4) suffix19 = true := by
  rw [suffix19, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe20⟩
private def suffix18 : List Cell := (1,23) :: suffix19
private theorem safe18 : branches (cap 4) suffix18 = true := by
  rw [suffix18, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe19⟩
private def suffix17 : List Cell := (1,22) :: suffix18
private theorem safe17 : branches (cap 4) suffix17 = true := by
  rw [suffix17, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe18⟩
private def suffix16 : List Cell := (1,20) :: suffix17
private theorem safe16 : branches (cap 4) suffix16 = true := by
  rw [suffix16, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe17⟩
private def suffix15 : List Cell := (1,19) :: suffix16
private theorem safe15 : branches (cap 4) suffix15 = true := by
  rw [suffix15, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe16⟩
private def suffix14 : List Cell := (1,18) :: suffix15
private theorem safe14 : branches (cap 4) suffix14 = true := by
  rw [suffix14, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe15⟩
private def suffix13 : List Cell := (1,17) :: suffix14
private theorem safe13 : branches (cap 4) suffix13 = true := by
  rw [suffix13, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe14⟩
private def suffix12 : List Cell := (1,15) :: suffix13
private theorem safe12 : branches (cap 4) suffix12 = true := by
  rw [suffix12, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe13⟩
private def suffix11 : List Cell := (1,14) :: suffix12
private theorem safe11 : branches (cap 4) suffix11 = true := by
  rw [suffix11, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe12⟩
private def suffix10 : List Cell := (1,13) :: suffix11
private theorem safe10 : branches (cap 4) suffix10 = true := by
  rw [suffix10, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe11⟩
private def suffix9 : List Cell := (1,12) :: suffix10
private theorem safe9 : branches (cap 4) suffix9 = true := by
  rw [suffix9, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe10⟩
private def suffix8 : List Cell := (1,10) :: suffix9
private theorem safe8 : branches (cap 4) suffix8 = true := by
  rw [suffix8, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe9⟩
private def suffix7 : List Cell := (1,9) :: suffix8
private theorem safe7 : branches (cap 4) suffix7 = true := by
  rw [suffix7, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe8⟩
private def suffix6 : List Cell := (1,8) :: suffix7
private theorem safe6 : branches (cap 4) suffix6 = true := by
  rw [suffix6, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe7⟩
private def suffix5 : List Cell := (1,7) :: suffix6
private theorem safe5 : branches (cap 4) suffix5 = true := by
  rw [suffix5, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe6⟩
private def suffix4 : List Cell := (1,5) :: suffix5
private theorem safe4 : branches (cap 4) suffix4 = true := by
  rw [suffix4, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe5⟩
private def suffix3 : List Cell := (1,4) :: suffix4
private theorem safe3 : branches (cap 4) suffix3 = true := by
  rw [suffix3, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe4⟩
private def suffix2 : List Cell := (1,3) :: suffix3
private theorem safe2 : branches (cap 4) suffix2 = true := by
  rw [suffix2, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe3⟩
private def suffix1 : List Cell := (1,2) :: suffix2
private theorem safe1 : branches (cap 4) suffix1 = true := by
  rw [suffix1, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe2⟩
private def suffix0 : List Cell := (1,0) :: suffix1
private theorem safe0 : branches (cap 4) suffix0 = true := by
  rw [suffix0, branches, Bool.and_eq_true]
  exact ⟨by decide +kernel,safe1⟩
theorem origin_bound : cap 5 pool = true := by
  have he : pool = suffix0 := by decide +kernel
  rw [he]
  exact safe0
end PEqualNP.Research.AffineClique
