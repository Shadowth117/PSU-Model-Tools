/*
NXOB/NXR Model Importer
By Shadowth117

Special thanks to:
Kion - Provided documentation and guidance on the format. 
Agrajag - Provided documentation and in depth explanations of parts of the format.
TGE - For the MaxScript Extension scripts
*/
ClearListener()
FileIn @"include\MaxScriptExtensions\FileStreamReader.ms"
FileIn @"include\MaxScriptExtensions\FileUtils.ms"

struct PSUBone
(
	flags,
	boneWeightUsed,
	nodeParent,
	nodefirstChild,
	nodeNextSibling,
	PosVec,
	RotVec,
	ScaleVec,
	tfm,
	unknown1,
	unknown2,
	MaxBone
)

struct PSUMatGroup
(
	diffuseTexCount,
	effTexCount,
	shortPad,
	matOffset
)

struct PSUMat
(
	a
)

struct PSUVGroup
(
	unknown_1,
	unknown_1_5,
	vertexFormat,
	unknown_3,
	vertexLength,
	nop,
	vertexCountOfs,
	vertexListOfs,
	boneBindingOfs,
	boneBindingCount,
	totalVertexCount,
	unknown_4,
	unknown_5,
	vertexScale,
	boneId,
	bonePalette,
	vertCount
)

struct PSUDraw
(
	unknownByte1,
	unknownByte2,
	unknownShort1,
	directDrawCount,
	directDrawOfs,
	indexedDrawCount,
	indexedDrawOfs,
	meshSet
)

struct PSUMesh
(
	centerX,
	centerY,
	centerZ,
	radius,
	top_level_bone,
	unknown_int1,
	mat_id,
	group_id,
	unknown_int2,
	unknown_int3
)

struct PSUAnimInfo
(
	unk1,
	unk2,
	unk3,
	unk4,
	unkShort1,
	unkShort2,
	nodeid,
	key1Start,
	key1End,
	key2Start,
	key2End,
	ksetCount,
	ksetSize,
	kpointer
)

struct vGroup
(
	uvCount,
	listOffset
)

struct PSUVList
(
	pos,
	nrm,
	uv,
	vcolor,
	valpha,
	weight,
	vec4
)

	
fn meshSplitter obj objInvArray =
(	
	max modify mode
	splitMeshes = #()
	skinMode = true
	if (for m in obj.modifiers where isKindOf m skin collect m).count < 1 then
	(
		skinMode = false
	)
	
	rigidUsed = getuserprop obj "rigid"
	
	--CREATE A BIT ARRAY TO INVERT FOR THE VERTICES
	faceCount = getNumFaces obj.mesh
	faceArray = #{1..faceCount}
	
	if skinMode == true then
	(
		--detachElementsWithSkin logic start. Original script by Liinko
		--BAKE AND REMOVE ZERO WEIGHTS ON THE SKIN
		objSkin = obj.skin
		modPanel.setCurrentObject objSkin
		vertCount = (skinOps.GetNumberVertices objSkin)
		skinOps.SelectVertices objSkin vertCount
		skinOps.bakeSelectedVerts objSkin
		objSkin.clearZeroLimit = 0.000
		skinOps.RemoveZeroWeights objSkin

		--STORE THE VERTEX WEIGHTS
		vertWeightsArray = #()

		for ele in objInvArray do
		(
			verts = meshop.getVertsUsingFace obj.mesh (faceArray - ele)
			vertsEle = #()

			for v in verts do
			(
				weights = #()
				_bones = #()

				wc = skinOps.GetVertexWeightCount objSkin v

				for b = 1 to wc do
				(
					append weights (skinOps.GetVertexWeight objSkin v b)
					append _bones (skinOps.GetVertexWeightBoneID objSkin v b)
				)
				while weights.count > 4 do
				(
					lowestWeightId = 1
					lowestWeight = weights[1]
					for i=2 to weights.count do
					(
						if lowestWeight > weights[i] then
						(
							lowestWeightId = i
							lowestWeight = weights[i]
						)
					)
					deleteItem _bones lowestWeightId
					deleteItem weights lowestWeightId
				)
				append vertsEle #(_bones,weights)
			)

			append vertWeightsArray vertsEle

		)
	)

	--CLONE AND FIX THE SKIN WEIGHTS
	for i = 1 to objInvArray.count do
	(
		--DUPE THE OBJECT
		max create mode
		maxOps.cloneNodes obj newNodes:&newObjs
		select newObjs[1]
		addModifier newObjs[1] (turn_to_mesh()) before:newObjs[1].modifiers.count #noprompt
		maxOps.CollapseNodeTo newObjs[1] newObjs[1].modifiers.count false
			
		meshop.deleteFaces newObjs[1] objInvArray[i]
		
		max modify mode
		if skinMode == true then
		(
			newObjSkin = newObjs[1].skin

			modPanel.setCurrentObject newObjSkin

			--LOAD THE VERTEX WEIGHTS
			vCount = (skinOps.GetNumberVertices newObjSkin)

			if vertWeightsArray[i][1] != undefined then
			(
				for v = 1 to vCount do
				(
					skinOps.ReplaceVertexWeights newObjSkin v vertWeightsArray[i][v][1] vertWeightsArray[i][v][2]
				)
			)
		) else 
		(
			if (for m in newObjs[1].modifiers where classof m == skin collect m).count > 0 then
			(
				for bn = 1 to (skinOps.GetNumberBones newObjs[1].skin) do
				(
					skinOps.removebone newObjs[1].skin 1
				)
			)
		)
		append splitMeshes newObjs[1]
	)
	
	if rigidUsed == true then
	(
		setuserpropbuffer obj ""
		skinMode = false
	)
	--gc light:false delayed:false
	
	splitMeshes
)

fn PSUImport modelFile extraHeader =
(
	local reader = FileStreamReader()
	TexNameArray = #()
	BoneNameArray = #()
	BoneDataArray = #()
	WeightedBoneArray = #()
	IndexDataArray = #()
	DrawDataArray = #()
	VlistDataArray = #()
	StripListArray = #()
	triArray = #()
	totalVertCount = -1
	totalVertCountOfs = -1
	
	--Get bone names
	xnaFile = (getFilenamePath modelFile) + ((getFilenameFile modelFile) + ".xna")
	print xnaFile
	if (doesFileExist xnaFile) then
	(
		reader.SetFile xnaFile false
		reader.SetBigEndian false
		reader.SeekSet( 0x8 )
		xnaNameOfs = reader.ReadU32()
		reader.SeekSet( xnaNameOfs )
		unk = reader.ReadU32()
		xnaNameCount = reader.ReadU32()
		pointer = reader.ReadU32()
		print xnaNameCount
		print (reader.GetPosition())
		for i = 1 to xnaNameCount do
		(
			BoneNameArray[i] = reader.ReadCString()
			print BoneNameArray[i]
		)
	)
	
	--Get texture names
	xntFile = (getFilenamePath modelFile) + ((getFilenameFile modelFile) + ".xnt")
	print xntFile
	if (doesFileExist xntFile) then
	(
		reader.SetFile xntFile false
		reader.SetBigEndian false
		reader.SeekSet( 0x8 )
		xntNameOfs = reader.ReadU32()
		reader.SeekSet( xntNameOfs )
		xntNameCount = reader.ReadU32()
		pointer = reader.ReadU32()
		print xntNameCount
		print (reader.GetPosition())
		for i = 1 to xntNameCount do
		(
			TexNameArray[i] = reader.ReadCString()
			print TexNameArray[i]
		)
	)
	
	-- Read file. Should support xnj and xnr maybe
	reader = FileStreamReader()
	reader.SetFile modelFile false
	reader.SetBigEndian false
	
	--Find model start, parse other things along the way
	keepChecking = true
	nxOffset = 0
	tempOff = 0
	modelFound = false
	do
	(
		type = reader.ReadU32()
		case type of
		(
			--NXIF
			0x4649584E: (keepChecking = false; reader.SeekCur( 0x1C ); if extraHeader then (nxOffset += reader.GetPosition()) else (nxOffset += 0x20))
			--NXR or NXOB
			0x52584E: (keepChecking = false; nxOffset -= reader.GetPosition() - nxOffset - 0x4; modelFound = true)
			0x424F584E: (keepChecking = false; nxOffset -= reader.GetPosition() - nxOffset - 0x4; modelFound = true)
			--NXTL
			0x4C54584E: (keepChecking = false; nxOffset -= reader.GetPosition() - nxOffset - 0x4)
			--NXNN
			0x4E4E584E: (keepChecking = false; nxOffset -= reader.GetPosition() - nxOffset - 0x4)
			--NXEF
			0x4645584E: (keepChecking = false; nxOffset -= reader.GetPosition() - nxOffset - 0x4)
		)
	) while keepChecking == true
	
	if modelFound == false then
	(
		keepChecking = true
		do
		(
			type = reader.ReadU32()
			case type of
			(
				--NXR or NXOB
				0x52584E: (keepChecking = false)
				0x424F584E: (keepChecking = false)
			)
		) while keepChecking == true
	)
	
	reader.SeekCur( 0x4 )
	Obj = reader.ReadU32() + nxOffset
	print (bit.intashex Obj)
	
	key = 0
	boneOff = 0x10
	--Since file offsets after the Obj offset seem to be absolute for some reason in some files, calc the "key". 
	
	reader.SeekCur( 0x8 )
	test0 = reader.ReadU16()
	test1 = reader.ReadU16()

	while test1 != 0xFFFF do --Technically doesn't account for all possible scenarios, but should account for all used scenarios
	(
		reader.SeekCur( 0xC)
		test0 = reader.ReadU16()
		test1 = reader.ReadU16()
		boneOff += 0x10
	)
	
	reader.SeekSet( Obj + 0x30)
	boneOffUnfixed = reader.ReadU32()
	key = boneOffUnfixed - boneOff - nxOffset
		
	if boneOff > 0x10 then
	(
		reader.SeekSet( 0x10 )
		totalVertCount = reader.ReadU32()
		totalVertCountOfs = reader.ReadU32() - key
	)
	reader.SeekSet( Obj )
	
	--Read Obj. I refer to it as such due to PSO2 calling it "OBJC"
	center = reader.ReadVec3F32() 				-- 0x0
	radius = reader.ReadF32()     				-- 0xC 
	matCount = reader.ReadU32()   				--0x10
	matOffset = reader.ReadU32() - key			--0x14
	vsetCount = reader.ReadU32()                --0x18
	vsetOffset = reader.ReadU32() - key         --0x1C
	indexGroupCount = reader.ReadU32()          --0x20
	indexGroupOffset = reader.ReadU32() - key   --0x24
	boneCount = reader.ReadU32()                --0x28
	boneTreeDepth = reader.ReadU32()            --0x2C
	boneOffset = reader.ReadU32() - key         --0x30
	unkOne = reader.ReadU32()                   --0x34
	drawCount = reader.ReadU32()                --0x38
	drawOffset = reader.ReadU32() - key         --0x3C
	unkCount = reader.ReadU32()                 --0x40
	
	print "mat info"
	print matCount
	print matOffset
	
	--Read Indices
	if indexGroupCount  > 0 then
	(
		reader.SeekSet( indexGroupOffset )
		for i = 1 to indexGroupCount do
		(
			uvCount = reader.ReadU32()
			vgOffset = reader.ReadU32() - key
			append IndexDataArray (VGroup uvCount:uvCount listOffset:vgOffset)
		)
		for i = 1 to IndexGroupCount do
		(
			reader.SeekSet( IndexDataArray[i].listOffset )
			unkStripInfo = reader.ReadU32()
			indexCount = reader.ReadU32()
			stripSetCount =  reader.ReadU32()
			stripLengthOfs = reader.ReadU32() - key
			indexOfs = reader.ReadU32() - key
			
			stripSetCounts = #()
			stripLists = #()
			reader.SeekSet(stripLengthOfs)
			for j = 1 to stripSetCount do
			(
				append stripSetCounts ((reader.ReadU16()))
			)
			reader.SeekSet(indexOfs)
			for j = 1 to stripSetCount do
			(
				/*
				stripSet = #()
				for k = 1 to stripSetCounts[j] do
				(
					append stripSet ((reader.ReadU16()))
				)
				append stripLists stripSet*/
				
				for k = 1 to (stripSetCounts[j]) do
				(
					append stripLists ((reader.ReadU16()))
				)
				append stripLists -1
				--print stripLists
			)
			append StripListArray stripLists
		)
	)
	
	--Read Bones
	if boneCount > 0 then
	(
		reader.SeekSet( boneOffset )
		for i = 1 to boneCount do
		(
			flags = reader.ReadU32() 
			boneWeightUsed = reader.ReadS16()
			nodeParent = reader.ReadS16()
			nodefirstChild = reader.ReadS16()
			nodeNextSibling = reader.ReadS16()
			PosVec = reader.ReadVec3F32()
			RotVec = reader.ReadVec3F32()
			ScaleVec = reader.ReadVec3F32()
			--reader.SeekCur( 0x31 )
			m11 = reader.ReadF32(); m12 = reader.ReadF32(); m13 = reader.ReadF32(); reader.ReadF32()
			m21 = reader.ReadF32(); m22 = reader.ReadF32(); m23 = reader.ReadF32(); reader.ReadF32()
			m31 = reader.ReadF32(); m32 = reader.ReadF32(); m33 = reader.ReadF32(); reader.ReadF32()
			m41 = reader.ReadF32(); m42 = reader.ReadF32(); m43 = reader.ReadF32(); reader.ReadF32()
			
			unknown1 = undefined
			unknown2 = undefined
			unknown1 = reader.ReadVec4F32()
			unknown2 = reader.ReadVec4F32()
			
			tfm = matrix3 [m11,m12,m13] [m21,m22,m23] [m31,m32,m33] [m41,m42,m43]
			append BoneDataArray (	PSUBone flags:flags boneWeightUsed:boneWeightUsed nodeParent:nodeParent nodefirstChild:nodefirstChild nodeNextSibling:nodeNextSibling PosVec:PosVec RotVec:RotVec ScaleVec:ScaleVec tfm:tfm unknown1:unknown1 unknown2:unknown2 MaxBone:undefined)
		)
	)
	if vsetCount > 0 then
	(
		--Read VertGroups
		reader.SeekSet( vsetOffset )
		vSets = #()
		for i = 1 to vsetCount do
		(
			uvCount = reader.ReadU32()
			vgOffset = reader.ReadU32() - key
			append vSets (VGroup uvCount:uvCount listOffset:vgOffset)
		)
		
		print "Vsets"
		--Read Vertex Sets
		vGroups = #()
		for i = 1 to vSets.count do
		(
			reader.SeekSet( vSets[i].listOffset )
			
			unk1 = reader.ReadU16()
			unk1_5 = reader.ReadU16()
			vertFormat = reader.ReadU32()  --0x4
			vertLen = reader.ReadU32()        --0x8 VertLen for NXOB?
			unk3 = reader.ReadU32()      --0xC VertBufferSize
			vertCountOf = reader.ReadU32() - key                    --0x10 can be vert list instead conditionally
			vertListOf = reader.ReadU32()                           --0x14
				--if vertListOf > 0 then (vertListOf -= key)
			bonePaletteOf = reader.ReadU32()                        --0x18
				if bonePaletteOf > 0 then (bonePaletteOf -= key)
			bonePaletteCount = reader.ReadU32()                     --0x1C
			totalVertCount = reader.ReadU32()                       --0x20
			unk4 = reader.ReadU32()                                 --0x24
			unk5 = reader.ReadU32()                                 --0x28
			vertScale = reader.ReadU32() --Maybe not actually vert scale? Definitely an int and not a float....
			
			reader.SeekSet( vertCountOf )
			vertCount = reader.ReadU16()
			
			bonePalette = #()
			if (bonePaletteOf != 0) then
			(
				print bonePaletteOf
				reader.SeekSet( bonePaletteOf )
				for j = 1 to vertListOf do
				(
					append bonePalette (reader.ReadU32())
					print bonePalette[j]
				)
			)
			
			print ("vset offset " + vSets[i].listOffset as string)
			print ("unk1 " + unk1 as string)
			print ("unk1_5 " + unk1_5 as string)
			print (bit.intashex vertFormat)
			print ("vertLen " + vertLen as string)
			print unk3
			print ("vertcountOf " + vertCountOf as string)
			print ("vertListOf " + vertListOf as string)
			print ("bonePaletteOf " + bonePaletteOf as string)
			print ("bonePaletteCount " + bonePaletteCount as string )
			print ("totalVertCount " + totalVertCount as string)
			print unk4
			print ("unk5 " + unk5 as string)
			print ("vertScale " + vertScale as string)
			
			print (bit.and vertFormat 3)                 --UV for NXR, Position for NXOB?
			print (bit.and (bit.shift vertFormat -2) 7)  --Color for NXR
			print (bit.and (bit.shift vertFormat -5) 3)  --Normals for NXR, Color for NXOB?
			print (bit.and (bit.shift vertFormat -7) 3)  --Position for NXR, UV for NXOB
			print (bit.and (bit.shift vertFormat -9) 3)  --Weights for NXR
			
			append vGroups (PSUVGroup unknown_1:unk1 unknown_1_5:unk1_5 vertexFormat:vertFormat unknown_3:unk3 vertexLength:vertLen vertexCountOfs:vertCountOf vertexListOfs:vertListOf boneBindingOfs:bonePaletteOf boneBindingCount:bonePaletteCount totalVertexCount:totalVertCount unknown_4:unk4 unknown_5:unk5 vertexScale:vertScale boneId:i bonePalette:bonePalette vertCount:vertCount)
		)
		
		--Read Vertices
		for i = 1 to vSets.Count do
		(
			print ("group " + i as string)
			if vGroups[i].vertexCountOfs != 0 or vGroups[i].vertexListOf != 0 then
			(
				count = vGroups[i].unknown_3
				reader.SeekSet( vGroups[i].vertexCountOfs )

				pos = (bit.and vGroups[i].vertexFormat 0x2) 
				nrm = (bit.and vGroups[i].vertexFormat 0x10)
				vcolor = (bit.and vGroups[i].vertexFormat 0x40)
				valpha = (bit.and vGroups[i].vertexFormat 0x80)
				uv = (bit.and vGroups[i].vertexFormat 0x100)
				weight = (bit.and vGroups[i].vertexFormat 0x8)
				vec4 = (bit.and vGroups[i].vertexFormat 0x200)
				
				print pos
				print nrm
				print vcolor
				print uv
				print weight
				print ("uvcheck2 " + (bit.and vGroups[i].vertexFormat 0x100) as string)
				
				posList = undefined
				if pos > 0 then
				(
					print ("pos " + i as string) 
					posList = #()
					posList[count] = [0, 0, 0]
				)
				vcolorList = undefined
				if vcolor > 0 then
				(
					print ("vcolor " + i as string) 
					vcolorList = #()
					vcolorList[count] = [0, 0, 0]
				)
				valphaList = undefined
				if valpha > 0 then
				(
					print ("valpha " + i as string) 
					valphaList = #()
					valphaList[count] = [0, 0, 0]
				)
				uvList = undefined
				if uv > 0 then
				(
					print ("uv " + i as string) 
					uvList = #()
					uvList[count] = [0, 0, 0]
				)
				nrmList = undefined
				if nrm > 0 then
				(
					print ("nrm " + i as string) 
					nrmList = #()
					nrmList[count] = [0, 0, 0]
				)
				weightList = undefined
				if weight > 0 then
				(
					print ("weight " + i as string) 
					weightList = #()
					weightList[count] = [0, 0, 0]
				)
				vec4List = undefined
				if vec4 > 0 then
				(
					vec4List = #()
					vec4List[count] = [0, 0, 0, 0]
				)
				
				for j = 1 to (count) do
				(
					offset = 0
					if pos > 0 then
					(
						vertPos = 0
						case pos of
						(
							--1: (vertPos = reader.ReadVec3F16(); offset += 0x6)
							--2: (vertPos = reader.ReadVec3F32(); offset += 0xC)
							default: (vertPos = reader.ReadVec3F32(); offset += 0xC)
						)
						posList[j] = vertPos
					)
					if weight > 0 then
					(
						weightPoint = reader.ReadVec3F32()
						vertWeight = #()
						vertWeight[4] = 1 - weightPoint.X - weightPoint.Y - weightPoint.Z
						vertWeight[1] = weightPoint.X
						vertWeight[2] = weightPoint.Y
						vertWeight[3] = weightPoint.Z
						
						weightList[j] = vertWeight
						offset += 0xC
					)
					if nrm > 0 then
					(
						vertNrm = 0
						case nrm of
						(
							--1: (vertNrm = reader.ReadVec3F16(); offset += 0x6)
							--2: (vertNrm = reader.ReadVec3F32(); offset += 0xC)
							default: (vertNrm = reader.ReadVec3F32(); offset += 0xC)
						)
						nrmList[j] = vertNrm
					)
					if vcolor > 0 then
					(
						b = reader.ReadU8()
						g = reader.ReadU8()
						r = reader.ReadU8()
						a = reader.ReadU8()
						vcolorItem = (color r g b a)
						vcolorList[j] = vcolorItem 
						offset += 0x4
					)
					if valpha > 0 then
					(
						valphaList[j] = reader.ReadF32()
						offset += 0x4
					)
					if uv > 0 then
					(	
						vertUv = 0
						case uv of
						(
							--1: (vertUv = reader.ReadVec2F16(); offset += 0x6)
							--2: (vertUv = reader.ReadVec2F32(); offset += 0xC)
							default: (vertUv = reader.ReadVec2F32(); offset += 0xC)
						)
						vertUV.Y = -vertUV.Y
						uvList[j] = vertUv
					)
					if vec4 > 0 then
					(
						vec4List[j] = reader.ReadVec4F32(); offset += 0x10
					)
					if offset < vGroups[i].vertexLength then
					(
						reader.SeekCur(vGroups[i].vertexLength - offset)
					)
				)
				append VlistDataArray (PSUVList pos:posList nrm:nrmList vcolor:vcolorList valpha:valphaList uv:uvList weight:weightList vec4:vec4List)
			)
			--print VlistDataArray[i]
		)
	)
	
	if matCount > 0 then
	(
		--Read Mats
		reader.SeekSet( matOffset )
		for i = 1 to matCount do
		(
			
		)
	)
	
	if drawCount > 0 then
	(
		--Read Draw
		reader.SeekSet( drawOffset )
		for i = 1 to drawCount do
		(
			print ("Draw " + i as string)
			--print (bit.intashex (reader.GetPosition()))
			unknownByte1 = reader.ReadU8()
			unknownByte2 = reader.ReadU8()
			unknownShort1 = reader.ReadU16()
			directDrawCount = reader.ReadU32()
			directDrawOfs = reader.ReadU32() - key   
			indexedDrawCount = reader.ReadU32()
			indexedDrawOfs = reader.ReadU32() - key   
			--print (bit.intashex directDrawOfs)
			--print (bit.intashex indexedDrawOfs)
				
			draw = (PSUDraw unknownByte1:unknownByte1 unknownByte2:unknownByte2 unknownShort1:unknownShort1 directDrawCount:directDrawCount directDrawOfs:directDrawOfs indexedDrawCount:indexedDrawCount indexedDrawOfs:indexedDrawOfs meshSet:undefined)


			--print draw
			pos = reader.GetPosition()
			
			reader.SeekSet( directDrawOfs )
			meshSet = #()
			for j = 1 to directDrawCount do
			(
				print (bit.intashex (reader.GetPosition()))
				print ("Mesh " + j as string + " Draw: " + i as string)
				centerX = reader.ReadF32()
				centerY = reader.ReadF32()
				centerZ = reader.ReadF32()
				radius = reader.ReadF32()
				top_level_bone = reader.ReadU32()
				unknown_int1 = reader.ReadU32()
				mat_id = reader.ReadU32()
				group_id = reader.ReadU32()
				unknown_int2 = reader.ReadU32()
				unknown_int3 = reader.ReadU32()
					
				append meshSet (PSUMesh centerX:centerX centerY:centerY centerZ:centerZ radius:radius top_level_bone:top_level_bone unknown_int1:unknown_int1 mat_id:mat_id group_id:group_id unknown_int2:unknown_int2 unknown_int3:unknown_int3)
				print meshSet[j]
			)
			
			draw.meshSet = meshSet
			append DrawDataArray draw
			
			reader.SeekSet( pos )
		)
	)
	
	reader.close()
	
	--Create bones in max
	nodeCounter = 0
	for node in BoneDataArray do
    (
		tfm = (inverse node.tfm);
		
        local parentBone = undefined;
        if ( node.nodeParent != -1 ) then
		(
            parentBone = BoneDataArray[node.nodeParent+1].MaxBone;
		)
		
		newBone = bonesys.createbone \
			tfm.row4 \
			(tfm.row4 + 0.01 * (normalize tfm.row3)) \
			(normalize tfm.row1);
				
		if(BoneNameArray.count > 0) then
		(
			newBone.name = ("(" + nodeCounter as string + ")") + BoneNameArray[nodeCounter + 1];
		)
        newBone.width  = 0.001;
        newBone.height = 0.001;
        newBone.transform = tfm;
        newBone.setBoneEnable false 0;
        newBone.wirecolor = ([0,196,196] as color);
        newBone.showlinks = true;
        newBone.pos.controller      = TCB_position ();
        newBone.rotation.controller = TCB_rotation ();
		
		
		if (ResizeChecked == true) then 
		(
			newBone.pos = [newBone.pos.x * ResizeValue, newBone.pos.y * ResizeValue, newBone.pos.z * ResizeValue]
		)
        newBone.Parent = parentBone;
        nodeCounter += 1;
        node.MaxBone = newBone;
		if node.boneWeightUsed > -1 then
		(
			append WeightedBoneArray newBone
		)
    )
	
	--Process tris. Add faces for same vertex group to face array index of that group + 1. After mesh creation, loop through and assign mat to faces based on order 
	faceMatListArray = #()
	faceListArray = #()
	extrafaceBitArray = #()
	extraRigidBoneArray = #()
	rigidVertArray = #()
	
	for i = 1 to VlistDataArray.count do
	(
		extrafaceBitArray[i] = #()
		extraRigidBoneArray[i] = #()
		rigidVertArray[i] = #()
		rigidVertArray[i][VlistDataArray[i].pos.count] = 0
	)
	for draw in drawDataArray do
	(
		for drawMesh in draw.meshSet do
		(
			meshRigidBone = drawMesh.top_level_bone 
			drawBitArray = #{}
			
			print drawMesh
			print drawMesh.group_id
			if faceMatListArray[drawMesh.group_id+1] == undefined then
			(
				faceMatListArray[drawMesh.group_id+1] = #()
				faceListArray[drawMesh.group_id+1] = #()
			)
			
			flip = false
			dupe = false
			j = 1
			--Condense faces for export. Prepare with bit arrays for splitting as necessary via meshsplitter
			while j < (StripListArray[drawMesh.unknown_int2+1].count - 1) do
			(
				if StripListArray[drawMesh.unknown_int2+1][j + 2] < 0 then
				(
					j += 3
				) else 
				(
					face = [(StripListArray[drawMesh.unknown_int2+1][j]+1), (StripListArray[drawMesh.unknown_int2+1][j + 1]+1), (StripListArray[drawMesh.unknown_int2+1][j + 2]+1)]
					faceArr = #((StripListArray[drawMesh.unknown_int2+1][j]+1), (StripListArray[drawMesh.unknown_int2+1][j + 1]+1), (StripListArray[drawMesh.unknown_int2+1][j + 2]+1))
					
					if(flip) then
					(
						temp = face.x
						face.x = face.y
						face.y = temp
					) 
					flip = not flip
					
					faceExists = finditem faceListArray[drawMesh.group_id+1] face
					
					--Check if this is a degen face
					for f = 1 to faceArr.count-1 while skip == false do
					(
						for g = 1 to faceArr.count while skip == false do
						(
							if f != g and faceArr[f] == faceArr[g] then
							(
								faceExists = 0
							)
						)
					)
					
					if faceExists > 0 then
					(
						dupe = true
					) else (
						rigidVertArray[drawMesh.group_id+1][face.x] = drawMesh.top_level_bone
						rigidVertArray[drawMesh.group_id+1][face.y] = drawMesh.top_level_bone
						rigidVertArray[drawMesh.group_id+1][face.z] = drawMesh.top_level_bone
					)
					
					append faceListArray[drawMesh.group_id+1] face
					append faceMatListArray[drawMesh.group_id+1] (drawMesh.mat_id + 1)
					append drawBitArray faceListArray[drawMesh.group_id+1].count

					j += 1
				)
			)
			
			--Only add here if we're resolved to split current drawMesh
			if dupe == true then
			(
				append extrafaceBitArray[drawMesh.group_id+1] drawBitArray
				append extraRigidBoneArray[drawMesh.group_id+1] drawMesh.top_level_bone
			) 
		)
	)
	for i = 1 to faceListArray.count do
	(
		fullBit = -#{1..faceListArray[i].count}
		for j = 1 to extrafaceBitArray[i].count do
		(
			extrafaceBitArray[i][j] = -(fullbit + extrafaceBitArray[i][j])
		)
	)
	--Create and assign data to meshes
	counter = 0
	vcolorsUsed = false
	for i = 1 to faceListArray.count do
	(
		newMesh = mesh name:("mesh" + counter as string) pos:[0,0,0] \
			vertices:VlistDataArray[i].pos faces:faceListArray[i]
		
		--Assign material ids
		for j = 1 to newMesh.faces.count do
		(
			setFaceMatID newMesh j faceMatListArray[i][j]
		)
		
		--Assign UVs
		if VlistDataArray[i].uv != undefined then
		(
			meshop.setNumMaps newMesh ((meshop.getNumMaps newMesh) + 1) keep:true
			meshop.setMapSupport newMesh 1 true
			meshop.setNumMapVerts newMesh 1 VlistDataArray[i].uv.Count
			meshop.setNumMapFaces newMesh 1 (meshop.getNumFaces newMesh) 
			
			for j = 1 to VlistDataArray[i].uv.Count do
			(
				meshop.setMapVert newMesh 1 j [VlistDataArray[i].uv[j].X, VlistDataArray[i].uv[j].Y, 0]
			)
			for j = 1 to (meshop.getNumFaces newMesh) do
			(
				face = getFace newMesh j
				meshop.setMapFace newMesh 1 j face
			)
		)
		
		--Assign UVs?
		if VlistDataArray[i].vec4 != undefined then
		(
			meshop.setNumMaps newMesh ((meshop.getNumMaps newMesh) + 2) keep:true
			meshop.setMapSupport newMesh 1 true
			meshop.setNumMapVerts newMesh 1 VlistDataArray[i].vec4.Count
			meshop.setNumMapFaces newMesh 1 (meshop.getNumFaces newMesh) 
			meshop.setMapSupport newMesh 2 true
			meshop.setNumMapVerts newMesh 2 VlistDataArray[i].vec4.Count
			meshop.setNumMapFaces newMesh 2 (meshop.getNumFaces newMesh) 
			
			for j = 1 to VlistDataArray[i].vec4.Count do
			(
				meshop.setMapVert newMesh 1 j [VlistDataArray[i].vec4[j].X, VlistDataArray[i].vec4[j].Y, 0]
				meshop.setMapVert newMesh 2 j [VlistDataArray[i].vec4[j].Z, VlistDataArray[i].vec4[j].W, 0]
			)
			for j = 1 to (meshop.getNumFaces newMesh) do
			(
				face = getFace newMesh j
				meshop.setMapFace newMesh 1 j face
				meshop.setMapFace newMesh 2 j face
			)
		)
		
		--Assign Vcolors
		if VlistDataArray[i].vcolor != undefined then
		(
			vcolorsUsed = true
			meshop.setNumMaps newMesh ((meshop.getNumMaps newMesh) + 1) keep:true
			meshop.setMapSupport newMesh -2 true
			meshop.setNumMapVerts newMesh -2 VlistDataArray[i].vcolor.Count
			meshop.setNumMapFaces newMesh -2 (meshop.getNumFaces newMesh) 
			setNumCPVVerts newMesh newMesh.numverts
			
			-- Set vertex coloring -- 
			for j = 1 to VlistDataArray[i].vcolor.Count do
			(
				setvertcolor newMesh j (color VlistDataArray[i].vcolor[j].r VlistDataArray[i].vcolor[j].g VlistDataArray[i].vcolor[j].b VlistDataArray[i].vcolor[j].a)
				if VlistDataArray[i].valpha != undefined then
				(
					meshop.setvertalpha newMesh -2 j (VlistDataArray[i].valpha[j])
				) else 
				(
					meshop.setvertalpha newMesh -2 j (VlistDataArray[i].vcolor[j].a)
				)
			)
			for j = 1 to (meshop.getNumFaces newMesh) do
			(
				face = getFace newMesh j
				meshop.setMapFace newMesh -2 j face
			)
			defaultVCFaces newMesh
		)
		
		
		--Assign normals
		if VlistDataArray[i].nrm != undefined then
		(
			--Set Normals
			max modify mode
			select newMesh
			addmodifier newMesh (Edit_Normals ()) ui:off
			nMNorms = newMesh.modifiers[#Edit_Normals]	
				
			--Finish setting normals
			newMesh.Edit_Normals.MakeExplicit selection:#{1..newMesh.verts.count}
			EN_convertVS = newMesh.Edit_Normals.ConvertVertexSelection
			EN_setNormal = newMesh.Edit_Normals.SetNormal
			EN_getNormal = newMesh.Edit_Normals.GetNormal
			EN_getVertexID = newMesh.Edit_Normals.GetVertexID
			EN_getNormalID = newMesh.Edit_Normals.GetNormalID
			EN_getDegree = newMesh.Edit_Normals.GetFaceDegree
			EN_setSelection = newMesh.Edit_Normals.SetSelection
			--EN_makeExplicit = newMesh.Edit_Normals.MakeExplicit
			EN_setExplicit = newMesh.Edit_Normals.SetNormalExplicit
			normID = #{}

			
			for v = 1 to newMesh.verts.count do(
				--free normID
				EN_convertVS #{v} &normID
				for id in normID do 
				(
					EN_setSelection #{id}
					EN_setExplicit id explicit:true
					EN_setNormal id VlistDataArray[i].nrm[v]
				)
			)
			
			update newMesh
			maxOps.CollapseNodeTo newMesh 1 true -- Collapse the Edit Normals modifier
			update newMesh
		)
		
		count =  0
		Max modify mode
		Select newMesh
		skinMod = Skin()
		AddModifier newMesh skinMod
		--If there's proper weights, use them. Otherwise, the model is probably a rigid assignment and so we apply accordingly.
		if VlistDataArray[i].weight != undefined then
		(
			boneArr = #()
			--Apply Skinned Nodes 
			boneCounter = 1
			for b in vGroups[i].bonePalette do
			(
				SkinOps.AddBone skinMod (WeightedBoneArray[b+1]) 0
				append boneArr boneCounter
				boneCounter += 1
			)
			
			-- Set the weight for each of them 
			ModPanel.SetCurrentObject skinMod
			
			for j = 1 to newMesh.numverts do 
			(
				skinOps.unNormalizeVertex skinMod j true
				trueWeightArr = #()
				for w = 1 to boneArr.count do
				(
					trueWeightArr[w] = VlistDataArray[i].weight[j][w]
				)
				skinOps.ReplaceVertexWeights skinMod j boneArr trueWeightArr
			)
		) else 
		(
			setuserprop newMesh "rigid" true
			boneIds = makeUniqueArray rigidVertArray[i] 
			for id = 1 to boneIds.count do
			(
				boneIds[id] += 1
				boneId = BoneDataArray[boneIds[id]].MaxBone
				SkinOps.AddBone skinMod boneId 0
			)
			
			for j = 1 to newMesh.numverts do 
			(
				if rigidVertArray[i][j] != undefined then
				(
					trueWeightArr = #()
					convertedIdArr = #()
					for id = 1 to boneIds.count do
					(
						append convertedIdArr id
						if (rigidVertArray[i][j] + 1) == boneIds[id] then
						(
							append trueWeightArr 1
						) else 
						(
							append trueWeightArr 0
						)
					)
					skinOps.ReplaceVertexWeights skinMod j convertedIdArr trueWeightArr
				)
			)
		) 
		
		--Split submeshes if they contain duplicate faces
		subMeshes = #()
		if extrafaceBitArray[i].count > 0 then
		(
			
			subMeshes = meshSplitter newMesh extrafaceBitArray[i]
			
			for id = 1 to extraRigidBoneArray[i].count do
			(
				if (getuserprop submeshes[id] "rigid") == true then
				(
					setuserpropbuffer submeshes[id] ""
					skinOps.Addbone submeshes[id].skin WeightedBoneArray[extraRigidBoneArray[i][id]+1] 0
				)
			)
		)
		
		
		meshop.removeDegenerateFaces newMesh
		for subMesh in subMeshes do
		(
			meshop.removeDegenerateFaces subMesh
		)
		counter += 1
	)
	
	if vcolorsUsed then
	(
		for o in geometry do(
		  o.showVertexColors = true 
		)
	)
	completeRedraw()
)

fn PSUAnimImport animFile =
(
	local reader = FileStreamReader()
	reader.SetFile animFile false
	reader.SetBigEndian false
	sceneBones = #()
	nodeInfo = #()
	
	--Get nodes
	for o in objects where isGroupHead o == false and isGroupMember o == false and (superclassof o == helper or classOf o == Biped_Object or classOf o == BoneGeometry or (try(classOf o.transform.controller == BipSlave_Control)catch(false))) do
	(
		if (findstring o.name ")" != undefined) then
		(
			id = (filterstring o.name "()")[1]
			sceneBones[( (id as integer) + 1)] = o
		) else (
			append sceneBones o
		)
	)
	
	--Read anim settings
	reader.SeekSet( 0x8 )
	animFPSAddr = reader.ReadU32() + 8
	reader.SeekCur( animFPSAddr )
	framerate = reader.ReadF32()
	reader.SeekCur( -0x14 )
	animStart = reader.ReadF32()
	animEnd = reader.ReadF32()
	nodeCount = reader.ReadU32()
	print nodeCount
	print animStart
	print animEnd
	
	reader.SeekCur( -0x38)
	for i = 1 to nodeCount do
	(
		unk1 = reader.ReadU8()
		unk2 = reader.ReadU8()
		unk3 = reader.ReadU8()
		unk4 = reader.ReadU8()
		
		unkShort1 = reader.ReadU16()
		unkShort2 = reader.ReadU16()
		
		nodeid = reader.ReadU32()
		key1Start = reader.ReadF32()
		key1End = reader.ReadF32()
		key2Start = reader.ReadF32()
		key2End = reader.ReadF32()
		ksetCount = reader.ReadU32()
		ksetSize = reader.ReadU32()
		kpointer = reader.ReadU32()
		
		print "nodeid"
		print nodeid
		nodeInfo[nodeCount - i + 1] = (PSUAnimInfo unk1:unk1 unk2:unk2 unk3:unk3 unk4:unk4 unkShort1:unkShort1 unkShort2:unkShort2 nodeid:nodeid key1Start:key1Start key1End:key1End key2Start:key2Start key2End:key2End ksetCount:ksetCount ksetSize:ksetSize kpointer:kpointer)

		reader.SeekCur( -0x50 )
	)
	key = nodeInfo[1].kpointer - 0x10
	
	with animate on
	(
		for i = 1 to nodeCount do
		(
			for j = 1 to nodeInfo[i].ksetCount do
			(
				id = nodeInfo[i].nodeid + 1
				print id
				truepointer = (nodeInfo[i].kpointer - key) + ((j - 1) * 0x8)
				reader.SeekSet( truepointer )
				print truepointer
				
				if (bit.and nodeInfo[i].unk2 0x1) > 0 then
				(
					frame = reader.ReadF32()
					data = reader.ReadF32()
					print frame
					print data
					at time frame sceneBones[id].pos.x = data
				) else if (bit.and nodeInfo[i].unk2 0x2) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadU16()
					at time frame sceneBones[id].pos.y = data
				) else if (bit.and nodeInfo[i].unk2 0x4) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadU16()
					at time frame sceneBones[id].pos.z = data
				) else if (bit.and nodeInfo[i].unk2 0x8) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadU16()
					at time frame (rotate sceneBones[id] (eulerangles data 0 0))
				) else if (bit.and nodeInfo[i].unk2 0x10) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadF32()
					at time frame (rotate sceneBones[id] (eulerangles 0 data 0))
				) else if (bit.and nodeInfo[i].unk2 0x20) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadF32()
					at time frame (rotate sceneBones[id] (eulerangles 0 0 data))
				) else if (bit.and nodeInfo[i].unk2 0x40) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadF32()
					at time frame (scale sceneBones[id] [data, data, data])
				) else if (bit.and nodeInfo[i].unk2 0x80) > 0 then
				(
					frame = reader.ReadF32() 
					data = reader.ReadF32()
					print "unknown data 0x80"
				) else (
					frame = reader.ReadF32() 
					data = reader.ReadF32()
					print ("unknown data " + nodeInfo[i].unk2 as string)
				)
			)
		)
	)
	
	reader.close()
	animationrange = interval animStart animEnd
)

rollout psuImportRollout "PSU Model Importer"
(
		--------------------
	-- User Interface --
	--------------------
	group "About"
	(
		label lab1 "PSU Model Importer"
		Label lab2 "By Shadowth117"
	)
	group "Settings"
	(
		checkBox autoSizeCheckBox "Rescale" checked:false align:#center
		spinner autoSizeSpinner "Scale by:" align:#center type:#float range:[0,10000,100] enabled:false
		checkBox YZCheckBox "Y-Z Axis Flip" checked: true align:#center
		checkBox PRSImport "Use PRS Data" checked: false align:#center
		checkBox ExtraHeader "Agrajag Header" checked: false align:#center
	)	
	group "Import"
	(
		button importButton "Import..."
	)

	group "Import Anim"
	(
		button importAnimButton "Import Anim..."
	)
	
	on autoSizeCheckBox changed nowChecked do
	(
		autoSizeSpinner.enabled = nowChecked
	)
	
	on importButton pressed do
	(
		local objFileName = undefined
		-- Open up a dialog box
		objFileName = getOpenFileName caption:"Import Phantasy Star Universe .xnr" \
					types:"PSU Model (*.xnr, *.xnj)|*.xnr;*.xnj|All Files (*.*)|*.*|"
        if (objFileName != undefined) then
		(
			PSUImport objFileName ExtraHeader.checked
		)
		
		-- Redraw max viewports
		max views redraw
		-- Ta-daa! You should now see a lovely new imported model in all its glory.
		--print "Import completed."
	)
	
	on importAnimButton pressed do
	(
		local objFileName = undefined
		-- Open up a dialog box
		objFileName = getOpenFileName caption:"Import Phantasy Star Universe .xnm" \
					types:"PSU Anim (*.xnm, *.xnm)|*.xnm;*.xnm|All Files (*.*)|*.*|"
        if (objFileName != undefined) then
		(
			PSUAnimImport objFileName
		)
		
		-- Redraw max viewports
		max views redraw
		-- Ta-daa! You should now see a lovely new imported model in all its glory.
		--print "Import completed."
	)
)
createDialog psuImportRollout 160 320