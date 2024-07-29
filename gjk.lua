local m = {}
--Implementation of Gilbert Johnson Keerthi collision detection algorithm
--Dependencies
--Type declarations
type Shape = {
	vertices:{Vector2}|{Vector3}, --Ignored if isCircle is true
	position:Vector2|Vector3,
	isCircle:boolean, --If this is true then our support function has to treat it differently
	radius:number, --Not used if isCircle is false
	dim:number,
}
--Config vars
local ApproximatePrecision = 4 --Higher digits means more precision when using ApproximatelyEqual
local ShapeDimensionEnums = {
	Dim2 = 0,
	Dim3 = 1,
}
local debugMode = false
--Global vars
--Helper functions
local function ApproximatelyEqual(num1:number, num2:number):boolean
	--Shifts the decimal place back by ApproximatePrecision places, rounds the result to the nearest integer and sees if they're equivalent
	return math.round(num1*math.pow(10, ApproximatePrecision)) == math.round(num2*math.pow(10, ApproximatePrecision))
end

local function SupportFunction3D(Dir:Vector3, Shape:Shape):Vector3? --Dir must be a unit vector
	if Shape.dim ~= ShapeDimensionEnums.Dim3 then error("Must provide a shape that has a dim equal to dim2") return end
	--If the shape is a circle then the support point is the point along the circumference the direction vector
	if Shape.isCircle then
		return Shape.position::Vector3 + Dir*Shape.radius
	end
	--For a non-circle, dot the direction with the normalised vectors to each vertex and pick the vertex with the highest product
	local highestDot, highestVertex = nil,nil
	for k,v in Shape.vertices::{Vector3} do
		local vert = v.Unit
		local prod = vert:Dot(Dir)
		if highestDot == nil or highestDot < prod then
			highestDot = prod
			highestVertex = v
		end
	end
	return highestVertex + Shape.position
end


local function SupportFunction2D(Dir:Vector2, Shape:Shape):Vector2?
	if Shape.dim ~= ShapeDimensionEnums.Dim2 then error("Must provide a shape that has a dim equal to dim2") return end
	--If the shape is a circle then the support point is the point along the circumference the direction vector
	if Shape.isCircle then return Dir * Shape.radius end
	--If the shape doesn't have vertices for some reason then error
	if #Shape.vertices == 0 then error("Shape must have defined vertices!") return nil end
	--Essentially, this function maximises the dot product between Dir and the direction vector between each vertex and the origin
	local highestDot = nil
	local highestIndex = -1 --Points to the index of the vertex that has the highest dot
	--Loop through the vertices of the shape and dot it with Dir
	for i = 1, #Shape.vertices do
		local dp = (Shape.vertices[i]+Shape.position):Dot(Dir)
		if highestDot == nil or highestDot < dp then
			highestDot = dp
			highestIndex = i
		end
	end
	return Shape.vertices[highestIndex]
end

local function SupportFunction(Dir:Vector3|Vector2, Shape:Shape): Vector3|Vector2|nil --Finds the farthest point on the given shape with in the given direction assuming that shape is 3D
	--If the shape doesn't have vertices for some reason then error
	if #Shape.vertices == 0 then error("Shape must have defined vertices!") return nil end
	--Essentially, this function maximises the dot product between Dir and the direction vector between each vertex and the origin
	local highestDot = nil
	local highestIndex = -1 --Points to the index of the vertex that has the highest dot
	--Loop through the vertices of the shape and dot it with Dir
	for i = 1, #Shape.vertices do
		local dp = Shape.vertices[i]:Dot(Dir)
		if highestDot == nil or highestDot < dp then
			highestDot = dp
			highestIndex = i
		end
	end
	return Shape.vertices[highestIndex]
end

local function TripleProduct(Dir1:Vector2|Vector3, Dir2:Vector2|Vector3):Vector3
	--Returns a direction vector normal to Dir1
	---By way of 1) casting both Dirs to Vector3 if it isnt already in one then getting the cross product between the two and then crossing that with Dir1
	if typeof(Dir1) == "Vector2" then Dir1 = Vector3.new(Dir1.X, 0, Dir1.Y) end
	if typeof(Dir2) == "Vector2" then Dir2 = Vector3.new(Dir2.X, 0, Dir2.Y) end
	--Or (Dir1 x Dir2) x Dir1
	local TripleProduct = (Dir1::Vector3):Cross((Dir2::Vector3)):Cross((Dir1::Vector3))
	--Cast it back into a Vector2
	return TripleProduct
end

local c = 1 -- To track how many simplex steps we've made

local function handleSimplex3D(simplex:{Vector3}):(boolean, Vector3?)
	if #simplex == 2 then
		--The next direction returned is the direction normal to the two points we have, in the direction of the origin
		local edge1 = (simplex[2] - simplex[1]).Unit
		local originVector = simplex[2].Unit
		--If the origin is along the edge then we stop
		if originVector:Dot(edge1) == 1 then return true, nil end
		local normalDir = TripleProduct(edge1, originVector).Unit
		--If the normalDir is not facing the origin then flip it
		if originVector:Dot(normalDir) < 0 then 
			normalDir = -normalDir
		end
		return false, normalDir.Unit
	elseif #simplex ==  3 then
		--We have a 2D simplex here so the next direction we need to point in is in the direction orthogonal to both edges towards the origin
		--If the origin is coplanar to the 2D simplex then return true
		local edge1 = (simplex[3] - simplex[1]).Unit
		local edge2 = (simplex[3] - simplex[2]).Unit
		local normalVector = edge1:Cross(edge2).Unit
		local originVector = (simplex[3]).Unit
		--The coplanar check is just seeing if the origin vector is orthogonal to the normal vector
		if normalVector:Dot(originVector) == 0 then return true, nil end
		--Check if the normal vector points towards the origin and invert it if not
		if normalVector:Dot(originVector) < 0 then
			normalVector = -normalVector
		end
		
		return false, normalVector
	elseif #simplex == 4 then
		if debugMode then print("---") end
		--Define the 3 edges between the 4th point, assuming that the vertices are as follows : A B C D where D is the most recent point
		local AD = (simplex[4] - simplex[1]).Unit --This is A -> D
		local BD = (simplex[4] - simplex[2]).Unit 
		local CD = (simplex[4] - simplex[3]).Unit
		--Since we want the vector simplex[4] -> origin since that matches all our vectors
		local originVector = (-simplex[4]).Unit
		--We have to check if the origin is coplanar with any of the 
		-- 3 pairs of surfaces on our tetrahedron like we did in our 3-sided simplex
		local triangle_ABD_norm = AD:Cross(BD).Unit 
		local triangle_BCD_norm = BD:Cross(CD).Unit 
		local triangle_ACD_norm = CD:Cross(AD).Unit
		--Check which direction the normals are facing in comparison to the vertex that wasn't used and invert them if they're facing that vertex
		if triangle_ABD_norm:Dot(-CD) > 0 then 
			triangle_ABD_norm = -triangle_ABD_norm 
		end
		
		if triangle_ACD_norm:Dot(-BD) > 0 then
			triangle_ACD_norm = -triangle_ACD_norm
		end
		
		if triangle_BCD_norm:Dot(-AD) > 0 then
			triangle_BCD_norm = -triangle_BCD_norm
		end
		--Oh actually if the dot is 0 then its coplanar so anything equal to 
		--or less than 0 gives us a simplex that contains the origin so 
		-- unless we need to specifically indicate that its coplanar we don't need that check
		
		--Dot the normal with the origin vector 
		if triangle_ABD_norm:Dot(originVector) > 0 then 
			table.remove(simplex, 3) --Remove point C since we know that is in the wrong direction
			return false, triangle_ABD_norm
		end
		
		--Repeat for the next 2 triangles BCD and ACD

		--if ApproximatelyEqual(triangle_BCD_norm:Dot(originVector), 0) then print("Coplanar") return true, nil end
		if triangle_BCD_norm:Dot(originVector) > 0 then
			table.remove(simplex, 1)
			return false, triangle_BCD_norm
		end
		--One more for ACD
		--if ApproximatelyEqual(triangle_ACD_norm:Dot(originVector), 0) then print("Coplanar") return true, nil end
		if triangle_ACD_norm:Dot(originVector) > 0 then
			table.remove(simplex, 2)
			return false, triangle_ACD_norm
		end
		--If the origin is within the simplex then all 3 of those guards shouldn't be reached so we can return true
		return true, nil
	end
	error(`No case is defined for {#simplex}`)
	return false, nil
end

local function handleSimplex(simplex:{Vector2}):(boolean, Vector2?)
	--Based on how many vertices are in our simplex, do different things
	if #simplex == 2 then
		--Line case
		--Grab two vectors: One between SImplex[1] and Simplex[2] and between Simplex[2] and origin
		local vertexVector = (simplex[1] - simplex[2]).Unit
		local originVector = -simplex[2].Unit
		--We need to check one edge case where the origin lies along the vector formed using our two vertices
		if ApproximatelyEqual(vertexVector:Dot(originVector),1) then return true, nil end
		--Otherwise, set the direction to be normal to the vertexVector
		local normVector = TripleProduct(vertexVector, originVector).Unit
		--Cast it into a Vector2 and set that as our direction and continue
		return false, Vector2.new(normVector.X, normVector.Z)
	else
		--Triangle case
		---We need to identify if the origin is contained within the simplex by setting two of the three vertices as constant and checking the regions adjacent to those edges
		--So we pin simplex[1] and [2] and define 3 vectors
		local simplexEdge1 = (simplex[1] - simplex[3]).Unit
		local simplexEdge2 = (simplex[2] - simplex[3]).Unit
		local originVector = -simplex[3].Unit
		--for k,v in simplex do print(v) end
		--If the origin lies along one of our two edges then return true
		if ApproximatelyEqual(math.abs(originVector:Dot(simplexEdge1)), 1) then return true, nil end
		if ApproximatelyEqual(math.abs(originVector:Dot(simplexEdge2)), 1) then return true, nil end
		--Now we check if the origin is within the two adjacent boundaries to our two edges
		local edge1Normal = -TripleProduct(simplexEdge1, simplexEdge2).Unit --The way we've done our triple product is to define our cross product as inwards facing so we just invert the vector
		local edge2Normal = -TripleProduct(simplexEdge2, simplexEdge1).Unit 
		--Cast the two into Vector2
		edge1Normal = Vector2.new(edge1Normal.X, edge1Normal.Z)
		edge2Normal = Vector2.new(edge2Normal.X, edge2Normal.Z)
		--(by comparing the dot products of these two to our origin vector. Since a dot > 0 implies that the vectors are vaguely in the same direction as each other)
		if edge1Normal:Dot(originVector) > 0 then
			table.remove(simplex, 2)
			return false, edge1Normal
		end
		if edge2Normal:Dot(originVector) > 0 then
			table.remove(simplex, 1)
			return false, edge2Normal
		end
		--If neither of these two conditions are true then our simplex contains the origin so we can return true
		return true, nil
	end
end

--Module methods
function m.Create2DShape(Vertices:{Vector2}, Position:Vector2):Shape
	local NewShape:Shape = {
		vertices = Vertices,
		position = Position,
		dim = ShapeDimensionEnums.Dim2,
		isCircle = false,
		radius = 0,
	}
	return NewShape
end

function m.Create3DShape(Vertices:{Vector3}, Position:Vector3):Shape
	local NewShape:Shape = {
		vertices = Vertices,
		position = Position,
		dim = ShapeDimensionEnums.Dim3,
		isCircle = false,
		radius = 0,
	}
	return NewShape
end

function m.Create2DCircle(Position:Vector3, Radius:number):Shape
	local NewShape:Shape = {
		vertices = {},
		position = Position,
		dim = ShapeDimensionEnums.Dim2,
		isCircle = true,
		radius = Radius,
	}
	return NewShape
end

function m.Create3DSphere(Position:Vector3, Radius:number):Shape
	local NewShape:Shape = {
		vertices = {},
		position = Position,
		dim = ShapeDimensionEnums.Dim3,
		isCircle = true,
		radius = Radius,
	}
	return NewShape
end

function m.Collides(Shape1:Shape, Shape2:Shape):boolean
	--Guards
	if Shape1.dim ~= Shape2.dim then error(`Shape1 must be in the same dimension as Shape2`) return false end
	if Shape1.position == Shape2.position then return true end
	---Currently I don't want to write a handler for 3D shapes but it shouldn't be too bad; we just need to use tetrahedrons as our simplex
	if Shape1.dim == ShapeDimensionEnums.Dim2 then
		--Start with selecting a direction, by convention its just the direction vector between Shape2 and Shape1
		local dir = (Shape2.position - Shape1.position).Unit
		--Since all the vertices are direction vectors, add the position onto it to get the position of each vertex
		local simplex = {(SupportFunction2D(dir, Shape1) + Shape1.position) - (SupportFunction2D(-dir,Shape2) + Shape2.position)}
		--Set the new direction to the direction vector between the origin and the 1st minkowsky vertex
		---One more ternary statement just in case the two shapes share a vertex so the simplex is 0,0,0 and normalising it leads to a NaN vector
		dir = if simplex[1].Magnitude == 0 then -simplex[1] else -simplex[1].Unit --(Since we're doing [0,0,0] - [x,y,z]) 
		local db = 10
		local c = 0
		while true do
			if c >= db then print("Debug break") break end
			c+=1
			--If the direction is [0,0,0] then the two shpaes share one vertex which is really a bit of a strange situation to be in
			--Fetch the minkowsky sum using the direction of the first simplex vertex
			local minComp1, minComp2 = SupportFunction2D(dir, Shape1), SupportFunction2D(-dir, Shape2)
			local minkowskySum = (minComp1 + Shape1.position) - (minComp2 + Shape2.position)
			--if Shape1.isCircle or Shape2.isCircle then
				--print(`minkowsky: {minkowskySum}, components : {minComp1} & {minComp2}`)
			--end
			--If the minkowskySum doesn't pass the origin then return false 
			if (-minkowskySum).Unit:Dot(dir) > 0  then return false end
			--Add our vertex to our simplex
			table.insert(simplex, minkowskySum)
			--If the origin is contained by our simplex then return true since we've found a point that is shared by both shapes
			local simplexResult, newDir = handleSimplex(simplex)
			if simplexResult then 
				return true end
			--Otherwise set the new direction to the 
			dir = newDir.Unit
		end
		return false
	elseif Shape1.dim == ShapeDimensionEnums.Dim3 then
		local dir = ((Shape2.position::Vector3) - (Shape1.position::Vector3)).Unit
		local simplex:{Vector3} = {}
		local minkowskyDiff = SupportFunction3D(dir, Shape1)::Vector3 - SupportFunction3D(-dir, Shape2)::Vector3
		if minkowskyDiff == Vector3.zero then return true end
		table.insert(simplex, minkowskyDiff)
		dir = (-minkowskyDiff).Unit
		
		local debugLimit = 30
		local count = 0
		while true do
			if count >= debugLimit then debugMode = false print("Debug break") break end
			count += 1
			local minkowskyDiff = SupportFunction3D(dir, Shape1)::Vector3 - SupportFunction3D(-dir, Shape2)::Vector3
			if (-minkowskyDiff).Unit:Dot(dir) > 0 then return false end
			table.insert(simplex, minkowskyDiff)
			local containsOrigin, newDir = handleSimplex3D(simplex)
			if containsOrigin then return true end
			dir = newDir.Unit
		end
	else 
		error(`Unrecognised dim enum of {Shape1.dim}`)
		return false
	end
end

function m._debugMode(mode) debugMode = mode end

return m
