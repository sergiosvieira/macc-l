#/***************************************************************************
# *   Copyright (C) 2011 by Sergio Vieira                                   *
# *   sergiosvieira@larces.uece.br                                          *
# *   Mestrado Academico em Ciencia da Computacao (MACC)                    *
# *   Universidade Estadual do Ceara (UECE/Brazil)                               *
# *                                                                         *
# *                                                                         *
# *   This program is free software; you can redistribute it and/or modify  *
# *   it under the terms of the GNU General Public License as published by  *
# *   the Free Software Foundation; either version 2 of the License, or     *
# *   (at your option) any later version.                                   *
# *                                                                         *
# *   This program is distributed in the hope that it will be useful,       *
# *   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
# *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
# *   GNU General Public License for more details.                          *
# *                                                                         *
# *   You should have received a copy of the GNU General Public License     *
# *   along with this program; if not, write to the                         *
# *   Free Software Foundation, Inc.,                                       *
# *   59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.             *
# ***************************************************************************/

#!/usr/bin/env ruby


if (ARGV.length != 5)
	puts "Manhattan Topoloy Generator - Copyright (C) 2011 by sergiosvieira@larces.uece.br\nError: missing parameters."
	puts "Usage: ruby inter.rb <segment width> <segment height> <rows> <columns> <average velocity>"
	exit
end

w = Integer(ARGV[0]) # segment width
h = Integer(ARGV[1]) # segment height
avg = Float(ARGV[4]) # average velocity
is_entry = 0
r = Integer(ARGV[2]) # rows
c = Integer(ARGV[3]) # columns

def range_rand(min,max)
  min + rand(max-min)
end

entry = range_rand(1,(r-1)*(c-1))

#puts entry

for i in (0..(r-1))
	for j in (0..(c-1))
		puts "<INTERSECTION>"
		puts "IID=%d"%((i*4 + j)+1)
		puts "XPOS=%d"%((j+1)*w)
		puts "YPOS=%d"%((i+1)*h)
		puts "</INTERSECTION>"
	end
end

for i in (0..(r-1))
	for j in (0..(c-2))
		if (i*c+j+2 <= r*c)
		puts "<ROAD>"
		puts "FLOW=504"
		puts "SPEED=%f"%(avg)
		puts "ENTRY=0"

			puts "<SEGMENT>"
			puts "START=%d"%((i*c+j+1))
			puts "END=%d"%(i*c+j+2)
			if ((i*(c-1)+j+1) != entry)
				puts "SEGM_ENTRY=0"
			else
				puts "SEGM_ENTRY=1"
			end
			puts "LANE=2"
			puts "</SEGMENT>"
			puts "<SEGMENT>"
			puts "START=%d"%((i*c+j+2))
			puts "END=%d"%(i*c+j+1)
			puts "SEGM_ENTRY=0"
			puts "LANE=2"
			puts "</SEGMENT>"
			
		puts "</ROAD>"
		end
	end
end

for i in (0..(r-2))
	for j in (0..(c-1))
		puts "<ROAD>"
		puts "FLOW=504"
		puts "SPEED=32"
		puts "ENTRY=0"
			
			puts "<SEGMENT>"
			puts "START=%d"%((i*c+j+1))
			puts "END=%d"%((i+1)*c+j+1)
			puts "SEGM_ENTRY=0"
			puts "LANE=2"
			puts "</SEGMENT>"
			puts "<SEGMENT>"
			puts "START=%d"%((i+1)*c+j+1)
			puts "END=%d"%((i*c+j+1))
			puts "SEGM_ENTRY=0"
			puts "LANE=2"
			puts "</SEGMENT>"	
			
		puts "</ROAD>"			
	end
end
